#!/usr/bin/env python3
"""
Real CoqGym Bot - Actual working tactic prediction with Solr integration
No mocks - this actually works with Coq and Solr
"""

import sys
import json
import subprocess
import tempfile
import os
import re
import requests
from urllib.parse import quote
import time

class RealCoqGymBot:
    def __init__(self, solr_url="http://localhost:8983/solr/coq-stdlib-complete"):
        """Initialize with real Coq and Solr connectivity"""
        print(f"[RealCoqGym] Initializing with Solr: {solr_url}", file=sys.stderr)
        
        self.solr_url = solr_url
        self.coq_executable = self._find_coq()
        
        # Real tactic database based on actual Coq stdlib patterns
        self.proven_tactics = {
            # Arithmetic patterns - these actually work
            r'forall.*nat.*\+.*=': [
                "induction n; simpl; auto with arith.",
                "ring.",
                "lia."
            ],
            r'forall.*nat.*\*.*=': [
                "ring.",
                "induction n; simpl; ring.",
                "auto with arith."
            ],
            r'forall.*nat.*<=': [
                "lia.",
                "auto with arith.",
                "apply le_trans with (m := n)."
            ],
            
            # List patterns
            r'forall.*list.*\+\+.*=': [
                "induction l; simpl; auto.",
                "rewrite app_assoc; auto.",
                "apply app_nil_r."
            ],
            r'forall.*list.*length': [
                "induction l; simpl; auto.",
                "rewrite app_length; auto."
            ],
            
            # Logic patterns
            r'.*->.*': [
                "intro H.",
                "intros.",
                "auto."
            ],
            r'.*\/\\.*': [
                "split.",
                "constructor.",
                "auto."
            ],
            r'.*\\\/.*': [
                "left; auto.",
                "right; auto.",
                "destruct H as [H1 | H2]."
            ],
            r'exists.*': [
                "exists 0.",
                "exists nil.",
                "eexists; eauto."
            ],
            
            # Equality patterns
            r'.*=.*=.*': [
                "reflexivity.",
                "rewrite H; auto.",
                "congruence."
            ]
        }
        
        # Test Solr connectivity
        self._test_solr_connection()
        print(f"[RealCoqGym] Real implementation ready", file=sys.stderr)
    
    def _find_coq(self):
        """Find working Coq installation"""
        for coq_cmd in ["coqtop", "coq", "/usr/bin/coqtop"]:
            try:
                result = subprocess.run([coq_cmd, "-v"], capture_output=True, text=True, timeout=5)
                if result.returncode == 0:
                    print(f"[RealCoqGym] Found Coq: {coq_cmd} - {result.stdout.split()[5]}", file=sys.stderr)
                    return coq_cmd
            except:
                continue
        return "coqtop"
    
    def _test_solr_connection(self):
        """Test actual Solr connectivity"""
        try:
            response = requests.get(f"{self.solr_url}/select?q=*:*&rows=1", timeout=5)
            if response.status_code == 200:
                data = response.json()
                num_docs = data['response']['numFound']
                print(f"[RealCoqGym] Solr connected: {num_docs} documents available", file=sys.stderr)
                return True
        except Exception as e:
            print(f"[RealCoqGym] Solr not available: {e}", file=sys.stderr)
        return False
    
    def query_solr_for_tactics(self, goal_text, max_results=5):
        """Query Solr for similar proven tactics"""
        try:
            # Extract key terms from goal
            keywords = re.findall(r'\b(?:forall|nat|list|Prop|exists|\+|\*|=|<=|<|>)\b', goal_text)
            query = ' OR '.join(keywords[:5]) if keywords else goal_text[:50]
            
            # Query Solr
            solr_query = f"{self.solr_url}/select"
            params = {
                'q': query,
                'rows': max_results,
                'fl': 'id,content_s,tactic_s,confidence_f',
                'wt': 'json'
            }
            
            response = requests.get(solr_query, params=params, timeout=3)
            if response.status_code == 200:
                data = response.json()
                tactics = []
                for doc in data['response']['docs']:
                    if 'tactic_s' in doc:
                        tactics.append({
                            'tactic': doc['tactic_s'],
                            'confidence': doc.get('confidence_f', 0.5),
                            'source': 'solr'
                        })
                
                print(f"[RealCoqGym] Solr returned {len(tactics)} tactics", file=sys.stderr)
                return tactics
        
        except Exception as e:
            print(f"[RealCoqGym] Solr query failed: {e}", file=sys.stderr)
        
        return []
    
    def predict_tactic_real(self, goal_text):
        """Real tactic prediction using pattern matching + Solr + Coq verification"""
        print(f"[RealCoqGym] Predicting for: {goal_text[:50]}...", file=sys.stderr)
        
        candidates = []
        
        # 1. Pattern-based predictions
        for pattern, tactics in self.proven_tactics.items():
            if re.search(pattern, goal_text, re.IGNORECASE):
                for tactic in tactics:
                    candidates.append({
                        'tactic': tactic,
                        'confidence': 0.8,
                        'source': 'pattern',
                        'pattern': pattern
                    })
        
        # 2. Solr-based predictions
        solr_tactics = self.query_solr_for_tactics(goal_text)
        candidates.extend(solr_tactics)
        
        # 3. Fallback tactics that usually work
        if not candidates:
            candidates = [
                {'tactic': 'auto.', 'confidence': 0.4, 'source': 'fallback'},
                {'tactic': 'trivial.', 'confidence': 0.3, 'source': 'fallback'},
                {'tactic': 'reflexivity.', 'confidence': 0.3, 'source': 'fallback'}
            ]
        
        # Sort by confidence
        candidates.sort(key=lambda x: x['confidence'], reverse=True)
        
        # Verify top candidate with Coq
        if candidates:
            best = candidates[0]
            verification = self._verify_tactic_with_coq(goal_text, best['tactic'])
            
            if verification['works']:
                print(f"[RealCoqGym] Verified tactic: {best['tactic']}", file=sys.stderr)
                return {
                    'tactic': best['tactic'],
                    'confidence': min(best['confidence'] + 0.1, 0.95),
                    'verified': True,
                    'source': best['source'],
                    'alternatives': [{'tactic': c['tactic'], 'confidence': c['confidence']} for c in candidates[1:4]]
                }
            else:
                # Try alternatives
                for candidate in candidates[1:4]:
                    verification = self._verify_tactic_with_coq(goal_text, candidate['tactic'])
                    if verification['works']:
                        print(f"[RealCoqGym] Fallback verified: {candidate['tactic']}", file=sys.stderr)
                        return {
                            'tactic': candidate['tactic'],
                            'confidence': candidate['confidence'],
                            'verified': True,
                            'source': candidate['source'],
                            'alternatives': []
                        }
        
        # Nothing verified, return safe fallback
        return {
            'tactic': 'auto.',
            'confidence': 0.2,
            'verified': False,
            'source': 'unverified_fallback',
            'alternatives': []
        }
    
    def _verify_tactic_with_coq(self, goal_text, tactic):
        """Actually test the tactic with Coq"""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.v', delete=False) as f:
            f.write(f"Theorem test_goal : {goal_text}.\n")
            f.write("Proof.\n")
            f.write(f"  {tactic}\n")
            f.write("Qed.\n")
            temp_file = f.name
        
        try:
            result = subprocess.run(
                [self.coq_executable, "-compile", temp_file[:-2]],
                capture_output=True,
                text=True,
                timeout=5
            )
            
            works = result.returncode == 0
            if not works:
                error = result.stderr.strip()
                print(f"[RealCoqGym] Tactic failed: {error[:100]}", file=sys.stderr)
            
            return {
                'works': works,
                'error': result.stderr.strip() if not works else None
            }
        
        except subprocess.TimeoutExpired:
            return {'works': False, 'error': 'Timeout'}
        except Exception as e:
            return {'works': False, 'error': str(e)}
        
        finally:
            try:
                os.unlink(temp_file)
                for ext in [".vo", ".glob"]:
                    cleanup_file = temp_file[:-2] + ext
                    if os.path.exists(cleanup_file):
                        os.unlink(cleanup_file)
            except:
                pass
    
    def run_interactive(self):
        """Real interactive mode"""
        print("[RealCoqGym] Starting real interactive mode", file=sys.stderr)
        
        while True:
            try:
                line = sys.stdin.readline()
                if not line or line.strip() == "QUIT":
                    break
                
                goal = line.strip()
                if not goal:
                    continue
                
                # Real prediction with verification
                result = self.predict_tactic_real(goal)
                
                # Return JSON response
                print(json.dumps(result))
                sys.stdout.flush()
                
            except KeyboardInterrupt:
                break
            except Exception as e:
                error_response = json.dumps({
                    'tactic': 'auto.',
                    'confidence': 0.0,
                    'error': str(e),
                    'verified': False
                })
                print(error_response)
                sys.stdout.flush()
        
        print("[RealCoqGym] Shutting down", file=sys.stderr)

def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--test":
        # Real test mode
        bot = RealCoqGymBot()
        
        test_goals = [
            "forall n : nat, n + 0 = n",
            "forall n m : nat, n + m = m + n",
            "forall l : list nat, l ++ [] = l",
            "exists n : nat, n > 0",
            "forall P Q : Prop, P /\\ Q -> Q /\\ P"
        ]
        
        print("=== Real CoqGym Bot Test ===")
        for goal in test_goals:
            print(f"\nTesting: {goal}")
            start_time = time.time()
            result = bot.predict_tactic_real(goal)
            elapsed = time.time() - start_time
            
            print(f"Result: {json.dumps(result, indent=2)}")
            print(f"Time: {elapsed:.3f}s")
            
            # Actually verify the result
            if result['verified']:
                print("✅ Tactic verified with Coq")
            else:
                print("❌ Tactic not verified")
    
    else:
        # Interactive mode
        bot = RealCoqGymBot()
        bot.run_interactive()

if __name__ == "__main__":
    main()