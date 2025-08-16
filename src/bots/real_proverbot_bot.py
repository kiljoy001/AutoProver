#!/usr/bin/env python3
"""
Real ProverBot - Actual complete proof generation that works
Uses real Coq compilation and Solr for proof discovery
"""

import sys
import json
import subprocess
import tempfile
import os
import re
import requests
import time
sys.path.append(os.path.join(os.path.dirname(__file__), '..', 'utils'))
from solr_proof_indexer import SolrProofIndexer

class RealProverBot:
    def __init__(self, solr_url="http://localhost:8983/solr/coq-stdlib-complete", timeout=30):
        """Initialize with real Coq and proof strategies"""
        print(f"[RealProverBot] Initializing real proof engine", file=sys.stderr)
        
        self.solr_url = solr_url
        self.timeout = timeout
        self.coq_executable = self._find_coq()
        
        # Initialize proof indexer for uploading completed proofs
        self.proof_indexer = SolrProofIndexer()
        print("[RealProverBot] Proof indexer initialized - will upload successful proofs", file=sys.stderr)
        
        # Real proof strategies that actually work
        self.proof_strategies = [
            {
                'name': 'basic_automation',
                'tactics': ['auto.', 'trivial.', 'reflexivity.', 'tauto.'],
                'weight': 0.8
            },
            {
                'name': 'arithmetic',
                'tactics': ['lia.', 'ring.', 'omega.', 'auto with arith.'],
                'weight': 0.9,
                'patterns': [r'\+', r'\*', r'<=', r'<', r'>', r'nat']
            },
            {
                'name': 'induction',
                'tactics': ['induction n.', 'induction l.', 'induction m.'],
                'weight': 0.85,
                'patterns': [r'forall.*nat', r'forall.*list']
            },
            {
                'name': 'logic_decomposition',
                'tactics': ['split.', 'left.', 'right.', 'intro.', 'intros.'],
                'weight': 0.7,
                'patterns': [r'/\\\\', r'\\\\/', r'->', r'exists']
            },
            {
                'name': 'rewriting',
                'tactics': ['rewrite H.', 'subst.', 'simpl.'],
                'weight': 0.6,
                'patterns': [r'=']
            }
        ]
        
        print(f"[RealProverBot] Loaded {len(self.proof_strategies)} real strategies", file=sys.stderr)
    
    def _find_coq(self):
        """Find working Coq installation"""
        for coq_cmd in ["coqtop", "coq", "/usr/bin/coqtop"]:
            try:
                result = subprocess.run([coq_cmd, "-v"], capture_output=True, text=True, timeout=5)
                if result.returncode == 0:
                    print(f"[RealProverBot] Found Coq: {coq_cmd}", file=sys.stderr)
                    return coq_cmd
            except:
                continue
        return "coqtop"
    
    def query_solr_for_proofs(self, goal_text):
        """Query Solr for similar complete proofs"""
        try:
            # Extract meaningful terms
            terms = re.findall(r'\b(?:forall|nat|list|Prop|exists|True|False)\b', goal_text)
            query = ' AND '.join(terms[:3]) if terms else goal_text[:30]
            
            params = {
                'q': query,
                'rows': 5,
                'fl': 'id,proof_script_s,theorem_s,tactics_ss',
                'wt': 'json'
            }
            
            response = requests.get(f"{self.solr_url}/select", params=params, timeout=3)
            if response.status_code == 200:
                data = response.json()
                proofs = []
                for doc in data['response']['docs']:
                    if 'proof_script_s' in doc:
                        proofs.append(doc['proof_script_s'])
                
                print(f"[RealProverBot] Solr found {len(proofs)} similar proofs", file=sys.stderr)
                return proofs
        
        except Exception as e:
            print(f"[RealProverBot] Solr query failed: {e}", file=sys.stderr)
        
        return []
    
    def generate_complete_proof(self, goal_text, context=""):
        """Generate actual complete proof that compiles with Coq"""
        print(f"[RealProverBot] Generating proof for: {goal_text[:50]}...", file=sys.stderr)
        
        # 1. Try Solr-based proofs first
        solr_proofs = self.query_solr_for_proofs(goal_text)
        for proof_script in solr_proofs:
            if self._test_proof_compiles(goal_text, proof_script, context):
                # Upload successful proof to Solr
                self.proof_indexer.index_completed_proof(
                    theorem_statement=goal_text,
                    proof_script=proof_script,
                    bot_name="RealProverBot",
                    confidence=0.9,
                    context=context
                )
                
                return {
                    'proof_complete': True,
                    'proof_script': proof_script,
                    'confidence': 0.9,
                    'method': 'solr_retrieval',
                    'verification_status': 'proven'
                }
        
        # 2. Try strategy-based proof generation
        for strategy in self._select_strategies(goal_text):
            proof_script = self._generate_proof_with_strategy(goal_text, strategy)
            
            if self._test_proof_compiles(goal_text, proof_script, context):
                # Upload successful proof to Solr
                self.proof_indexer.index_completed_proof(
                    theorem_statement=goal_text,
                    proof_script=proof_script,
                    bot_name="RealProverBot",
                    confidence=strategy['weight'],
                    context=context
                )
                
                return {
                    'proof_complete': True,
                    'proof_script': proof_script,
                    'confidence': strategy['weight'],
                    'method': f"strategy_{strategy['name']}",
                    'verification_status': 'proven'
                }
        
        # 3. Try systematic tactic combinations
        for tactic_combo in self._generate_tactic_combinations(goal_text):
            if self._test_proof_compiles(goal_text, tactic_combo, context):
                # Upload successful proof to Solr
                self.proof_indexer.index_completed_proof(
                    theorem_statement=goal_text,
                    proof_script=tactic_combo,
                    bot_name="RealProverBot",
                    confidence=0.6,
                    context=context
                )
                
                return {
                    'proof_complete': True,
                    'proof_script': tactic_combo,
                    'confidence': 0.6,
                    'method': 'systematic_search',
                    'verification_status': 'proven'
                }
        
        # 4. Fallback: try very basic tactics
        basic_attempts = [
            "auto.",
            "trivial.",
            "reflexivity.",
            "tauto.",
            "intro; auto.",
            "intros; auto.",
            "split; auto."
        ]
        
        for tactic in basic_attempts:
            if self._test_proof_compiles(goal_text, tactic, context):
                # Upload successful proof to Solr
                self.proof_indexer.index_completed_proof(
                    theorem_statement=goal_text,
                    proof_script=tactic,
                    bot_name="RealProverBot",
                    confidence=0.4,
                    context=context
                )
                
                return {
                    'proof_complete': True,
                    'proof_script': tactic,
                    'confidence': 0.4,
                    'method': 'basic_fallback',
                    'verification_status': 'proven'
                }
        
        # 5. Complete failure
        return {
            'proof_complete': False,
            'proof_script': 'auto. (* Failed to find proof *)',
            'confidence': 0.0,
            'method': 'failed',
            'verification_status': 'failed',
            'error': 'No working proof found'
        }
    
    def _select_strategies(self, goal_text):
        """Select appropriate strategies based on goal analysis"""
        applicable = []
        
        for strategy in self.proof_strategies:
            if 'patterns' in strategy:
                matches = sum(1 for p in strategy['patterns'] 
                             if re.search(p, goal_text, re.IGNORECASE))
                if matches > 0:
                    strategy['relevance'] = matches / len(strategy['patterns'])
                    applicable.append(strategy)
            else:
                # Always applicable
                strategy['relevance'] = 0.5
                applicable.append(strategy)
        
        # Sort by relevance and weight
        applicable.sort(key=lambda s: s['relevance'] * s['weight'], reverse=True)
        return applicable
    
    def _generate_proof_with_strategy(self, goal_text, strategy):
        """Generate proof script using specific strategy"""
        if strategy['name'] == 'induction':
            # Smart induction based on goal
            if re.search(r'forall.*n.*nat', goal_text):
                return "induction n; simpl; auto with arith."
            elif re.search(r'forall.*l.*list', goal_text):
                return "induction l; simpl; auto."
            else:
                return "induction n; auto."
        
        elif strategy['name'] == 'arithmetic':
            if re.search(r'\+', goal_text):
                return "ring."
            elif re.search(r'<=|<|>', goal_text):
                return "lia."
            else:
                return "auto with arith."
        
        elif strategy['name'] == 'logic_decomposition':
            if re.search(r'/\\\\', goal_text):
                return "split; auto."
            elif re.search(r'\\\\/', goal_text):
                return "left; auto."
            elif re.search(r'exists', goal_text):
                if 'nat' in goal_text:
                    return "exists 0; auto."
                elif 'list' in goal_text:
                    return "exists nil; auto."
                else:
                    return "eexists; eauto."
            else:
                return "intro; auto."
        
        else:
            # Use first tactic from strategy
            return strategy['tactics'][0]
    
    def _generate_tactic_combinations(self, goal_text):
        """Generate systematic combinations of tactics"""
        combinations = [
            "intro; auto.",
            "intros; auto.",
            "split; auto.",
            "left; auto.",
            "right; auto.",
            "exists 0; auto.",
            "exists nil; auto.",
            "induction n; auto.",
            "induction l; auto.",
            "rewrite H; auto.",
            "simpl; auto.",
            "reflexivity.",
            "ring.",
            "lia.",
            "tauto."
        ]
        return combinations
    
    def _test_proof_compiles(self, goal_text, proof_script, context=""):
        """Test if proof actually compiles with Coq"""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.v', delete=False) as f:
            if context:
                f.write(f"{context}\n\n")
            
            f.write(f"Theorem test_theorem : {goal_text}.\n")
            f.write("Proof.\n")
            f.write(f"  {proof_script}\n")
            f.write("Qed.\n")
            temp_file = f.name
        
        try:
            result = subprocess.run(
                [self.coq_executable, "-compile", temp_file[:-2]],
                capture_output=True,
                text=True,
                timeout=self.timeout
            )
            
            success = result.returncode == 0
            if success:
                print(f"[RealProverBot] ✅ Proof verified: {proof_script}", file=sys.stderr)
            else:
                print(f"[RealProverBot] ❌ Proof failed: {result.stderr[:100]}", file=sys.stderr)
            
            return success
        
        except subprocess.TimeoutExpired:
            print(f"[RealProverBot] ⏰ Proof timeout", file=sys.stderr)
            return False
        except Exception as e:
            print(f"[RealProverBot] 💥 Proof error: {e}", file=sys.stderr)
            return False
        
        finally:
            try:
                os.unlink(temp_file)
                for ext in [".vo", ".glob", ".vio", ".vos"]:
                    cleanup_file = temp_file[:-2] + ext
                    if os.path.exists(cleanup_file):
                        os.unlink(cleanup_file)
            except:
                pass
    
    def run_interactive(self):
        """Real interactive mode"""
        print("[RealProverBot] Starting real interactive mode", file=sys.stderr)
        
        while True:
            try:
                line = sys.stdin.readline()
                if not line or line.strip() == "QUIT":
                    break
                
                goal = line.strip()
                if not goal:
                    continue
                
                # Generate real proof
                result = self.generate_complete_proof(goal)
                
                print(json.dumps(result))
                sys.stdout.flush()
                
            except KeyboardInterrupt:
                break
            except Exception as e:
                error_response = json.dumps({
                    'proof_complete': False,
                    'proof_script': 'auto.',
                    'confidence': 0.0,
                    'error': str(e),
                    'verification_status': 'error'
                })
                print(error_response)
                sys.stdout.flush()
        
        print("[RealProverBot] Shutting down", file=sys.stderr)

def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--test":
        # Real test mode
        bot = RealProverBot()
        
        test_goals = [
            "forall n : nat, n + 0 = n",
            "forall n m : nat, n + m = m + n",
            "forall l : list nat, l ++ [] = l",
            "exists n : nat, n > 0",
            "forall P Q : Prop, P /\\ Q -> Q /\\ P",
            "True"
        ]
        
        print("=== Real ProverBot Test ===")
        successes = 0
        
        for goal in test_goals:
            print(f"\n🎯 Testing: {goal}")
            start_time = time.time()
            result = bot.generate_complete_proof(goal)
            elapsed = time.time() - start_time
            
            if result['proof_complete']:
                print(f"✅ SUCCESS: {result['proof_script']}")
                print(f"   Method: {result['method']}, Confidence: {result['confidence']:.2f}")
                successes += 1
            else:
                print(f"❌ FAILED: {result.get('error', 'Unknown error')}")
            
            print(f"   Time: {elapsed:.3f}s")
        
        print(f"\n📊 Results: {successes}/{len(test_goals)} proofs completed ({successes/len(test_goals)*100:.1f}%)")
    
    else:
        # Interactive mode
        bot = RealProverBot()
        bot.run_interactive()

if __name__ == "__main__":
    main()