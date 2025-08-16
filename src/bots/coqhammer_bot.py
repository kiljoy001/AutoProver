#!/usr/bin/env python3
"""
CoqHammer Bot - Automated theorem proving with SMT integration
Uses external provers and reconstruction for powerful automation
"""

import sys
import json
import subprocess
import tempfile
import os
import re
import time

class CoqHammerBot:
    def __init__(self, timeout=60):
        """Initialize CoqHammer with SMT integration"""
        print(f"[CoqHammer] Initializing with {timeout}s timeout...", file=sys.stderr)
        
        self.timeout = timeout
        self.coq_executable = self._find_coq()
        
        # CoqHammer tactics and external provers
        self.hammer_tactics = {
            # Main hammer tactics
            "hammer": ["hammer.", "sauto.", "scrush.", "sfirstorder."],
            
            # Reconstruction tactics
            "reconstr": ["yelles.", "z3.", "eprover.", "vampire."],
            
            # SMT-style tactics
            "smt": ["smt.", "cvc4.", "yices2.", "z3_tac."],
            
            # Automation with external reasoning
            "auto_external": ["hauto.", "hfirstorder.", "hcrush."],
            
            # Arithmetic with SMT
            "smt_arith": ["liauto.", "niauto.", "psatz."],
            
            # Logic automation
            "logic_hammer": ["qauto.", "intuition.", "classical_logic."]
        }
        
        # External prover availability (would be detected in real implementation)
        self.available_provers = {
            "z3": True,        # Usually available
            "eprover": False,  # May need installation  
            "vampire": False,  # May need installation
            "cvc4": False,     # May need installation
            "yices2": False    # May need installation
        }
        
        print("[CoqHammer] SMT integration initialized", file=sys.stderr)
    
    def _find_coq(self):
        """Find Coq executable with CoqHammer support"""
        for coq_cmd in ["coqtop", "coq", "/usr/bin/coqtop"]:
            try:
                # Check if CoqHammer is available
                result = subprocess.run(
                    [coq_cmd, "-I", "+coqhammer", "-q"],
                    input="Require Import Hammer.Hammer.\n",
                    text=True,
                    capture_output=True,
                    timeout=10
                )
                if result.returncode == 0:
                    print(f"[CoqHammer] Found Coq with CoqHammer: {coq_cmd}", file=sys.stderr)
                    return coq_cmd
            except (subprocess.CalledProcessError, FileNotFoundError, subprocess.TimeoutExpired):
                continue
        
        print("[CoqHammer] CoqHammer not found, using basic Coq", file=sys.stderr)
        return "coqtop"  # fallback
    
    def prove_with_hammer(self, goal_text, context=""):
        """Prove using CoqHammer with SMT backend"""
        print(f"[CoqHammer] Attempting hammer proof for: {goal_text[:50]}...", file=sys.stderr)
        
        # Create temporary Coq file with CoqHammer setup
        with tempfile.NamedTemporaryFile(mode='w', suffix='.v', delete=False) as f:
            # Include CoqHammer
            f.write("Require Import Hammer.Hammer.\n")
            f.write("Require Import Hammer.Plugin.Hammer.\n\n")
            
            # Write context
            if context:
                f.write(f"{context}\n\n")
            
            # Write theorem to prove
            f.write(f"Theorem hammer_goal : {goal_text}.\n")
            f.write("Proof.\n")
            
            # Try CoqHammer tactics in order of preference
            hammer_attempts = self._select_hammer_tactics(goal_text)
            
            for i, (tactic, description) in enumerate(hammer_attempts):
                f.write(f"  (* Attempt {i+1}: {description} *)\n")
                f.write(f"  try ({tactic}).\n")
            
            # Fallback to basic tactics
            f.write("  (* Fallback automation *)\n")
            f.write("  auto || eauto || firstorder.\n")
            f.write("Qed.\n")
            
            temp_file = f.name
        
        try:
            # Run CoqHammer proof
            print("[CoqHammer] Running external provers...", file=sys.stderr)
            start_time = time.time()
            
            result = subprocess.run(
                [self.coq_executable, "-I", "+coqhammer", "-compile", temp_file[:-2]],
                capture_output=True,
                text=True,
                timeout=self.timeout
            )
            
            elapsed = time.time() - start_time
            
            if result.returncode == 0:
                print(f"[CoqHammer] Proof successful in {elapsed:.2f}s!", file=sys.stderr)
                
                # Extract which tactic worked (simplified)
                successful_tactic = self._extract_successful_tactic(result.stdout, hammer_attempts)
                
                return {
                    "proof_found": True,
                    "tactic": successful_tactic,
                    "confidence": 0.95,
                    "proof_time": elapsed,
                    "external_provers_used": True,
                    "reconstruction": "automatic",
                    "method": "hammer"
                }
            else:
                # CoqHammer failed, try simpler automation
                print(f"[CoqHammer] Hammer failed, trying basic automation", file=sys.stderr)
                
                simple_result = self._try_simple_automation(goal_text, context)
                return simple_result
        
        except subprocess.TimeoutExpired:
            print(f"[CoqHammer] Timeout after {self.timeout}s", file=sys.stderr)
            return {
                "proof_found": False,
                "tactic": "auto.",
                "confidence": 0.1,
                "error": f"Timeout after {self.timeout}s",
                "method": "timeout"
            }
        
        finally:
            # Clean up
            try:
                os.unlink(temp_file)
                for ext in [".vo", ".glob", ".vio", ".vos"]:
                    cleanup_file = temp_file[:-2] + ext
                    if os.path.exists(cleanup_file):
                        os.unlink(cleanup_file)
            except OSError:
                pass
    
    def _select_hammer_tactics(self, goal_text):
        """Select appropriate CoqHammer tactics based on goal"""
        tactics = []
        goal_lower = goal_text.lower()
        
        # Goal-specific tactic selection
        if re.search(r'forall.*nat.*=', goal_text, re.IGNORECASE):
            tactics.append(("liauto.", "Linear arithmetic automation"))
            tactics.append(("hammer.", "Full hammer with arithmetic"))
        
        elif re.search(r'forall.*list', goal_text, re.IGNORECASE):
            tactics.append(("sauto.", "Safe automation for lists"))
            tactics.append(("hammer.", "Full hammer"))
        
        elif re.search(r'exists', goal_text, re.IGNORECASE):
            tactics.append(("scrush.", "Crushing automation"))
            tactics.append(("sfirstorder.", "First-order automation"))
        
        elif re.search(r'/\\\\|\\\\\\/|~', goal_text):
            tactics.append(("sfirstorder.", "First-order logic"))
            tactics.append(("qauto.", "Quantifier automation"))
        
        elif re.search(r'\\+|\\*|≤|≥', goal_text):
            tactics.append(("liauto.", "Linear arithmetic"))
            tactics.append(("niauto.", "Non-linear arithmetic"))
            tactics.append(("psatz.", "Polynomial automation"))
        
        # Always try the main hammer
        if not any("hammer." in t[0] for t in tactics):
            tactics.append(("hammer.", "Full automated reasoning"))
        
        # Add safe fallbacks
        tactics.extend([
            ("sauto.", "Safe automation"),
            ("hauto.", "Heuristic automation"), 
            ("scrush.", "Crushing tactics")
        ])
        
        return tactics[:4]  # Return top 4 attempts
    
    def _try_simple_automation(self, goal_text, context):
        """Fallback to simple automation when hammer fails"""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.v', delete=False) as f:
            if context:
                f.write(f"{context}\n\n")
            
            f.write(f"Theorem simple_goal : {goal_text}.\n")
            f.write("Proof.\n")
            f.write("  auto || eauto || firstorder || tauto.\n")
            f.write("Qed.\n")
            
            temp_file = f.name
        
        try:
            result = subprocess.run(
                [self.coq_executable, "-compile", temp_file[:-2]],
                capture_output=True,
                text=True,
                timeout=10
            )
            
            if result.returncode == 0:
                return {
                    "proof_found": True,
                    "tactic": "auto.",
                    "confidence": 0.6,
                    "external_provers_used": False,
                    "method": "simple_automation"
                }
            else:
                return {
                    "proof_found": False,
                    "tactic": "admit.",
                    "confidence": 0.0,
                    "error": "All tactics failed",
                    "method": "failed"
                }
        
        except subprocess.TimeoutExpired:
            return {
                "proof_found": False,
                "tactic": "auto.",
                "confidence": 0.1,
                "error": "Simple automation timeout",
                "method": "timeout"
            }
        
        finally:
            try:
                os.unlink(temp_file)
                for ext in [".vo", ".glob"]:
                    cleanup_file = temp_file[:-2] + ext
                    if os.path.exists(cleanup_file):
                        os.unlink(cleanup_file)
            except OSError:
                pass
    
    def _extract_successful_tactic(self, coq_output, attempted_tactics):
        """Extract which tactic succeeded from Coq output"""
        # This would parse Coq output to determine which tactic worked
        # For now, return the first hammer tactic
        if attempted_tactics:
            return attempted_tactics[0][0]
        return "hammer."
    
    def run_interactive(self):
        """Run in interactive mode for bot network"""
        print("[CoqHammer] Starting interactive mode", file=sys.stderr)
        
        while True:
            try:
                line = sys.stdin.readline()
                if not line or line.strip() == "QUIT":
                    break
                
                goal = line.strip()
                if not goal:
                    continue
                
                # Attempt proof with CoqHammer
                result = self.prove_with_hammer(goal)
                
                # Return JSON response for the bot network
                response = json.dumps(result)
                print(response)
                sys.stdout.flush()
                
            except KeyboardInterrupt:
                break
            except Exception as e:
                error_response = json.dumps({
                    "proof_found": False,
                    "tactic": "auto.",
                    "confidence": 0.0,
                    "error": str(e),
                    "method": "error"
                })
                print(error_response)
                sys.stdout.flush()
        
        print("[CoqHammer] Shutting down", file=sys.stderr)

def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--test":
        # Test mode
        bot = CoqHammerBot()
        
        test_goals = [
            "forall n : nat, n + 0 = n",
            "forall n m : nat, n + m = m + n",
            "forall l : list nat, l ++ [] = l", 
            "exists n : nat, n > 0",
            "forall P Q : Prop, P /\\ Q -> Q /\\ P",
            "forall n : nat, n * 1 = n",
            "forall n : nat, n <= n + 1"
        ]
        
        for goal in test_goals:
            print(f"\nTesting: {goal}")
            result = bot.prove_with_hammer(goal)
            print(f"Hammer: {json.dumps(result, indent=2)}")
    else:
        # Interactive mode
        bot = CoqHammerBot()
        bot.run_interactive()

if __name__ == "__main__":
    main()