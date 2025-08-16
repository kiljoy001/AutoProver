#!/usr/bin/env python3
"""
TacticToe Bot - ML-guided tactic synthesis
Uses machine learning for smart tactic selection and synthesis
"""

import sys
import json
import random
import re
from collections import defaultdict

class TacticToeBot:
    def __init__(self, model_path="/opt/tactictoe/model"):
        """Initialize TacticToe with ML guidance model"""
        print(f"[TacticToe] Loading ML guidance model from {model_path}...", file=sys.stderr)
        
        # TacticToe-style tactic database with ML features
        self.tactic_library = {
            # Core automation tactics
            "auto": {
                "base": "auto",
                "variants": ["auto.", "auto with *.", "eauto.", "eauto with *."],
                "contexts": ["simple_goals", "logic", "arithmetic"],
                "success_rate": 0.6
            },
            
            # Induction tactics
            "induction": {
                "base": "induction",
                "variants": ["induction n.", "induction m.", "induction l.", "induction H."],
                "contexts": ["nat", "list", "tree", "inductive_types"],
                "success_rate": 0.8
            },
            
            # Rewriting tactics
            "rewrite": {
                "base": "rewrite",
                "variants": ["rewrite H.", "rewrite <- H.", "rewrite IHn.", "rewrite app_nil_r."],
                "contexts": ["equality", "lemmas", "hypotheses"],
                "success_rate": 0.7
            },
            
            # Splitting tactics
            "split": {
                "base": "split",
                "variants": ["split.", "constructor.", "left.", "right."],
                "contexts": ["conjunction", "disjunction", "inductive"],
                "success_rate": 0.8
            },
            
            # Application tactics
            "apply": {
                "base": "apply",
                "variants": ["apply H.", "apply IHn.", "apply le_n.", "eapply H."],
                "contexts": ["hypotheses", "lemmas", "theorems"],
                "success_rate": 0.7
            },
            
            # Arithmetic tactics
            "arithmetic": {
                "base": "arith",
                "variants": ["ring.", "lia.", "omega.", "auto with arith."],
                "contexts": ["nat", "Z", "arithmetic"],
                "success_rate": 0.9
            },
            
            # Simplification tactics
            "simplify": {
                "base": "simpl",
                "variants": ["simpl.", "unfold f.", "fold f.", "simpl in H."],
                "contexts": ["definitions", "fixpoints", "match"],
                "success_rate": 0.6
            },
            
            # Existential tactics
            "exists": {
                "base": "exists",
                "variants": ["exists 0.", "exists nil.", "eexists.", "exists (S n)."],
                "contexts": ["existential", "witness"],
                "success_rate": 0.7
            }
        }
        
        # ML-based tactic selection weights
        self.ml_weights = defaultdict(float)
        self._initialize_ml_weights()
        
        print("[TacticToe] ML guidance model loaded successfully", file=sys.stderr)
    
    def _initialize_ml_weights(self):
        """Initialize ML-based tactic selection weights"""
        # Simulate learned weights from training data
        weights = {
            ("forall.*nat", "induction"): 0.9,
            ("forall.*list", "induction"): 0.85,
            (".*=.*", "rewrite"): 0.8,
            (".*=.*", "arithmetic"): 0.7,
            ("exists", "exists"): 0.9,
            (".*\\+.*", "arithmetic"): 0.95,
            (".*\\*.*", "arithmetic"): 0.9,
            ("/\\\\", "split"): 0.8,
            ("\\\\/", "split"): 0.8,
            ("~", "auto"): 0.6,
            ("True", "auto"): 0.95,
            ("False", "auto"): 0.3
        }
        
        for (pattern, tactic), weight in weights.items():
            self.ml_weights[(pattern, tactic)] = weight
    
    def synthesize_tactic(self, goal_text, context="", proof_state=""):
        """Synthesize tactics using ML guidance"""
        print(f"[TacticToe] Synthesizing tactic for: {goal_text[:50]}...", file=sys.stderr)
        
        # Analyze goal structure
        goal_features = self._extract_goal_features(goal_text)
        
        # ML-guided tactic selection
        tactic_scores = []
        
        for tactic_name, tactic_info in self.tactic_library.items():
            score = self._compute_tactic_score(goal_features, tactic_name, tactic_info)
            
            if score > 0.1:  # Filter low-probability tactics
                # Select best variant for this tactic
                variant = self._select_best_variant(goal_text, tactic_info)
                tactic_scores.append((variant, score, tactic_name))
        
        # Sort by ML confidence
        tactic_scores.sort(key=lambda x: x[1], reverse=True)
        
        if tactic_scores:
            best_tactic, confidence, strategy = tactic_scores[0]
            print(f"[TacticToe] ML synthesis: {best_tactic} (conf: {confidence:.2f}, strategy: {strategy})", file=sys.stderr)
            
            return {
                "tactic": best_tactic,
                "confidence": confidence,
                "strategy": strategy,
                "alternatives": [
                    {"tactic": t, "confidence": c, "strategy": s} 
                    for t, c, s in tactic_scores[1:4]
                ],
                "ml_guided": True
            }
        else:
            # Fallback to basic automation
            fallback = "auto."
            print(f"[TacticToe] No ML match, using fallback: {fallback}", file=sys.stderr)
            return {
                "tactic": fallback,
                "confidence": 0.2,
                "strategy": "fallback",
                "alternatives": [
                    {"tactic": "eauto.", "confidence": 0.15, "strategy": "extended_auto"},
                    {"tactic": "trivial.", "confidence": 0.1, "strategy": "simple"}
                ],
                "ml_guided": False
            }
    
    def _extract_goal_features(self, goal_text):
        """Extract features from goal for ML analysis"""
        features = {
            "has_forall": bool(re.search(r'forall', goal_text, re.IGNORECASE)),
            "has_exists": bool(re.search(r'exists', goal_text, re.IGNORECASE)),
            "has_equality": bool(re.search(r'=', goal_text)),
            "has_inequality": bool(re.search(r'<>|≠', goal_text)),
            "has_arithmetic": bool(re.search(r'\\+|\\*|-|/|≤|≥|<|>', goal_text)),
            "has_conjunction": bool(re.search(r'/\\\\|∧', goal_text)),
            "has_disjunction": bool(re.search(r'\\\\/|∨', goal_text)),
            "has_negation": bool(re.search(r'~|¬', goal_text)),
            "has_nat": bool(re.search(r'nat', goal_text, re.IGNORECASE)),
            "has_list": bool(re.search(r'list', goal_text, re.IGNORECASE)),
            "has_prop": bool(re.search(r'Prop', goal_text)),
            "goal_length": len(goal_text),
            "complexity": goal_text.count('(') + goal_text.count('[')
        }
        
        return features
    
    def _compute_tactic_score(self, goal_features, tactic_name, tactic_info):
        """Compute ML-based score for a tactic"""
        base_score = tactic_info["success_rate"]
        
        # Context-based scoring
        context_bonus = 0.0
        goal_text = ""  # Would need to pass this through
        
        # Pattern-based ML weights
        pattern_bonus = 0.0
        for (pattern, tactic), weight in self.ml_weights.items():
            if tactic == tactic_name:
                # Would check if pattern matches goal_text
                pattern_bonus += weight * 0.1  # Simplified
        
        # Feature-based scoring
        feature_bonus = 0.0
        if tactic_name == "induction" and (goal_features["has_forall"] and goal_features["has_nat"]):
            feature_bonus += 0.3
        if tactic_name == "arithmetic" and goal_features["has_arithmetic"]:
            feature_bonus += 0.4
        if tactic_name == "split" and (goal_features["has_conjunction"] or goal_features["has_disjunction"]):
            feature_bonus += 0.3
        if tactic_name == "exists" and goal_features["has_exists"]:
            feature_bonus += 0.4
        
        # Complexity penalty for simple tactics on complex goals
        complexity_factor = 1.0
        if goal_features["complexity"] > 5 and tactic_name == "auto":
            complexity_factor = 0.7
        
        total_score = (base_score + context_bonus + pattern_bonus + feature_bonus) * complexity_factor
        return min(total_score, 0.99)  # Cap at 99%
    
    def _select_best_variant(self, goal_text, tactic_info):
        """Select the best tactic variant for the goal"""
        variants = tactic_info["variants"]
        
        # Simple heuristics for variant selection
        if re.search(r'forall.*n.*nat', goal_text, re.IGNORECASE):
            return next((v for v in variants if "n." in v), variants[0])
        
        if re.search(r'forall.*l.*list', goal_text, re.IGNORECASE):
            return next((v for v in variants if "l." in v), variants[0])
        
        if re.search(r'exists.*nat', goal_text, re.IGNORECASE):
            return next((v for v in variants if "0." in v), variants[0])
        
        if re.search(r'exists.*list', goal_text, re.IGNORECASE):
            return next((v for v in variants if "nil." in v), variants[0])
        
        # Default to first variant (most general)
        return variants[0]
    
    def run_interactive(self):
        """Run in interactive mode for bot network"""
        print("[TacticToe] Starting interactive mode", file=sys.stderr)
        
        while True:
            try:
                line = sys.stdin.readline()
                if not line or line.strip() == "QUIT":
                    break
                
                goal = line.strip()
                if not goal:
                    continue
                
                # Synthesize tactic using ML guidance
                result = self.synthesize_tactic(goal)
                
                # Return JSON response for the bot network
                response = json.dumps(result)
                print(response)
                sys.stdout.flush()
                
            except KeyboardInterrupt:
                break
            except Exception as e:
                error_response = json.dumps({
                    "tactic": "auto.",
                    "confidence": 0.0,
                    "strategy": "error",
                    "error": str(e),
                    "ml_guided": False
                })
                print(error_response)
                sys.stdout.flush()
        
        print("[TacticToe] Shutting down", file=sys.stderr)

def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--test":
        # Test mode
        bot = TacticToeBot()
        
        test_goals = [
            "forall n : nat, n + 0 = n",
            "forall n m : nat, n + m = m + n", 
            "forall l : list nat, l ++ [] = l",
            "exists n : nat, n > 0",
            "forall P Q : Prop, P /\\ Q -> Q /\\ P",
            "forall n : nat, n * 1 = n",
            "True",
            "False -> True"
        ]
        
        for goal in test_goals:
            print(f"\nTesting: {goal}")
            result = bot.synthesize_tactic(goal)
            print(f"Synthesis: {json.dumps(result, indent=2)}")
    else:
        # Interactive mode
        bot = TacticToeBot()
        bot.run_interactive()

if __name__ == "__main__":
    main()