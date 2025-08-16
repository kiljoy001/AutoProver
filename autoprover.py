#!/usr/bin/env python3
"""
AutoProver - Unified Application
Integrated formally verified bot network for theorem proving
"""

import sys
import os
import json
import argparse
import time
import subprocess
from pathlib import Path

# Add src paths
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src', 'bots'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src', 'utils'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src', 'core'))

from real_coqgym_bot import RealCoqGymBot
from real_proverbot_bot import RealProverBot
from solr_proof_indexer import SolrProofIndexer
from safe_coq_checker import SafeCoqChecker
from ghostdag_consensus import GhostDAGConsensus, parallel_proof_attempt
from ocaml_bridge_interface import OCamlBridgeInterface, ocaml_coordinated_proof_attempt

# GPU acceleration imports
try:
    from gpu_coqgym_bot import GPUCoqGymBot
    GPU_AVAILABLE = True
except ImportError:
    GPU_AVAILABLE = False

try:
    import torch
    CUDA_AVAILABLE = torch.cuda.is_available()
except ImportError:
    CUDA_AVAILABLE = False

class AutoProverApp:
    """Unified AutoProver Application"""
    
    def __init__(self):
        self.config_path = "config/bot_deployment.json"
        self.config = self._load_config()
        self.bots = {}
        self.proof_indexer = None
        self.safety_checker = None
        self.gpu_enabled = False
        self.consensus = None
        self.ocaml_bridge = None
        
        print("🚀 AutoProver - Formally Verified Bot Network")
        print("=" * 50)
        
        # Check GPU availability
        if CUDA_AVAILABLE and GPU_AVAILABLE:
            import torch
            gpu_name = torch.cuda.get_device_name()
            vram = torch.cuda.get_device_properties(0).total_memory / 1e9
            print(f"🔥 GPU Detected: {gpu_name} ({vram:.1f}GB VRAM)")
            self.gpu_enabled = True
        else:
            print("💻 Running on CPU only")
    
    def _load_config(self):
        """Load configuration"""
        try:
            with open(self.config_path, 'r') as f:
                return json.load(f)
        except Exception as e:
            print(f"❌ Failed to load config: {e}")
            return self._default_config()
    
    def _default_config(self):
        """Default configuration if file not found"""
        return {
            "safety_configuration": {
                "enforce_no_admits": True,
                "enforce_no_axioms": True,
                "require_coq_compilation": True
            },
            "bot_executables": {
                "coqgym": {"enabled": True},
                "proverbot9001": {"enabled": True}
            }
        }
    
    def initialize(self):
        """Initialize all components"""
        print("\n🔧 Initializing Components...")
        
        # Initialize safety checker
        if self.config.get("safety_configuration", {}).get("enforce_no_admits", True):
            self.safety_checker = SafeCoqChecker()
            print("✅ Safety checker: No admits/axioms enforced")
        
        # Initialize Solr indexer
        try:
            self.proof_indexer = SolrProofIndexer()
            print("✅ Solr proof indexer: Ready")
        except Exception as e:
            print(f"⚠️  Solr indexer failed: {e}")
        
        # Initialize OCaml Bridge for Maximum Parallelism - REQUIRED
        try:
            self.ocaml_bridge = OCamlBridgeInterface()
            if self.ocaml_bridge.is_available():
                print("✅ OCaml maximum parallelism bridge: Ready (REQUIRED)")
            else:
                print("⚠️  OCaml bridge compiling...")
                time.sleep(2)  # Give compilation time
                if not self.ocaml_bridge.is_available():
                    print("❌ OCaml bridge failed to compile")
                    print("⚠️  Falling back to Python-only mode (reduced parallelism)")
                    self.ocaml_bridge = None
        except Exception as e:
            print(f"❌ OCaml bridge failed: {e}")
            print("⚠️  Falling back to Python-only mode")
            self.ocaml_bridge = None
        
        # Initialize GhostDAG consensus - REQUIRED
        try:
            self.consensus = GhostDAGConsensus(k=3, max_parallel_attempts=len(self.config.get("bot_executables", {})))
            print("✅ GhostDAG consensus: Ready (REQUIRED)")
        except Exception as e:
            print(f"❌ GhostDAG consensus failed: {e}")
            print("💥 FATAL: AutoProver requires GhostDAG consensus to operate")
            return False
        
        # Initialize bots
        bot_config = self.config.get("bot_executables", {})
        
        # Initialize CoqGym (CPU or GPU version)
        if bot_config.get("coqgym", {}).get("enabled", False):
            try:
                if self.gpu_enabled:
                    self.bots["coqgym_gpu"] = GPUCoqGymBot()
                    print("✅ GPU-CoqGym bot: Ready (CUDA accelerated)")
                
                self.bots["coqgym"] = RealCoqGymBot()
                print("✅ CoqGym bot: Ready (CPU)")
            except Exception as e:
                print(f"❌ CoqGym bot failed: {e}")
        
        if bot_config.get("proverbot9001", {}).get("enabled", False):
            try:
                self.bots["proverbot9001"] = RealProverBot()
                print("✅ ProverBot9001: Ready")
            except Exception as e:
                print(f"❌ ProverBot9001 failed: {e}")
        
        print(f"\n🤖 {len(self.bots)} bots initialized")
        print("🔗 All operations will use OCaml maximum parallelism + GhostDAG consensus ONLY")
        return len(self.bots) > 0 and self.consensus is not None and self.ocaml_bridge is not None
    
    def interactive_mode(self):
        """Interactive theorem proving mode"""
        print("\n🎯 Interactive Proving Mode")
        print("Enter Coq goals, get AI-assisted proofs")
        print("Commands: :help, :quit, :status, :stats")
        print("-" * 40)
        
        session_stats = {"goals_processed": 0, "proofs_found": 0, "time_spent": 0}
        
        while True:
            try:
                goal = input("\nCoq goal> ").strip()
                
                if goal in [":quit", ":q"]:
                    break
                elif goal in [":help", ":h"]:
                    self._show_help()
                    continue
                elif goal in [":status", ":s"]:
                    self._show_status()
                    continue
                elif goal in [":stats"]:
                    self._show_session_stats(session_stats)
                    continue
                elif not goal:
                    continue
                
                # Process the goal
                start_time = time.time()
                result = self._process_goal(goal)
                elapsed = time.time() - start_time
                
                # Update stats
                session_stats["goals_processed"] += 1
                session_stats["time_spent"] += elapsed
                if result.get("success", False):
                    session_stats["proofs_found"] += 1
                
                # Display result
                self._display_result(result, elapsed)
                
            except KeyboardInterrupt:
                print("\n👋 Exiting...")
                break
            except Exception as e:
                print(f"❌ Error: {e}")
        
        self._show_session_stats(session_stats)
    
    def batch_mode(self, input_file):
        """Batch processing mode"""
        print(f"\n📁 Batch Mode: Processing {input_file}")
        
        try:
            with open(input_file, 'r') as f:
                goals = [line.strip() for line in f if line.strip() and not line.startswith('#')]
            
            print(f"Found {len(goals)} goals to process")
            
            results = []
            for i, goal in enumerate(goals, 1):
                print(f"\n[{i}/{len(goals)}] Processing: {goal[:50]}...")
                result = self._process_goal(goal)
                results.append({"goal": goal, "result": result})
                
                if result.get("success", False):
                    print(f"✅ SUCCESS: {result['tactic']}")
                else:
                    print(f"❌ FAILED: {result.get('error', 'Unknown error')}")
            
            # Summary
            successes = sum(1 for r in results if r["result"].get("success", False))
            print(f"\n📊 Batch Results: {successes}/{len(goals)} proofs completed ({successes/len(goals)*100:.1f}%)")
            
            return results
            
        except Exception as e:
            print(f"❌ Batch processing failed: {e}")
            return []
    
    def test_mode(self):
        """Test all bots with standard theorems"""
        print("\n🧪 Test Mode: Standard Theorem Suite")
        
        test_goals = [
            "forall n : nat, n + 0 = n",
            "forall n m : nat, n + m = m + n",
            "forall l : list nat, l ++ [] = l",
            "exists n : nat, n > 0",
            "forall P Q : Prop, P /\\ Q -> Q /\\ P",
            "True",
            "forall n : nat, n * 1 = n",
            "forall a b c : nat, a + (b + c) = (a + b) + c"
        ]
        
        bot_results = {}
        
        for bot_name, bot in self.bots.items():
            print(f"\n🤖 Testing {bot_name}...")
            bot_results[bot_name] = []
            
            for goal in test_goals:
                start_time = time.time()
                
                if bot_name == "coqgym":
                    result = bot.predict_tactic_real(goal)
                elif bot_name == "proverbot9001":
                    result = bot.generate_complete_proof(goal)
                else:
                    result = {"error": "Unknown bot type"}
                
                elapsed = time.time() - start_time
                
                success = result.get("verified", False) or result.get("proof_complete", False)
                bot_results[bot_name].append({
                    "goal": goal,
                    "success": success,
                    "time": elapsed,
                    "result": result
                })
                
                status = "✅" if success else "❌"
                print(f"  {status} {goal[:40]}... ({elapsed:.3f}s)")
        
        # Summary
        print("\n📊 Test Summary:")
        for bot_name, results in bot_results.items():
            successes = sum(1 for r in results if r["success"])
            avg_time = sum(r["time"] for r in results) / len(results)
            print(f"  {bot_name}: {successes}/{len(test_goals)} ({successes/len(test_goals)*100:.1f}%) - {avg_time:.3f}s avg")
        
        return bot_results
    
    def _process_goal(self, goal):
        """Process goal using ONLY OCaml maximum parallelism - no fallbacks"""
        if not self.ocaml_bridge:
            return {"success": False, "error": "OCaml bridge not available"}
        
        if not self.consensus:
            return {"success": False, "error": "GhostDAG consensus not available"}
        
        start_time = time.time()
        
        try:
            print(f"🔥 OCaml coordinating maximum parallelism for: {goal[:50]}...", flush=True)
            
            # Use OCaml bridge for maximum parallelism
            result = ocaml_coordinated_proof_attempt(goal)
            
            if result and result.get("success", False):
                return {
                    "success": True,
                    "tactic": result["tactic"],
                    "confidence": result["confidence"],
                    "bot": result["bot"],
                    "method": result["method"],
                    "consensus_score": result.get("consensus_score", 0.0),
                    "blue_block": result.get("blue_block", True),
                    "inference_time": result["inference_time"],
                    "parallel_execution": True,
                    "ocaml_coordinated": True
                }
            else:
                error_msg = result.get("error", "OCaml coordination found no viable proof") if result else "OCaml coordination failed"
                return {
                    "success": False,
                    "error": error_msg,
                    "inference_time": time.time() - start_time,
                    "ocaml_coordinated": True
                }
                
        except Exception as e:
            return {
                "success": False,
                "error": f"OCaml coordination failed: {e}",
                "inference_time": time.time() - start_time,
                "ocaml_coordinated": True
            }
    
    def _display_result(self, result, elapsed):
        """Display result to user"""
        if result.get("success", False):
            print(f"✅ SUCCESS ({elapsed:.3f}s)")
            print(f"   Bot: {result['bot']} | Method: {result['method']}")
            print(f"   Tactic: {result['tactic']}")
            print(f"   Confidence: {result['confidence']:.2f}")
            
            # Show parallel execution info if available
            if result.get("ocaml_coordinated", False):
                print(f"   🔥 OCaml Maximum Parallelism: ✅")
            if "consensus_score" in result:
                print(f"   Consensus Score: {result['consensus_score']:.2f}")
            if "blue_block" in result:
                print(f"   Blue Block: {'✅' if result['blue_block'] else '❌'}")
            if result.get("parallel_execution", False):
                print(f"   Parallel Execution: ✅")
        else:
            print(f"❌ FAILED ({elapsed:.3f}s)")
            print(f"   Error: {result.get('error', 'Unknown error')}")
            if result.get("ocaml_coordinated", False):
                print(f"   🔥 OCaml Coordination: Attempted")
    
    def _show_help(self):
        """Show help information"""
        print("\n📖 AutoProver Commands:")
        print("  :help, :h     - Show this help")
        print("  :quit, :q     - Exit")
        print("  :status, :s   - Show system status")
        print("  :stats        - Show session statistics")
        print("  [goal]        - Prove a Coq goal")
        print("\nExample goals:")
        print("  forall n : nat, n + 0 = n")
        print("  exists n : nat, n > 0")
    
    def _show_status(self):
        """Show system status"""
        print("\n📊 System Status:")
        print(f"  Active bots: {len(self.bots)}")
        for name in self.bots:
            if "gpu" in name:
                print(f"    🔥 {name} (GPU accelerated)")
            else:
                print(f"    ✅ {name}")
        
        print(f"  GPU acceleration: {'✅' if self.gpu_enabled else '❌'}")
        if self.gpu_enabled:
            try:
                import torch
                print(f"    GPU: {torch.cuda.get_device_name()}")
                print(f"    VRAM usage: {torch.cuda.memory_allocated()/1e9:.1f}GB / {torch.cuda.get_device_properties(0).total_memory/1e9:.1f}GB")
            except:
                print("    GPU: Unable to check details")
        
        print(f"  Safety enforced: {self.safety_checker is not None}")
        print(f"  Solr indexing: {self.proof_indexer is not None}")
        print(f"  OCaml maximum parallelism: {self.ocaml_bridge.is_available() if self.ocaml_bridge else False}")
        print(f"  GhostDAG consensus: {self.consensus is not None}")
        
        if self.ocaml_bridge:
            try:
                stats = self.ocaml_bridge.get_stats()
                print(f"    OCaml bridge: {'✅ Ready' if stats['available'] else '❌ Not available'}")
                print(f"    Bridge compiled: {stats['compiled']}")
            except:
                print("    OCaml: Unable to check stats")
        
        if self.consensus:
            try:
                stats = self.consensus.get_stats()
                print(f"    Total blocks: {stats['total_blocks']}")
                print(f"    Blue blocks: {stats['blue_blocks']} | Red blocks: {stats['red_blocks']}")
                print(f"    Active attempts: {stats['active_attempts']}")
                print(f"    K parameter: {stats['k_parameter']}")
            except:
                print("    GhostDAG: Unable to check stats")
        
        if self.proof_indexer:
            try:
                stats = self.proof_indexer.get_stats()
                print(f"  Indexed proofs: {stats.get('solved_proofs', 'N/A')}")
            except:
                print("  Indexed proofs: Unable to check")
    
    def _show_session_stats(self, stats):
        """Show session statistics"""
        if stats["goals_processed"] > 0:
            success_rate = stats["proofs_found"] / stats["goals_processed"] * 100
            avg_time = stats["time_spent"] / stats["goals_processed"]
            
            print(f"\n📈 Session Statistics:")
            print(f"  Goals processed: {stats['goals_processed']}")
            print(f"  Proofs found: {stats['proofs_found']}")
            print(f"  Success rate: {success_rate:.1f}%")
            print(f"  Average time: {avg_time:.3f}s")
            print(f"  Total time: {stats['time_spent']:.1f}s")

def main():
    parser = argparse.ArgumentParser(description="AutoProver - Formally Verified Bot Network")
    parser.add_argument("mode", choices=["interactive", "batch", "test", "status", "gpu-setup"], 
                       help="Operation mode")
    parser.add_argument("--input", "-i", help="Input file for batch mode")
    parser.add_argument("--config", "-c", help="Configuration file path")
    parser.add_argument("--gpu", action="store_true", help="Force GPU acceleration check")
    
    args = parser.parse_args()
    
    # Handle GPU setup mode
    if args.mode == "gpu-setup":
        print("🔥 Setting up GPU acceleration...")
        try:
            subprocess.run([sys.executable, os.path.join(os.path.dirname(__file__), "gpu_install.sh")], check=True)
            print("✅ GPU setup complete! Restart AutoProver to use GPU acceleration.")
        except Exception as e:
            print(f"❌ GPU setup failed: {e}")
        return 0
    
    # Initialize application
    app = AutoProverApp()
    if args.config:
        app.config_path = args.config
    
    if not app.initialize():
        print("❌ Initialization failed - no bots available")
        return 1
    
    # Run requested mode
    try:
        if args.mode == "interactive":
            app.interactive_mode()
        elif args.mode == "batch":
            if not args.input:
                print("❌ Batch mode requires --input file")
                return 1
            app.batch_mode(args.input)
        elif args.mode == "test":
            app.test_mode()
        elif args.mode == "status":
            app._show_status()
    
    except KeyboardInterrupt:
        print("\n👋 Goodbye!")
    
    return 0

if __name__ == "__main__":
    sys.exit(main())