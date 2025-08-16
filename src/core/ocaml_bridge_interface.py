#!/usr/bin/env python3
"""
OCaml Bridge Interface - Python wrapper for OCaml-coordinated execution
Integrates OCaml maximum parallelism into the main AutoProver system
"""

import subprocess
import json
import os
import time
from typing import Dict, Optional, List

class OCamlBridgeInterface:
    """Interface to OCaml parallel execution coordinator"""
    
    def __init__(self):
        self.ocaml_bridge_path = "/home/scott/Repo/AutoProver/src/core/ocaml_python_bridge"
        self.is_compiled = False
        self._ensure_ocaml_bridge()
    
    def _ensure_ocaml_bridge(self):
        """Ensure OCaml bridge is compiled and ready"""
        try:
            # Check if already compiled
            if os.path.exists(self.ocaml_bridge_path):
                print("[OCaml-Interface] ✅ OCaml bridge found", flush=True)
                self.is_compiled = True
                return
            
            # Compile the bridge
            print("[OCaml-Interface] 🔧 Compiling OCaml bridge...", flush=True)
            compile_script = "/home/scott/Repo/AutoProver/src/core/compile_ocaml_bridge.sh"
            
            if os.path.exists(compile_script):
                result = subprocess.run([compile_script], 
                                      capture_output=True, text=True, timeout=30)
                
                if result.returncode == 0 and os.path.exists(self.ocaml_bridge_path):
                    print("[OCaml-Interface] ✅ OCaml bridge compiled successfully", flush=True)
                    self.is_compiled = True
                else:
                    print(f"[OCaml-Interface] ❌ Compilation failed: {result.stderr}", flush=True)
            else:
                print("[OCaml-Interface] ❌ Compile script not found", flush=True)
                
        except Exception as e:
            print(f"[OCaml-Interface] ❌ Bridge setup failed: {e}", flush=True)
    
    def execute_parallel_proof_attempt(self, goal: str) -> Optional[Dict]:
        """Execute proof attempt using OCaml maximum parallelism"""
        if not self.is_compiled:
            print("[OCaml-Interface] ❌ OCaml bridge not available", flush=True)
            return None
        
        try:
            print(f"[OCaml-Interface] 🚀 Delegating to OCaml coordinator: {goal[:50]}...", flush=True)
            start_time = time.time()
            
            # Execute OCaml bridge with goal
            process = subprocess.Popen(
                [self.ocaml_bridge_path],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
            
            # Send goal to OCaml
            stdout, stderr = process.communicate(input=goal, timeout=60)
            execution_time = time.time() - start_time
            
            if process.returncode == 0:
                # Parse OCaml output
                result = self._parse_ocaml_output(stdout, stderr, execution_time)
                print(f"[OCaml-Interface] ✅ OCaml coordination completed in {execution_time:.3f}s", flush=True)
                return result
            else:
                print(f"[OCaml-Interface] ❌ OCaml process failed: {stderr}", flush=True)
                return None
                
        except subprocess.TimeoutExpired:
            print("[OCaml-Interface] ⏰ OCaml execution timed out", flush=True)
            try:
                process.kill()
            except:
                pass
            return None
            
        except Exception as e:
            print(f"[OCaml-Interface] ❌ OCaml execution error: {e}", flush=True)
            return None
    
    def _parse_ocaml_output(self, stdout: str, stderr: str, execution_time: float) -> Dict:
        """Parse OCaml bridge output into standardized format"""
        print(f"[OCaml-Interface] 📥 Parsing OCaml output ({len(stdout)} chars)", flush=True)
        
        # Extract key information from OCaml output
        lines = stdout.split('\n')
        
        # Look for result indicators
        bot_name = "ocaml_coordinated"
        tactic = "auto."
        confidence = 0.5
        success = False
        consensus_score = 0.0
        
        for line in lines:
            if "FINAL RESULT" in line or "Consensus winner" in line:
                success = True
            elif "Bot:" in line:
                # Extract bot name
                parts = line.split("Bot:")
                if len(parts) > 1:
                    bot_name = parts[1].strip().split()[0]
            elif "Tactic:" in line:
                # Extract tactic
                parts = line.split("Tactic:")
                if len(parts) > 1:
                    tactic = parts[1].strip()
            elif "Confidence:" in line:
                # Extract confidence
                try:
                    parts = line.split("Confidence:")
                    if len(parts) > 1:
                        confidence = float(parts[1].strip().split()[0])
                except:
                    pass
            elif "score:" in line:
                # Extract consensus score
                try:
                    parts = line.split("score:")
                    if len(parts) > 1:
                        consensus_score = float(parts[1].strip().rstrip(')').split()[0])
                except:
                    pass
        
        # Check for success indicators
        if "✅" in stdout or "SUCCESS" in stdout or success:
            success = True
        
        result = {
            "success": success,
            "tactic": tactic,
            "confidence": confidence,
            "bot": f"{bot_name} (OCaml coordinated)",
            "method": "ocaml_maximum_parallelism",
            "consensus_score": consensus_score,
            "blue_block": True,  # OCaml coordination is always blue
            "inference_time": execution_time,
            "ocaml_stdout": stdout[:200] + "..." if len(stdout) > 200 else stdout,
            "parallel_execution": True
        }
        
        return result
    
    def is_available(self) -> bool:
        """Check if OCaml bridge is available"""
        return self.is_compiled and os.path.exists(self.ocaml_bridge_path)
    
    def get_stats(self) -> Dict:
        """Get OCaml bridge statistics"""
        return {
            "available": self.is_available(),
            "bridge_path": self.ocaml_bridge_path,
            "compiled": self.is_compiled
        }

# Global OCaml bridge instance
_ocaml_bridge = None

def get_ocaml_bridge() -> OCamlBridgeInterface:
    """Get global OCaml bridge instance"""
    global _ocaml_bridge
    if _ocaml_bridge is None:
        _ocaml_bridge = OCamlBridgeInterface()
    return _ocaml_bridge

def ocaml_coordinated_proof_attempt(goal: str) -> Optional[Dict]:
    """Execute proof attempt with OCaml coordination"""
    bridge = get_ocaml_bridge()
    return bridge.execute_parallel_proof_attempt(goal)

if __name__ == "__main__":
    # Test the OCaml bridge interface
    print("🧪 Testing OCaml Bridge Interface")
    
    bridge = OCamlBridgeInterface()
    print(f"Bridge available: {bridge.is_available()}")
    
    if bridge.is_available():
        test_goal = "forall n : nat, n + 0 = n"
        result = bridge.execute_parallel_proof_attempt(test_goal)
        
        print(f"\n📊 Test Result:")
        if result:
            print(f"  Success: {result['success']}")
            print(f"  Tactic: {result['tactic']}")
            print(f"  Bot: {result['bot']}")
            print(f"  Time: {result['inference_time']:.3f}s")
        else:
            print("  ❌ No result")
    else:
        print("❌ OCaml bridge not available")