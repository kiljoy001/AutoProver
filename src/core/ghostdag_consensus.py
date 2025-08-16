#!/usr/bin/env python3
"""
GhostDAG Consensus for Parallel Proof Attempts
Implements the GhostDAG protocol to select best proof tactics from multiple bots
"""

import time
import hashlib
import json
from collections import defaultdict, deque
from dataclasses import dataclass
from typing import List, Dict, Set, Optional, Tuple
import threading
import concurrent.futures

@dataclass
class ProofAttempt:
    """A proof attempt from a bot"""
    attempt_id: str
    bot_name: str
    goal: str
    tactic: str
    confidence: float
    verification_status: str  # "pending", "verified", "failed"
    timestamp: float
    dependencies: List[str]  # Parent attempts this builds on
    verification_time: float = 0.0
    error: Optional[str] = None

@dataclass
class GhostDAGBlock:
    """A block in the GhostDAG representing proof attempts"""
    block_id: str
    proof_attempts: List[ProofAttempt]
    parents: List[str]  # Parent block IDs
    timestamp: float
    is_blue: bool = False  # Blue blocks are in the main chain
    blue_score: int = 0
    
    def __post_init__(self):
        if not self.block_id:
            content = f"{self.timestamp}_{len(self.proof_attempts)}_{self.parents}"
            self.block_id = hashlib.sha256(content.encode()).hexdigest()[:16]

class GhostDAGConsensus:
    """GhostDAG consensus for selecting best proof tactics"""
    
    def __init__(self, k=3, max_parallel_attempts=8):
        """
        Initialize GhostDAG consensus
        k: maximum number of blocks a block can reference
        max_parallel_attempts: maximum parallel proof attempts
        """
        self.k = k
        self.max_parallel_attempts = max_parallel_attempts
        
        # DAG storage
        self.blocks: Dict[str, GhostDAGBlock] = {}
        self.genesis_block_id = self._create_genesis_block()
        self.tips: Set[str] = {self.genesis_block_id}
        
        # Consensus state
        self.blue_blocks: Set[str] = {self.genesis_block_id}
        self.virtual_block: Optional[GhostDAGBlock] = None
        
        # Active proof attempts
        self.active_attempts: Dict[str, ProofAttempt] = {}
        self.completed_attempts: Dict[str, ProofAttempt] = {}
        
        # Thread safety
        self.lock = threading.RLock()
        
        print("[GhostDAG] Consensus engine initialized", flush=True)
    
    def _create_genesis_block(self) -> str:
        """Create the genesis block"""
        genesis = GhostDAGBlock(
            block_id="genesis",
            proof_attempts=[],
            parents=[],
            timestamp=time.time(),
            is_blue=True,
            blue_score=0
        )
        self.blocks["genesis"] = genesis
        return "genesis"
    
    def submit_proof_attempts(self, goal: str, bot_results: List[Dict]) -> str:
        """Submit multiple proof attempts from different bots"""
        with self.lock:
            attempts = []
            
            for result in bot_results:
                attempt = ProofAttempt(
                    attempt_id=self._generate_attempt_id(),
                    bot_name=result.get("bot", "unknown"),
                    goal=goal,
                    tactic=result.get("tactic", ""),
                    confidence=result.get("confidence", 0.0),
                    verification_status="pending",
                    timestamp=time.time(),
                    dependencies=[]
                )
                
                attempts.append(attempt)
                self.active_attempts[attempt.attempt_id] = attempt
            
            # Create new block with these attempts
            block = self._create_block(attempts)
            self._add_block(block)
            
            print(f"[GhostDAG] Submitted {len(attempts)} parallel attempts for: {goal[:50]}...", flush=True)
            return block.block_id
    
    def _generate_attempt_id(self) -> str:
        """Generate unique attempt ID"""
        return hashlib.sha256(f"{time.time()}_{len(self.active_attempts)}".encode()).hexdigest()[:12]
    
    def _create_block(self, attempts: List[ProofAttempt]) -> GhostDAGBlock:
        """Create a new block with proof attempts"""
        # Select parents (up to k recent tips)
        parents = list(self.tips)[:self.k]
        
        block = GhostDAGBlock(
            block_id="",  # Will be generated in __post_init__
            proof_attempts=attempts,
            parents=parents,
            timestamp=time.time()
        )
        
        return block
    
    def _add_block(self, block: GhostDAGBlock):
        """Add block to DAG and update consensus"""
        self.blocks[block.block_id] = block
        
        # Update tips
        for parent_id in block.parents:
            self.tips.discard(parent_id)
        self.tips.add(block.block_id)
        
        # Run GhostDAG consensus algorithm
        self._update_consensus()
        
        print(f"[GhostDAG] Added block {block.block_id} with {len(block.proof_attempts)} attempts", flush=True)
    
    def _update_consensus(self):
        """Update GhostDAG consensus and blue blocks"""
        # Find the virtual block (combining all tips)
        virtual_parents = list(self.tips)
        self.virtual_block = GhostDAGBlock(
            block_id="virtual",
            proof_attempts=[],
            parents=virtual_parents,
            timestamp=time.time()
        )
        
        # Run GHOSTDAG algorithm to determine blue blocks
        self._run_ghostdag_coloring()
        
        # Update blue scores
        self._update_blue_scores()
    
    def _run_ghostdag_coloring(self):
        """Run the GHOSTDAG coloring algorithm"""
        if not self.virtual_block:
            return
        
        # Topological ordering of blocks
        ordered_blocks = self._topological_sort()
        
        # Reset coloring
        for block_id in self.blocks:
            self.blocks[block_id].is_blue = False
        
        # Genesis is always blue
        self.blocks[self.genesis_block_id].is_blue = True
        self.blue_blocks = {self.genesis_block_id}
        
        # Color blocks according to GHOSTDAG
        for block_id in ordered_blocks:
            if block_id == self.genesis_block_id:
                continue
                
            block = self.blocks[block_id]
            
            # Count blue parents
            blue_parents = sum(1 for p in block.parents if p in self.blue_blocks)
            red_parents = len(block.parents) - blue_parents
            
            # Block is blue if it doesn't create too much red
            if red_parents <= self.k:
                block.is_blue = True
                self.blue_blocks.add(block_id)
    
    def _topological_sort(self) -> List[str]:
        """Topological sort of blocks by timestamp"""
        return sorted(self.blocks.keys(), key=lambda bid: self.blocks[bid].timestamp)
    
    def _update_blue_scores(self):
        """Update blue scores for all blocks"""
        for block_id in self.blocks:
            blue_ancestors = self._count_blue_ancestors(block_id)
            self.blocks[block_id].blue_score = blue_ancestors
    
    def _count_blue_ancestors(self, block_id: str) -> int:
        """Count blue ancestors of a block"""
        visited = set()
        blue_count = 0
        queue = deque([block_id])
        
        while queue:
            current = queue.popleft()
            if current in visited:
                continue
            
            visited.add(current)
            
            if current in self.blue_blocks:
                blue_count += 1
            
            if current in self.blocks:
                queue.extend(self.blocks[current].parents)
        
        return blue_count
    
    def get_consensus_tactic(self, goal: str, timeout=10.0) -> Optional[Dict]:
        """Get the consensus tactic for a goal using GhostDAG selection"""
        start_time = time.time()
        
        while time.time() - start_time < timeout:
            with self.lock:
                # Find attempts for this goal
                goal_attempts = []
                for attempt in self.active_attempts.values():
                    if attempt.goal == goal:
                        goal_attempts.append(attempt)
                
                for attempt in self.completed_attempts.values():
                    if attempt.goal == goal:
                        goal_attempts.append(attempt)
                
                if not goal_attempts:
                    time.sleep(0.1)
                    continue
                
                # Score attempts using GhostDAG consensus
                scored_attempts = self._score_attempts_by_consensus(goal_attempts)
                
                if scored_attempts:
                    best_attempt = scored_attempts[0]
                    
                    return {
                        "tactic": best_attempt.tactic,
                        "confidence": best_attempt.confidence,
                        "bot": best_attempt.bot_name,
                        "consensus_score": self._get_consensus_score(best_attempt),
                        "verification_status": best_attempt.verification_status,
                        "attempt_id": best_attempt.attempt_id,
                        "blue_block": self._is_in_blue_block(best_attempt)
                    }
            
            time.sleep(0.1)
        
        return None
    
    def _score_attempts_by_consensus(self, attempts: List[ProofAttempt]) -> List[ProofAttempt]:
        """Score and rank attempts using GhostDAG consensus"""
        scored = []
        
        for attempt in attempts:
            score = self._calculate_consensus_score(attempt)
            scored.append((score, attempt))
        
        # Sort by consensus score (descending)
        scored.sort(key=lambda x: x[0], reverse=True)
        
        return [attempt for score, attempt in scored]
    
    def _calculate_consensus_score(self, attempt: ProofAttempt) -> float:
        """Calculate consensus score for an attempt"""
        base_score = attempt.confidence
        
        # Bonus for verified attempts
        if attempt.verification_status == "verified":
            base_score += 0.3
        elif attempt.verification_status == "failed":
            base_score -= 0.5
        
        # Bonus for being in blue blocks
        if self._is_in_blue_block(attempt):
            base_score += 0.2
        
        # Penalty for slow verification
        if attempt.verification_time > 5.0:
            base_score -= 0.1
        
        # Bonus for recent attempts
        age = time.time() - attempt.timestamp
        if age < 1.0:
            base_score += 0.1
        
        return max(0.0, min(1.0, base_score))
    
    def _is_in_blue_block(self, attempt: ProofAttempt) -> bool:
        """Check if attempt is in a blue block"""
        for block_id, block in self.blocks.items():
            if block.is_blue:
                for block_attempt in block.proof_attempts:
                    if block_attempt.attempt_id == attempt.attempt_id:
                        return True
        return False
    
    def _get_consensus_score(self, attempt: ProofAttempt) -> float:
        """Get the consensus score for an attempt"""
        return self._calculate_consensus_score(attempt)
    
    def mark_attempt_verified(self, attempt_id: str, verification_time: float = 0.0):
        """Mark an attempt as verified"""
        with self.lock:
            if attempt_id in self.active_attempts:
                attempt = self.active_attempts[attempt_id]
                attempt.verification_status = "verified"
                attempt.verification_time = verification_time
                
                # Move to completed
                self.completed_attempts[attempt_id] = attempt
                del self.active_attempts[attempt_id]
                
                print(f"[GhostDAG] Attempt {attempt_id[:8]} verified in {verification_time:.3f}s", flush=True)
    
    def mark_attempt_failed(self, attempt_id: str, error: str):
        """Mark an attempt as failed"""
        with self.lock:
            if attempt_id in self.active_attempts:
                attempt = self.active_attempts[attempt_id]
                attempt.verification_status = "failed"
                attempt.error = error
                
                # Move to completed
                self.completed_attempts[attempt_id] = attempt
                del self.active_attempts[attempt_id]
                
                print(f"[GhostDAG] Attempt {attempt_id[:8]} failed: {error}", flush=True)
    
    def get_stats(self) -> Dict:
        """Get consensus statistics"""
        with self.lock:
            blue_count = len(self.blue_blocks)
            total_blocks = len(self.blocks)
            
            return {
                "total_blocks": total_blocks,
                "blue_blocks": blue_count,
                "red_blocks": total_blocks - blue_count,
                "tips": len(self.tips),
                "active_attempts": len(self.active_attempts),
                "completed_attempts": len(self.completed_attempts),
                "k_parameter": self.k,
                "max_parallel": self.max_parallel_attempts
            }
    
    def cleanup_old_attempts(self, max_age=300.0):
        """Clean up old completed attempts"""
        with self.lock:
            current_time = time.time()
            to_remove = []
            
            for attempt_id, attempt in self.completed_attempts.items():
                if current_time - attempt.timestamp > max_age:
                    to_remove.append(attempt_id)
            
            for attempt_id in to_remove:
                del self.completed_attempts[attempt_id]
            
            if to_remove:
                print(f"[GhostDAG] Cleaned up {len(to_remove)} old attempts", flush=True)

# Global consensus instance
_consensus_instance = None

def get_consensus() -> GhostDAGConsensus:
    """Get global consensus instance"""
    global _consensus_instance
    if _consensus_instance is None:
        _consensus_instance = GhostDAGConsensus()
    return _consensus_instance

def parallel_proof_attempt(goal: str, bots: Dict, consensus: GhostDAGConsensus) -> Optional[Dict]:
    """Run MAXIMUM PARALLELISM proof attempts with GhostDAG consensus"""
    start_time = time.time()
    print(f"[GhostDAG] 🚀 PARALLEL EXECUTION: {len(bots)} bots for: {goal[:50]}...", flush=True)
    
    bot_results = []
    
    # Use process pool for TRUE parallelism (bypasses Python GIL)
    max_workers = min(len(bots), 8)  # Don't overwhelm system
    
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        # Submit ALL bot tasks immediately for maximum parallelism
        future_to_bot = {}
        submission_start = time.time()
        
        for bot_name, bot in bots.items():
            try:
                if bot_name.startswith("coqgym"):
                    if bot_name == "coqgym_gpu":
                        # GPU bot gets dedicated thread
                        future = executor.submit(bot.predict_tactic_gpu, [goal])
                        print(f"[GhostDAG] 🔥 Submitted GPU bot: {bot_name}", flush=True)
                    else:
                        future = executor.submit(bot.predict_tactic_real, goal)
                        print(f"[GhostDAG] 💻 Submitted CPU bot: {bot_name}", flush=True)
                elif bot_name == "proverbot9001":
                    future = executor.submit(bot.generate_complete_proof, goal)
                    print(f"[GhostDAG] 🧠 Submitted ProverBot: {bot_name}", flush=True)
                else:
                    print(f"[GhostDAG] ⚠️  Unknown bot type: {bot_name}", flush=True)
                    continue
                
                future_to_bot[future] = bot_name
                
            except Exception as e:
                print(f"[GhostDAG] ❌ Failed to submit {bot_name}: {e}", flush=True)
        
        submission_time = time.time() - submission_start
        print(f"[GhostDAG] ⚡ All {len(future_to_bot)} bots submitted in {submission_time:.3f}s", flush=True)
        
        # Collect results AS THEY COMPLETE (first-come-first-served)
        completed_count = 0
        for future in concurrent.futures.as_completed(future_to_bot, timeout=30):
            bot_name = future_to_bot[future]
            completed_count += 1
            
            try:
                result_start = time.time()
                result = future.result()
                result_time = time.time() - result_start
                
                # Handle GPU batch results
                if isinstance(result, list):
                    result = result[0]
                
                # Normalize result format
                normalized = {
                    "bot": bot_name,
                    "tactic": result.get("tactic", result.get("proof_script", "")),
                    "confidence": result.get("confidence", 0.0),
                    "verified": result.get("verified", result.get("proof_complete", False)),
                    "execution_time": result_time,
                    "completion_order": completed_count
                }
                
                bot_results.append(normalized)
                
                print(f"[GhostDAG] ✅ Bot {completed_count}/{len(future_to_bot)} completed: {bot_name} ({result_time:.3f}s)", flush=True)
                
            except concurrent.futures.TimeoutError:
                print(f"[GhostDAG] ⏰ Bot {bot_name} timed out", flush=True)
            except Exception as e:
                print(f"[GhostDAG] ❌ Bot {bot_name} failed: {e}", flush=True)
    
    if not bot_results:
        return None
    
    # Submit to consensus
    block_id = consensus.submit_proof_attempts(goal, bot_results)
    
    # Get consensus result
    consensus_result = consensus.get_consensus_tactic(goal, timeout=10.0)
    
    if consensus_result:
        print(f"[GhostDAG] Consensus selected: {consensus_result['tactic'][:50]}... (score: {consensus_result['consensus_score']:.2f})", flush=True)
    
    return consensus_result

if __name__ == "__main__":
    # Test the consensus engine
    consensus = GhostDAGConsensus()
    
    # Simulate proof attempts
    test_results = [
        {"bot": "coqgym", "tactic": "auto.", "confidence": 0.6, "verified": True},
        {"bot": "proverbot", "tactic": "induction n; auto.", "confidence": 0.8, "verified": True},
        {"bot": "coqhammer", "tactic": "lia.", "confidence": 0.9, "verified": True}
    ]
    
    goal = "forall n : nat, n + 0 = n"
    block_id = consensus.submit_proof_attempts(goal, test_results)
    
    # Mark some as verified
    for attempt_id in list(consensus.active_attempts.keys())[:2]:
        consensus.mark_attempt_verified(attempt_id, 0.1)
    
    result = consensus.get_consensus_tactic(goal)
    print(f"Consensus result: {result}")
    
    stats = consensus.get_stats()
    print(f"Consensus stats: {stats}")