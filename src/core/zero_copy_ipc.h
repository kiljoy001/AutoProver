/*
 * Zero-Copy IPC for AutoProver Proof Bots
 * 
 * High-performance shared memory architecture for passing proof states
 * between specialist bots without serialization overhead.
 */

#ifndef AUTOPROVER_ZERO_COPY_IPC_H
#define AUTOPROVER_ZERO_COPY_IPC_H

#include <stdint.h>
#include <stdatomic.h>
#include <sys/mman.h>
#include <sys/ipc.h>
#include <sys/shm.h>

/* ========== Core Structures ========== */

/* Memory layout for zero-copy proof state */
typedef struct {
    /* Immutable header - never changes after creation */
    uint64_t magic;           /* 0xC0Q50DA6 - "COQ-GHOSTDAG" */
    uint32_t version;         /* Protocol version */
    uint32_t max_bots;        /* Maximum parallel bots */
    uint64_t total_size;      /* Total shared memory size */
    
    /* Atomic counters for lock-free coordination */
    atomic_uint64_t epoch;    /* Global proof epoch */
    atomic_uint32_t active_bots;
    atomic_uint32_t completed_proofs;
    
    /* Memory regions */
    uint64_t proof_dag_offset;      /* Offset to proof DAG */
    uint64_t message_ring_offset;   /* Offset to message ring buffer */
    uint64_t proof_pool_offset;     /* Offset to proof state pool */
    uint64_t tactic_cache_offset;   /* Offset to tactic cache */
} ProofArena;

/* Proof state stored in shared memory */
typedef struct {
    uint64_t id;              /* Unique proof ID */
    uint32_t goal_hash;       /* Hash of current goal */
    uint32_t parent_count;    /* Number of parent states */
    
    /* Proof content offsets (into string pool) */
    uint32_t goal_offset;     /* Current goal string */
    uint32_t goal_length;
    uint32_t context_offset;  /* Proof context */
    uint32_t context_length;
    uint32_t tactic_offset;   /* Applied tactic */
    uint32_t tactic_length;
    
    /* Metadata */
    uint16_t specialist_id;   /* Which bot created this */
    uint16_t confidence;      /* Confidence score (0-1000) */
    uint32_t gas_used;        /* Computational cost */
    
    /* DAG pointers */
    uint64_t parent_ids[8];   /* Parent proof states */
    atomic_uint32_t child_count;
    
    /* Consensus data */
    atomic_int32_t blue_score;  /* GhostDAG blue score */
    atomic_bool is_blue;         /* Part of main chain */
    atomic_bool is_complete;     /* Proof complete */
} ProofState;

/* Lock-free message for bot communication */
typedef struct {
    atomic_uint64_t sequence;    /* Message sequence number */
    uint16_t sender_id;          /* Bot ID */
    uint16_t message_type;       /* Message type enum */
    uint32_t payload_size;       /* Size of payload */
    
    union {
        /* New proof attempt */
        struct {
            uint64_t proof_id;
            uint32_t goal_offset;
        } new_proof;
        
        /* Proof completion */
        struct {
            uint64_t proof_id;
            uint32_t tactic_offset;
            uint16_t confidence;
        } proof_done;
        
        /* Request for help */
        struct {
            uint64_t stuck_proof_id;
            uint32_t error_offset;
        } help_request;
        
        /* Lemma discovery */
        struct {
            uint32_t lemma_offset;
            uint32_t relevance_score;
        } lemma_found;
    } payload;
} BotMessage;

/* Ring buffer for messages */
typedef struct {
    atomic_uint64_t write_pos;
    atomic_uint64_t read_pos[32];  /* Per-bot read positions */
    uint32_t capacity;
    uint32_t message_size;
    char messages[];  /* Flexible array of messages */
} MessageRing;

/* ========== Memory Management ========== */

/* Initialize shared memory arena */
ProofArena* proof_arena_create(size_t size, uint32_t max_bots);

/* Attach to existing arena */
ProofArena* proof_arena_attach(key_t key);

/* Allocate proof state in arena */
ProofState* proof_state_alloc(ProofArena* arena);

/* Get pointer to proof DAG */
static inline void* get_proof_dag(ProofArena* arena) {
    return (char*)arena + arena->proof_dag_offset;
}

/* Get message ring buffer */
static inline MessageRing* get_message_ring(ProofArena* arena) {
    return (MessageRing*)((char*)arena + arena->message_ring_offset);
}

/* ========== Lock-Free Operations ========== */

/* Send message to all bots (lock-free) */
int send_bot_message(ProofArena* arena, BotMessage* msg);

/* Receive next message for bot (lock-free) */
int recv_bot_message(ProofArena* arena, uint16_t bot_id, BotMessage* msg);

/* Atomic proof state update */
int update_proof_state(ProofState* state, uint32_t new_score);

/* Compare-and-swap for consensus */
bool cas_blue_selection(ProofState* state, bool expected, bool new_val);

/* ========== Zero-Copy String Pool ========== */

/* String stored in shared memory pool */
typedef struct {
    uint32_t length;
    uint32_t hash;
    char data[];
} PooledString;

/* Intern string in pool (returns offset) */
uint32_t string_pool_intern(ProofArena* arena, const char* str, uint32_t len);

/* Get string from pool */
const char* string_pool_get(ProofArena* arena, uint32_t offset);

/* ========== Memory Barriers ========== */

/* Ensure all writes are visible before proceeding */
#define MEMORY_BARRIER() __atomic_thread_fence(__ATOMIC_SEQ_CST)

/* Read barrier for proof state */
#define READ_PROOF_STATE(state) do { \
    __atomic_load(&(state)->epoch, &epoch, __ATOMIC_ACQUIRE); \
} while(0)

/* Write barrier for proof state */  
#define WRITE_PROOF_STATE(state) do { \
    __atomic_store(&(state)->epoch, &epoch, __ATOMIC_RELEASE); \
} while(0)

/* ========== NUMA Optimization ========== */

#ifdef NUMA_AWARE
/* Pin bot to NUMA node for locality */
int pin_bot_numa(uint16_t bot_id, int numa_node);

/* Allocate proof states on specific NUMA node */
ProofState* proof_state_alloc_numa(ProofArena* arena, int numa_node);
#endif

/* ========== Performance Monitoring ========== */

typedef struct {
    atomic_uint64_t cache_hits;
    atomic_uint64_t cache_misses;
    atomic_uint64_t messages_sent;
    atomic_uint64_t proofs_completed;
    atomic_uint64_t memory_used;
} PerfCounters;

/* Get performance counters */
PerfCounters* get_perf_counters(ProofArena* arena);

#endif /* AUTOPROVER_ZERO_COPY_IPC_H */