# AG9-D: RunQueue Cache Performance Report

## Purpose

Profile RunQueue operations on Cortex-A76 to validate the two-stage selection
optimization from AG1-A and characterize cache performance for scheduling
hot paths.

## Measurement Infrastructure

Uses `LatencyStats` from `rust/sele4n-hal/src/profiling.rs` with PMCCNTR_EL0
cycle counter.

## Operations Profiled

### 1. RunQueue Insert

Insert a thread into the priority-indexed run queue. Measures cycles for
varying queue occupancy.

| Queue Size | Expected Cycles | Measured Cycles | Status |
|-----------|----------------|-----------------|--------|
| 1 thread | < 100 | *pending* | PENDING |
| 10 threads | < 200 | *pending* | PENDING |
| 50 threads | < 500 | *pending* | PENDING |
| 100 threads | < 1000 | *pending* | PENDING |

### 2. RunQueue Remove

Remove a specific thread from the run queue.

| Queue Size | Expected Cycles | Measured Cycles | Status |
|-----------|----------------|-----------------|--------|
| 1 thread | < 100 | *pending* | PENDING |
| 10 threads | < 200 | *pending* | PENDING |
| 50 threads | < 500 | *pending* | PENDING |
| 100 threads | < 1000 | *pending* | PENDING |

### 3. Two-Stage Selection (`chooseBestInBucketEffective`)

The AG1-A optimization uses a two-stage selection:
1. **Stage 1 (fast path)**: Check the highest-priority non-empty bucket
2. **Stage 2 (fallback)**: Full EDF scan within the bucket

| Scenario | Stage 1 Hit Rate | Total Cycles | Status |
|----------|-----------------|--------------|--------|
| Single priority | 100% | *pending* | PENDING |
| 2 priorities | ~50% | *pending* | PENDING |
| 8 priorities | ~12.5% | *pending* | PENDING |
| Mixed EDF | 0% (fallback) | *pending* | PENDING |

### 4. Cache Behavior

Cortex-A76 cache hierarchy:
- L1 D-cache: 64 KiB, 4-way, 64-byte lines
- L2 unified: 512 KiB, 8-way, 64-byte lines
- L3 unified: 2 MiB (shared)

| Metric | Expected | Measured | Status |
|--------|----------|----------|--------|
| L1 hit rate (insert) | > 90% | *pending* | PENDING |
| L1 hit rate (select) | > 85% | *pending* | PENDING |
| Working set (100 threads) | < 16 KiB | *pending* | PENDING |

## Analysis

### Two-Stage Selection Benefit

The two-stage selection avoids a full O(N) scan in the common case where
threads at the highest priority bucket have distinct deadlines. Stage 1
(bucket lookup) is O(1) via the priority bitmap; Stage 2 (EDF within bucket)
is O(k) where k is the number of threads at that priority level.

Expected improvement over flat scan:
- **Best case** (single priority per bucket): No EDF scan needed
- **Typical case** (2-3 per bucket): 60-80% reduction in comparison count
- **Worst case** (all same priority): Same as flat EDF scan

### Cache Optimization Considerations

RunQueue data structures are designed for cache efficiency:
- Priority buckets are contiguous in memory (array layout)
- Thread entries use compact representation (ObjId + deadline)
- Working set for typical workloads (< 50 threads) fits in L1 D-cache

## Cross-Reference

- RunQueue implementation: `SeLe4n/Kernel/Scheduler/RunQueue.lean`
- Selection optimization (AG1-A): `resolveInsertPriority` in `Operations/Selection.lean`
- Profiling module: `rust/sele4n-hal/src/profiling.rs`
