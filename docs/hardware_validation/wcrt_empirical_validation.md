# AG9-C: WCRT Empirical Validation Report

## Purpose

Validates the theoretical Worst-Case Response Time (WCRT) bound from the
`wcrtBound_unfold` theorem against measured scheduling latencies on physical
RPi5 hardware.

## Theoretical Bound

From `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean`:

```
WCRT = D * L_max + N * (B + P)
```

Where:
- `D` = number of scheduling domains
- `L_max` = maximum domain timeslice length
- `N` = number of threads with higher or equal priority
- `B` = maximum blocking time (from PIP analysis)
- `P` = maximum CBS budget period

## Measurement Infrastructure

### Cycle Counter (AG9-C instrumentation)

The `profiling` module in `rust/sele4n-hal/src/profiling.rs` provides:
- `read_cycle_counter()`: Reads PMCCNTR_EL0 (CPU cycle counter)
- `enable_cycle_counter()`: Enables PMU cycle counting
- `read_system_counter()`: Reads CNTPCT_EL0 (54 MHz system counter)
- `LatencyStats`: Min/max/sum/count accumulator

### Measurement Points

1. **Timer tick handler latency**: Cycles from timer interrupt to handler completion
2. **Scheduling decision latency**: Cycles for `schedule` transition
3. **Context switch latency**: Cycles for full save/restore TrapFrame
4. **End-to-end WCRT**: Cycles from thread becoming runnable to execution start

### Measurement Protocol

1. Enable PMU cycle counter during boot (`enable_cycle_counter()`)
2. Record cycle counter at each timer tick interrupt entry/exit
3. Accumulate 10,000+ samples in `LatencyStats`
4. Compute statistics: min, max, mean, p99, p99.9

## Results

| Metric | Expected | Measured | Status |
|--------|----------|----------|--------|
| Timer tick handler latency | < 1000 cycles | *pending* | PENDING |
| Scheduling decision latency | < 5000 cycles | *pending* | PENDING |
| Context switch latency | < 2000 cycles | *pending* | PENDING |
| End-to-end WCRT | < D*L_max + N*(B+P) | *pending* | PENDING |

## Statistical Summary

*(To be populated after hardware measurement)*

| Statistic | Timer Tick | Schedule | Context Switch |
|-----------|-----------|----------|----------------|
| Min | - | - | - |
| Max | - | - | - |
| Mean | - | - | - |
| P99 | - | - | - |
| P99.9 | - | - | - |
| Samples | - | - | - |

## Analysis

### Expected Behavior

On Cortex-A76 @ 2.4 GHz:
- 1 cycle ≈ 0.42 ns
- Timer tick interval: 1 ms = 2,400,000 cycles
- Expected handler latency: 100-500 cycles (GIC ACK + reprogram + EOI)
- Expected schedule latency: 1000-3000 cycles (run queue lookup + selection)
- Expected context switch: 500-1500 cycles (TrapFrame save/restore)

### WCRT Bound Comparison

The theoretical bound from `wcrtBound_unfold` is conservative — it accounts
for worst-case interference from all higher-priority threads across all
domains. Empirical measurements should be well below the theoretical bound
in typical configurations.

## Cross-Reference

- Theoretical bound: `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean`
- Timer model: `SeLe4n/Kernel/Architecture/TimerModel.lean`
- Profiling module: `rust/sele4n-hal/src/profiling.rs`
- Timer driver: `rust/sele4n-hal/src/timer.rs`
