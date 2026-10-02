# Verification Guide

## What is proved

| Claim | Status | Verification |
|-------|--------|-------------|
| N₀(d) = 0 for k = 3..15, S = ⌈k·log₂3⌉ | **CHECKED** (Lean 4.15, `native_decide`, 0 sorry; not re-checked after lean4#14576) | `lean/verified/`, `lake build` |
| Steiner's equation | proof written in Lean (Mathlib v4.29.0-rc2); the committed build file does not reach it (see README erratum) | `lean/skeleton/JunctionTheorem.lean`, `steiner_equation` |
| Nonsurjectivity k ≥ 18 | Lean proof **conditional on the axiom `small_gap_crystal_bound`** (k ≥ 666); same build caveat | `lean/skeleton/`, `crystal_nonsurjectivity` |
| No cycle with k ≤ 91 | **PROVED** (external) | Christian Hercher, J. Integer Seq. 26 (2023), Art. 23.3.5 (m-cycles, m ≤ 91; m ≤ k) |
| Spectral gap ρ_p < 1 | numerical (20 primes) + Wielandt argument (paper §6); says nothing on N₀ | `scripts/spectral_analysis.py` |

## What is NOT proved

| Claim | Status | Issue |
|-------|--------|-------|
| N₀(d) = 0 for k > 15 | **OPEN** | Lean verified stops at k=15 |
| Range Exclusion k=3..10000 | **INVALID** | lean/range-exclusion/ uses wrong corrsum formula |
| Baker argument k ≥ 10001 | **INVALID** | Applies to wrong function |
| N₀(d) = 0 for all k | **OPEN** | Gap between nonsurjectivity and N₀=0 |
| No nontrivial cycle (any k) | **NOT PROVED** | axiom `simons_de_weger` (skeleton, l. 551) is false as written; `no_positive_cycle` assumes its conclusion (`QuasiUniformity`) |

## The corrsum formula

The correct Steiner formula (proved in `lean/skeleton/JunctionTheorem.lean`):

    n₁ · (2^S − 3^k) = Σ_{i=0}^{k-1} 3^{k-1-i} · 2^{A_i}

where A = (0, A_1, ..., A_{k-1}) are cumulative positions with 0 < A_1 < ... < A_{k-1} < S.

This is implemented correctly in `lean/verified/CollatzVerified/Basic.lean` as `corrSumList`
with `compList` (which uses `enumIncr` to generate strictly increasing position sequences).

The `lean/range-exclusion/` module uses a DIFFERENT formula (`enumMonotone` with gap values).
See `docs/AUDIT_CORRSUM.md`.

## Lean compilation

```bash
cd lean/verified && lake build          # 280 theorems, 0 sorry — CORRECT
cd lean/skeleton                        # Requires Lean 4.29 + Mathlib
cd lean/range-exclusion && lake build   # Compiles but proves wrong thing — see WARNING.md
```
