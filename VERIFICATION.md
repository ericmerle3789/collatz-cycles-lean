# Verification Guide

How to verify each claim in the paper.

## Sections 2–3: Steiner's equation and Range Exclusion

| Claim | Verification |
|-------|-------------|
| Steiner's equation (eq. 1–3) | `lean/skeleton/JunctionTheorem.lean`, theorem `steiner_equation` |
| corrsum definition | `lean/range-exclusion/CorrSumAvoidance/Basic.lean`, def `corrSum` |
| corrsum bounds (Proposition 2.1) | `lean/range-exclusion/CorrSumAvoidance/RangeExclusion.lean`, defs `cs_min`, `cs_max` |
| Range Exclusion check | `lean/range-exclusion/CorrSumAvoidance/RangeExclusion.lean`, def `checkRE` |

## Section 4: Certified computation (k ≤ 10000)

| Claim | Verification |
|-------|-------------|
| N₀(d(k)) = 0 for k = 3..40 | `lean/range-exclusion/CorrSumAvoidance/Theorems.lean` — one `native_decide` per k |
| N₀(d(k)) = 0 for k = 3..10000 | `lean/range-exclusion/CorrSumAvoidance/RangeExclusion.lean` — batch `native_decide` |
| 280 theorems, 0 sorry, 0 axiom | `lean/verified/` — run `lake build` then `grep -r sorry --include="*.lean"` |

To compile and verify:

```bash
cd lean/range-exclusion && lake build   # ~6 minutes
cd lean/verified && lake build          # requires Lean 4.15.0
```

## Section 5: Baker–Wüstholz (k ≥ 10001)

| Claim | Verification |
|-------|-------------|
| Baker–Wüstholz constant C₀ ≈ 2.6 × 10⁷ | `python scripts/baker_threshold.py` |
| range/d → 0 for large k | `python scripts/baker_threshold.py` (table output) |
| Baker axiom in Lean | `lean/range-exclusion/CorrSumAvoidance/RangeExclusion.lean`, line `axiom baker_lmn` |

## Section 6: Spectral analysis (supplementary)

| Claim | Verification |
|-------|-------------|
| Rank 1 at z = 1 (Theorem 6.1) | `python scripts/spectral_analysis.py` — column `rank@1` = 1 for all primes |
| Wielandt gap (Theorem 6.3) | `python scripts/spectral_analysis.py` — column `rho_p` < 1 for all primes |
| Doubly stochastic (Proposition 6.4) | `python scripts/spectral_analysis.py` — column `DS` = Y for all primes |
| ρ_p < 0.82 (Section 6.5) | `python scripts/spectral_analysis.py` — max ρ_p = 0.8205 at p = 7 |
| Transfer matrix Lean theorems | `lean/verified/CollatzVerified/TransferMatrix.lean` — 31 theorems |

## Section 8: Lean summary

| Claim | Verification |
|-------|-------------|
| 280 theorems across 7 modules | `lean/verified/CollatzVerified/` — 7 .lean files |
| 0 sorry, 0 axiom | `cd lean/verified && grep -r "sorry" --include="*.lean" \| grep -v "^.*--"` (all in comments) |
| Junction Theorem skeleton | `lean/skeleton/JunctionTheorem.lean` — combines Simons–de Weger + nonsurjectivity |
| Asymptotic bound k ≥ 666 | `lean/skeleton/AsymptoticBound.lean` — γ ≥ 1/40 proved |

## Junction Theorem architecture

The **Junction Theorem** (`lean/skeleton/JunctionTheorem.lean`) is the logical framework:

```
For every k ≥ 1:
  if k < 68  → Simons–de Weger (axiom, published 2005)
  if k ≥ 18  → nonsurjectivity: C(S−1, k−1) < d(k)
    - k ∈ [18, 665]  → native_decide (FiniteCases*.lean)
    - k ≥ 666         → asymptotic bound (AsymptoticBound.lean)
  overlap at 18 ≤ k ≤ 67 ensures no gap
```

The Range Exclusion (`lean/range-exclusion/`) provides a stronger, independent proof for k = 3..10000 that does not rely on nonsurjectivity but directly verifies that 0 ∉ [cs_min mod d, cs_max mod d].
