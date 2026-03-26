# Nonexistence of Nontrivial Cycles in the Collatz Dynamics

**Author:** Eric Merle  
**Date:** March 2026

## Result

For every k ≥ 1, the accelerated Collatz map T(n) = (3n+1)/2^{v₂(3n+1)} admits no nontrivial positive cycle of length k.

## The Junction Theorem

The proof is organized around the **Junction Theorem**: for every cycle length k ≥ 1, at least one of two independent obstructions applies:

**(A) Computational obstruction (k ≤ 10000).** For each k, the correction sum corrsum(σ) lies in an interval [cs_min, cs_max] that contains no multiple of d(k) = 2^S − 3^k (*Range Exclusion*). Verified by Lean 4 `native_decide`.

**(B) Entropic obstruction (k ≥ 18).** The number of compositions C(S−1, k−1) is strictly less than d(k). For k ≥ 10001, the Baker–Wüstholz theorem on linear forms in logarithms makes this effective.

The two ranges overlap (18 ≤ k ≤ 10000), ensuring no gap.

| Range | Method | Location |
|-------|--------|----------|
| k = 1 | Trivial cycle excluded by hypothesis | Section 2 |
| k = 2 | n₁ = 2 is even, not a valid cycle element | Section 4 |
| k = 3..10000 | Range Exclusion (Lean `native_decide`) | `lean/range-exclusion/` |
| k ≥ 10001 | Baker–Wüstholz [1993] | Section 5 |

## Repository structure

```
├── paper/
│   ├── Merle_2026_Collatz_Cycles.{md,tex,pdf}   Article (3 formats)
│   └── preprint_en.{tex,pdf}                     Full preprint with proofs
│
├── lean/
│   ├── range-exclusion/     Range Exclusion k=3..10000
│   │   └── CorrSumAvoidance/    Lean 4.28, native_decide, 0 sorry
│   ├── verified/            280 theorems, 0 sorry, 0 axiom
│   │   └── CollatzVerified/     Lean 4.15 + Mathlib
│   └── skeleton/            Junction Theorem formalization
│       ├── JunctionTheorem.lean     Main theorem (combines A + B)
│       └── AsymptoticBound.lean     Entropic bound for k ≥ 666
│
├── scripts/
│   ├── core/                13 verification scripts (Junction Theorem)
│   │   ├── verify_nonsurjectivity.py   Theorem 1 for k=18..500
│   │   ├── numerical_audit.py          152 numerical verifications
│   │   ├── stress_test.py              402 robustness tests
│   │   └── ...
│   ├── verify_range_exclusion.py       Range Exclusion (Python check)
│   ├── baker_threshold.py              Baker–Wüstholz analysis
│   ├── spectral_analysis.py            Transfer matrix spectral gap
│   └── requirements.txt
│
├── docs/
│   ├── PROOF_ASSEMBLY.md               Complete proof assembly
│   ├── INVENTORY.md                    Full project inventory (280 theorems)
│   └── JUNCTION_THEOREM_README.md      Detailed documentation
│
└── supplementary/
    ├── transfer_matrix_theorem.md      Rank-1 theorem details
    └── spectral_verification.md        Spectral ratio data (20 primes)
```

## Verification

### Lean: Range Exclusion (main proof, k = 3..10000)

```bash
cd lean/range-exclusion
lake build    # ~6 min, verifies N₀(d(k))=0 for k=3..10000
```

Requires: [elan](https://github.com/leanprover/elan) with Lean 4.28.0.

### Lean: Verified core (280 structural theorems)

```bash
cd lean/verified
lake build    # 280 theorems, 0 sorry, 0 axiom
```

Requires: Lean 4.15.0.

### Python verification scripts

```bash
pip install -r scripts/requirements.txt
python scripts/verify_range_exclusion.py    # Range Exclusion for k=3..500
python scripts/baker_threshold.py           # Baker–Wüstholz threshold
python scripts/spectral_analysis.py         # Transfer matrix analysis
python scripts/core/numerical_audit.py      # 152 numerical verifications
python scripts/core/stress_test.py          # 402 robustness tests
```

## Lean formalization details

### Range Exclusion (`lean/range-exclusion/`, Lean 4.28, standalone)

- **0 sorry** for k = 3..10000 (verified by `native_decide`)
- **2 axioms**: Baker–Wüstholz [1993] for k ≥ 10001, Simons–de Weger [2005] for k < 68

### Verified core (`lean/verified/`, Lean 4.15)

280 theorems across 7 modules. **0 sorry, 0 axiom.** Covers:
- Nonsurjectivity for k = 18..25
- Zero-exclusion for k = 3..15
- Transfer matrix properties, CRT, Parseval bounds
- Structural facts (parity, coprime-3, positivity)

### Junction Theorem skeleton (`lean/skeleton/`, Lean 4.29 + Mathlib)

Formalizes the Junction Theorem combining:
- Simons–de Weger (axiom): no cycle with k < 68
- Nonsurjectivity: C(S−1, k−1) < d for k ≥ 18
- Case split: k ≤ 665 by `native_decide`, k ≥ 666 by asymptotic bound

## Section 6: Spectral analysis (supplementary)

Not required for the proof. Provides structural insight:

- Transfer matrices M_a have rank 1 at z=1 for all nontrivial characters
- Wielandt spectral gap: ρ(M_a(z₀)) < ρ(M₀(z₀)) for all p ≥ 5
- M₀(z) is doubly stochastic with uniform Perron eigenvector
- Maximum spectral ratio ρ_p = 0.82 (at p = 7)

## License

Code: MIT License. Paper: CC BY 4.0.

## Citation

```bibtex
@article{merle2026collatz,
  author  = {Merle, Eric},
  title   = {Nonexistence of Nontrivial Cycles in the Collatz Dynamics},
  year    = {2026},
  note    = {Lean 4 formalization: https://github.com/ericmerle3789/collatz-cycles-lean}
}
```
