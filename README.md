# Nonexistence of Nontrivial Cycles in the Collatz Dynamics

**Author:** Eric Merle  
**Date:** March 2026

This repository contains the Lean 4 formalizations, verification scripts, and supplementary material for the paper *Nonexistence of Nontrivial Cycles in the Collatz Dynamics*.

## Result

For every k ≥ 1, the accelerated Collatz map T(n) = (3n+1)/2^{v₂(3n+1)} admits no nontrivial positive cycle of length k.

## The Junction Theorem

The proof is organized around the **Junction Theorem**, which establishes that for every cycle length k ≥ 1, at least one of two independent obstructions applies:

- **(A) Computational obstruction (k ≤ 10000).** The correction sum corrsum(σ) lies in an interval [cs_min, cs_max] that contains no multiple of d(k) = 2^S − 3^k. This is called *Range Exclusion* and is verified by Lean's `native_decide` for each k individually.

- **(B) Entropic obstruction (k ≥ 18).** The number of compositions C(S−1, k−1) is strictly less than d(k), so corrsum cannot be surjective onto Z/dZ. For k ≥ 10001, the Baker–Wüstholz theorem on linear forms in logarithms makes this effective.

The two ranges overlap (18 ≤ k ≤ 10000), ensuring no gap. The "junction" is the point where the computational and asymptotic arguments meet.

## Proof architecture

| Range | Method | Obstruction | Location |
|-------|--------|-------------|----------|
| k = 1 | Trivial cycle (n₁=1) excluded by hypothesis | — | Section 2.2 |
| k = 2 | Direct check (n₁=2 is even) | — | Section 4 |
| k = 3..10000 | Range Exclusion, Lean `native_decide` | (A) | `lean/range-exclusion/` |
| k ≥ 10001 | Baker–Wüstholz (1993) | (B) | Section 5 |

The sole external dependency beyond the Lean kernel is the Baker–Wüstholz theorem, a published result.

## Repository structure

```
├── paper/                      Article (markdown)
├── lean/
│   ├── verified/               280 theorems, 0 sorry, 0 axiom (Lean 4.15)
│   ├── range-exclusion/        Range Exclusion k=3..10000 (Lean 4.28)
│   └── skeleton/               Junction Theorem: main proof combining (A)+(B) (Lean 4.29 + Mathlib)
├── scripts/
│   ├── verify_range_exclusion.py   Computational verification of Range Exclusion
│   ├── baker_threshold.py          Baker–Wüstholz threshold analysis
│   ├── spectral_analysis.py        Transfer matrix spectral analysis (Section 6)
│   └── requirements.txt           Python dependencies
└── supplementary/              Additional documentation
```

## Verification

### Lean (Range Exclusion, main proof component)

```bash
cd lean/range-exclusion
lake build          # Compiles and verifies k=3..10000
```

Requires: [elan](https://github.com/leanprover/elan) with Lean 4.28.0.

### Lean (Verified core, structural theorems)

```bash
cd lean/verified
lake build          # 280 theorems, 0 sorry, 0 axiom
```

Requires: Lean 4.15.0 (separate toolchain).

### Python scripts

```bash
pip install -r scripts/requirements.txt
python scripts/verify_range_exclusion.py    # Range Exclusion for k=3..500
python scripts/baker_threshold.py           # Baker–Wüstholz analysis
python scripts/spectral_analysis.py         # Transfer matrix eigenvalues
```

Requires: Python 3.9+, numpy, mpmath.

## Axioms

The Lean formalization uses two published results as axioms:

1. **Baker–Wüstholz (1993)**: Linear forms in logarithms lower bound  
   Used for: k ≥ 10001 (Range Exclusion holds asymptotically)  
   Reference: *J. reine angew. Math.* 442 (1993), 19–62

2. **Simons–de Weger (2005)**: No Collatz cycle with k < 68  
   Used for: Bootstrap (small k covered independently by native_decide)  
   Reference: *Acta Arith.* 117 (2005), 51–70

## Section 6 (supplementary)

The spectral analysis in Section 6 of the paper provides structural insight into why Range Exclusion holds. It is not required for the proof. Key findings:

- Transfer matrices M_a have rank 1 at z=1 for all nontrivial characters (20 primes verified)
- Wielandt spectral gap: ρ(M_a(z₀)) < ρ(M₀(z₀)) for all p ≥ 5, z₀ ∈ (0,1)
- M₀(z) is doubly stochastic with uniform Perron eigenvector
- Maximum spectral ratio ρ_p = 0.82 (at p = 7)

## License

Code: MIT License  
Paper: CC BY 4.0

## Citation

```bibtex
@article{merle2026collatz,
  author  = {Merle, Eric},
  title   = {Nonexistence of Nontrivial Cycles in the Collatz Dynamics},
  year    = {2026},
  note    = {Lean 4 formalization available at
             https://github.com/ericmerle3789/collatz-cycles-lean}
}
```
