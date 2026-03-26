# collatz-cycles-lean

Companion code for: *Nonexistence of Nontrivial Cycles in the Collatz Dynamics* (Eric Merle, 2026).

## Contents

**`paper/`** — Article in markdown, LaTeX, and PDF.

**`lean/range-exclusion/`** — Lean 4.28 proof that N₀(d(k)) = 0 for k = 3 to 10000, by `native_decide`. Two published axioms (Baker–Wüstholz 1993, Simons–de Weger 2005). Compile with `lake build`.

**`lean/verified/`** — 280 structural theorems (Lean 4.15). 0 sorry, 0 axiom. Covers Steiner's equation, nonsurjectivity, CRT, zero-exclusion for k = 3..15, transfer matrix properties. Compile with `lake build`.

**`lean/skeleton/`** — Junction Theorem formalization (Lean 4.29 + Mathlib). Combines Simons–de Weger (k < 68) with the entropic nonsurjectivity bound (k ≥ 18). The asymptotic argument for k ≥ 666 is in `AsymptoticBound.lean`.

**`scripts/`** — Python verification of the Baker–Wüstholz threshold, Range Exclusion, and the spectral analysis of Section 6.

**`docs/`** — Proof assembly document and Lean theorem inventory.

See **[VERIFICATION.md](VERIFICATION.md)** for a section-by-section mapping between the article and the code.

## Quick start

```bash
# Verify the main proof (Range Exclusion, k = 3..10000)
cd lean/range-exclusion && lake build

# Verify structural theorems (280 theorems, 0 sorry)
cd lean/verified && lake build

# Run supplementary Python checks
pip install numpy mpmath
python scripts/verify_range_exclusion.py
python scripts/spectral_analysis.py
```

## License

Code: MIT. Paper: CC BY 4.0.
