# collatz-cycles-lean

Companion code for: *Nonexistence of Nontrivial Cycles in the Collatz Dynamics* (Eric Merle, 2026).

## Result

N₀(d(k)) = 0 (no composition achieves corrsum ≡ 0 mod d) is established:
- For k = 3..15 by Lean 4 certified computation (0 sorry, 0 axiom)
- For k ≤ 91 by Hercher (2025), independently
- For k ≥ 18, nonsurjectivity C(S−1,k−1) < d is proved (Lean skeleton)

## Known Issue

The `lean/range-exclusion/` module contains a formula error: it computes a different
function than Steiner's corrsum. This module's results do not establish cycle nonexistence.
The correct proofs are in `lean/verified/` (k = 3..15) and `lean/skeleton/` (nonsurjectivity).
See `docs/AUDIT_CORRSUM.md` for the full analysis.

## Repository structure

```
├── paper/                      Article (md, tex, pdf)
├── lean/
│   ├── verified/               280 theorems, 0 sorry, 0 axiom (Lean 4.15) — CORRECT
│   ├── skeleton/               Junction Theorem (Lean 4.29 + Mathlib) — CORRECT
│   └── range-exclusion/        Range Exclusion — ⚠️ FORMULA ERROR (see WARNING.md)
├── scripts/                    Python verification
├── docs/
│   ├── AUDIT_CORRSUM.md        Corrsum bug analysis
│   └── PROOF_ASSEMBLY.md       Proof assembly
└── VERIFICATION.md             Article ↔ code mapping
```

## Verification

```bash
# Correct proofs (k = 3..15, Steiner formula)
cd lean/verified && lake build    # 280 theorems, 0 sorry

# Python check with correct formula
python scripts/verify_range_exclusion.py
```

## License

Code: MIT. Paper: CC BY 4.0.
