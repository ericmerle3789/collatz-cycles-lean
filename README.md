> ## ⚠️ Erratum — 2026-10-02
>
> **This repository does not prove that the Collatz map has no nontrivial cycle.** The former repository
> description, the title of the paper in `paper/`, and parts of the text below said or implied otherwise.
>
> **What is actually checked here.** Notation: S = ⌈k·log₂3⌉, d = 2^S − 3^k,
> corrSum(A) = Σ 3^(k−1−i)·2^(A_i) over positions 0 = A_0 < A_1 < … < A_(k−1) < S (Steiner).
> 1. `lean/verified/` (Lean 4.15.0, no Mathlib, 280 theorems, 0 `sorry`, no `axiom` declaration): for
>    k = 3..15, no A gives corrSum(A) ≡ 0 (mod d). Limits: these facts are proved by `native_decide`, which
>    trusts the compiler (axiom `Lean.ofReduceBool`), so "0 axiom" and "certified by the kernel" are not
>    accurate; only S = ⌈k·log₂3⌉ is checked, and the step "hence no k-cycle" is not formalized in this module;
>    Lean 4.15.0 predates the fix of the kernel soundness bug lean4#14576 (v4.32.2, 2026-07-28) and was not
>    re-checked.
> 2. `lean/skeleton/`, `crystal_nonsurjectivity`: C(S−1, k−1) < d for k ≥ 18, conditional on the axiom
>    `small_gap_crystal_bound` (stated for all k ≥ 666, justified only by an unformalized continued-fraction
>    argument and a numerical check). Non-surjectivity says that some residue is missed, not that 0 is; by
>    itself it excludes no cycle. As committed, `lean/skeleton/lakefile.lean` points to a missing `skeleton/`
>    subfolder, so this module does not build as is.
> 3. External: Christian Hercher, *There are no Collatz m-Cycles with m ≤ 91*, J. Integer Seq. 26 (2023),
>    Article 23.3.5. Since a cycle with k odd terms has m ≤ k, no cycle has k ≤ 91.
>
> **Withdrawn.**
> - `lean/skeleton/JunctionTheorem.lean`, axiom `simons_de_weger` (l. 551): **false as written** — the
>   trivial cycle (k = 1, S = 2, n₀ = 1, A = 0, so that 1·(2² − 3) = 1 = corrSum) satisfies the statement it
>   negates. `junction_unconditional` and `no_positive_cycle` use it and therefore establish nothing
>   (`no_positive_cycle` also assumes `QuasiUniformity`, which states its conclusion). The word "CORRECT" for
>   `lean/skeleton/` below refers to the corrSum formula only.
> - `scripts/verify_range_exclusion.py` and `scripts/baker_threshold.py` use the same wrong (monotone) object
>   as `lean/range-exclusion/`; they are not a check "with the correct formula".
> - `paper/` (md, tex, pdf — the PDF is an older version): the title; "This paper proves (ii)"; the Range
>   Exclusion and Baker sections (§3–5, k ≤ 10000 and k ≥ 10001); §7.1; the row "No cycle (all k)" of §7.4;
>   every sentence saying `native_decide` runs "within the trusted Lean kernel"; the sentence attributing
>   "k ≤ 10⁸" to Simons–de Weger. Reference [7] is Christian Hercher, J. Integer Seq. 26 (2023),
>   Article 23.3.5.
> - `docs/PROOF_ASSEMBLY.md` (retracted 2026-07-29): its notice still says that Path B (FCQ) establishes the
>   result for k = 3..200. This is withdrawn too — see the correction added to that file on 2026-10-02.
> - The 2026-04-22 notice below says `collatz-nocycle-lean4` has "no known formula errors" and a central
>   theorem depending only on the three standard axioms. Its hypotheses are explicit parameters, and one of
>   them (`DerivedLargeKBound`) already amounts, with Barina's verification, to its conclusion for k > 1322;
>   see that repository's README erratum.
> - "No further commits" below: three retraction commits were added on 2026-07-29.
>
> — Eric Merle, 2026-10-02

> **⚠️ Repository frozen 2026-04-22 (not archived on GitHub) — historical reference only.**
>
> **Active repo** : [collatz-nocycle-lean4](https://github.com/ericmerle3789/collatz-nocycle-lean4)
>
> ## ⚠️ Known formula error — do NOT cite the `lean/range-exclusion/` module
>
> The `lean/range-exclusion/` directory of this repository contains a Lean module with a **documented formula error** : the function computed in that module differs from Steiner's `corrSum`, so any result proven in `range-exclusion/` does NOT establish cycle non-existence. See `docs/AUDIT_CORRSUM.md` in this repo for the full diagnostic.
>
> **Rule for readers and reviewers** :
> - ❌ Do NOT copy, cite, or re-use any theorem from `lean/range-exclusion/`.
> - ❌ Do NOT treat the `range-exclusion/` results as valid Collatz cycle non-existence proofs.
> - ✅ The correct results of this archived repo are in `lean/verified/` (k = 3..15, 280 theorems, 0 sorry, 0 axiom, Lean 4.15) and `lean/skeleton/` (nonsurjectivity only; see the erratum above).
> - ✅ For current and publication-target work, consult [collatz-nocycle-lean4](https://github.com/ericmerle3789/collatz-nocycle-lean4).
>
> ## Relationship to the active repo
>
> `collatz-nocycle-lean4` supersedes this companion repo with :
> - A single consolidated Lean tree (36 files, 393 theorems, 0 sorry).
> - No known formula errors.
> - Central theorem `no_nontrivial_cycle_phase59` depends on `propext, Classical.choice, Quot.sound` only — verified via `#print axioms` on 2026-04-22.
>
> ## Maintenance
>
> No further commits. Issues → [active repo issue tracker](https://github.com/ericmerle3789/collatz-nocycle-lean4/issues).
>
> — Eric Merle, 2026-04-22

---

# collatz-cycles-lean

Companion code for: *Nonexistence of Nontrivial Cycles in the Collatz Dynamics* (Eric Merle, 2026).

## Result

N₀(d(k)) = 0 (no composition achieves corrsum ≡ 0 mod d) is established:
- For k = 3..15 by Lean 4 certified computation (0 sorry, 0 axiom)
- For k ≤ 91 by Hercher (2023, J. Integer Seq. 26, Art. 23.3.5), externally

Separately, C(S−1,k−1) < d for k ≥ 18 (Lean skeleton, conditional on the axiom `small_gap_crystal_bound`); this does not give N₀ = 0.

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
│   ├── skeleton/               Junction Theorem (Lean 4.29 + Mathlib) — corrSum formula correct; contains a false axiom (see erratum)
│   └── range-exclusion/        Range Exclusion — ⚠️ FORMULA ERROR (see WARNING.md)
├── scripts/                    Python verification
├── docs/
│   ├── AUDIT_CORRSUM.md        Corrsum bug analysis
│   └── PROOF_ASSEMBLY.md       Proof assembly — RETRACTED (2026-07-29)
└── VERIFICATION.md             Article ↔ code mapping
```

## Verification

```bash
# Correct proofs (k = 3..15, Steiner formula)
cd lean/verified && lake build    # 280 theorems, 0 sorry

# Python script for the (invalid) Range Exclusion — wrong formula, kept for the record
python scripts/verify_range_exclusion.py
```

## License

Code: MIT. Paper: CC BY 4.0.
