# ⚠️ Known Issue: corrSum Formula

The `corrSum` function in this module uses gap values directly as exponents of 2:

    corrSum(A, k) = Σ 3^{k-1-i} · 2^{A[i]}

where A comes from `enumMonotone` (non-decreasing partitions summing to S).

This is NOT the correct Steiner formula, which uses cumulative positions:

    corrSum_Steiner(k, A) = Σ 3^{k-1-i} · 2^{A_i}

where A = (0 < A_1 < ... < A_{k-1} < S) are strictly increasing positions.

The correct formula is implemented in `lean/verified/CollatzVerified/Basic.lean`
(`corrSumList` with `compList`), which covers k = 3..15 with 0 sorry and 0 axiom.

The `checkRE` results in this module do not establish N₀(d) = 0 for the true
Steiner corrsum. See `docs/AUDIT_CORRSUM.md` for the full analysis.
