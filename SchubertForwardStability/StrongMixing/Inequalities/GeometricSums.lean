import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum

/-!
# Finite reversed geometric tails

The finite covariance tail indexed by distance from the last coordinate is bounded
by the convergent positive geometric series, with its exact scalar sum explicit.
-/

open scoped BigOperators

namespace StrongMixing

/-- For `0 <= r < 1`, the reversed finite sum of positive-distance powers
`sum (r ^ (n - k))` for `k < n` is at most `r / (1 - r)`.
The empty-sum and zero-ratio boundaries are included. -/
theorem geometric_reverse_sum_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, r ^ (n - k)) ≤ r / (1 - r) := by
  have hs := (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum (Finset.range n)
    (fun k _ => pow_nonneg hr0 k)
  rw [tsum_geometric_of_lt_one hr0 hr1] at hs
  have hrev : (∑ k ∈ Finset.range n, r ^ (n - k)) =
      ∑ k ∈ Finset.range n, r ^ (k + 1) := by
    rw [← Finset.sum_range_reflect (fun k => r ^ (n - k)) n]
    apply Finset.sum_congr rfl
    intro k hk
    have hid : n - (n - 1 - k) = k + 1 := by
      have hkn := Finset.mem_range.mp hk
      omega
    rw [hid]
  rw [hrev]
  simp_rw [pow_succ']
  rw [← Finset.mul_sum]
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hs hr0

end StrongMixing
