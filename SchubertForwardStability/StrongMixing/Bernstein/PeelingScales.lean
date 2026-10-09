import SchubertForwardStability.StrongMixing.Bernstein.RetainedBernstein
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Geometric variance scales for finite peeling

The retained row at stage `j` is assigned a positive standard-deviation upper
scale proportional to `sqrt(n)*sqrt(retainedVariance(c))*sqrt(1/2)^j`. Its square
matches the decay of the cardinalities, and its finite sum has a uniform bound.
-/

open scoped BigOperators

namespace StrongMixing

/-- The positive standard-deviation scale assigned to retained peeling stage
`j` is `M*sqrt(n)*sqrt(retainedVariance(c))*sqrt(1/2)^j`. -/
noncomputable def peelingScale (c M : ℝ) (n j : ℕ) : ℝ :=
  M * Real.sqrt n * Real.sqrt (retainedVariance c) * Real.sqrt (1 / 2) ^ j

/-- The geometric scale ratio `sqrt(1/2)` lies strictly between zero and one. -/
theorem peeling_ratio_bounds : 0 < Real.sqrt (1 / 2 : ℝ) ∧ Real.sqrt (1 / 2 : ℝ) < 1 := by
  constructor
  · exact Real.sqrt_pos.mpr (by norm_num)
  · exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by norm_num)

/-- Every retained peeling scale is strictly positive when `M,c,n` are positive,
even if its selected finite coordinate set happens to be empty. -/
theorem peelingScale_pos {c M : ℝ} (hc : 0 < c) (hM : 0 < M) {n : ℕ}
    (hn : 0 < n) (j : ℕ) : 0 < peelingScale c M n j := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hq := Real.sqrt_pos.mpr (retainedVariance_pos hc)
  have hr := peeling_ratio_bounds.1
  unfold peelingScale
  positivity

/-- The square of the retained stage scale is exactly
`M^2*n*retainedVariance(c)/2^j`. -/
theorem peelingScale_sq {c M : ℝ} (hc : 0 < c) (n j : ℕ) :
    peelingScale c M n j ^ 2 = M ^ 2 * n * retainedVariance c / (2 : ℝ) ^ j := by
  unfold peelingScale
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n),
    Real.sq_sqrt (retainedVariance_pos hc).le]
  rw [← pow_mul, Nat.mul_comm j 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [div_pow, one_pow]
  ring

/-- The sum of all retained stage scales before any finite cutoff `J` is bounded
by `M*sqrt(n)*sqrt(retainedVariance(c))/(1-sqrt(1/2))`, independently of `J`. -/
theorem peelingScale_sum_le {c M : ℝ} (hM : 0 ≤ M) (n J : ℕ) :
    (∑ j ∈ Finset.range J, peelingScale c M n j) ≤
      M * Real.sqrt n * Real.sqrt (retainedVariance c) / (1 - Real.sqrt (1 / 2)) := by
  have hr := peeling_ratio_bounds
  have hg : (∑ j ∈ Finset.range J, Real.sqrt (1 / 2 : ℝ) ^ j) ≤
      1 / (1 - Real.sqrt (1 / 2)) := by
    simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hr.1.le hr.2)
  have hs : 0 ≤ M * Real.sqrt n * Real.sqrt (retainedVariance c) := by positivity
  unfold peelingScale
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left hg hs
  simpa only [mul_one_div] using h

end StrongMixing
