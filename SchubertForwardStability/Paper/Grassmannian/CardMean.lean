import SchubertForwardStability.LimitTheorems.Binomial.CentralBinomial
import SchubertForwardStability.Permutations.Random.SubsetMeans

/-! # Square-root asymptotic for a pair of subset cardinalities

For independent uniform random subsets `V, W` of `[1, n]`, the mean of `max(|V|, |W|)` is
`n/2 + sqrt(n)/(2*sqrt(pi)) + O(1/sqrt(n))`. The error is `sqrt(n)/(2*sqrt(pi))` times the
relative error of the Stirling estimate of the central binomial coefficient.
-/

open Filter Asymptotics MeasureTheory FinitaryPerm
open scoped Topology

namespace RecordStability

/-- The cardinality-maximum mean error is the scaled central-binomial error. -/
theorem subset_card_maximum_error (n : ℕ) :
    (∫ p, (max p.1.card p.2.card : ℝ) ∂(subsetLaw n).prod (subsetLaw n)) -
        ((n : ℝ) / 2 + Real.sqrt n / (2 * Real.sqrt Real.pi)) =
      Real.sqrt n / (2 * Real.sqrt Real.pi) *
        (((2 * n).choose n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n - 1) := by
  rw [subsetLaw_pair_card_max_mean, Real.sqrt_mul Real.pi_pos.le]
  have hp : Real.sqrt Real.pi ≠ 0 := (by positivity : 0 < Real.sqrt Real.pi).ne'
  field_simp [hp]
  ring_nf
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

/-- The mean error is bounded by an explicit reciprocal-square-root multiple. -/
theorem subset_card_maximum_error_le (n : ℕ) (hn : 0 < n) :
    |(∫ p, (max p.1.card p.2.card : ℝ) ∂(subsetLaw n).prod (subsetLaw n)) -
        ((n : ℝ) / 2 + Real.sqrt n / (2 * Real.sqrt Real.pi))| ≤
      (1 / (2 * Real.sqrt Real.pi)) * (Real.sqrt n)⁻¹ := by
  rw [subset_card_maximum_error, abs_mul, abs_of_nonneg (by positivity)]
  calc
    _ ≤ Real.sqrt n / (2 * Real.sqrt Real.pi) * (n : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (LimitTheorems.centralBinomial_error_le n hn)
        (by positivity)
    _ = _ := by
      have hnp : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnp).ne'
      have hp : Real.sqrt Real.pi ≠ 0 := (by positivity : 0 < Real.sqrt Real.pi).ne'
      field_simp [hs, hp, hnp.ne']
      exact Real.sq_sqrt hnp.le

/-- The maximum of two independent subset sizes has the square-root mean with its rate. -/
theorem grassmannian_card_maximum_mean :
    (fun n : ℕ =>
      (∫ p, (max p.1.card p.2.card : ℝ) ∂(subsetLaw n).prod (subsetLaw n)) -
        ((n : ℝ) / 2 + Real.sqrt n / (2 * Real.sqrt Real.pi))) =O[atTop]
          (fun n : ℕ => (Real.sqrt n)⁻¹) := by
  apply IsBigO.of_bound (1 / (2 * Real.sqrt Real.pi))
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  exact subset_card_maximum_error_le n (by omega)

end RecordStability
