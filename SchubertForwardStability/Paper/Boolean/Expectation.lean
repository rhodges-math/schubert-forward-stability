import SchubertForwardStability.Paper.Boolean.SumExcess
import SchubertForwardStability.Paper.Boolean.Terminal
import SchubertForwardStability.Paper.Boolean.StabilityLower

/-! # Bounded error in the Boolean Schubert product expectation

For independent uniform Boolean permutations `u, v` of size `n`, the mean of `FS(u,v)`
is `n + O(1)`. The finite maximum bound, terminal mean and summable backwards excess bound
give the upper estimate, and the support-deficit bound gives the lower estimate.

## Main results

* `RecordStability.boolean_product_expectation`: the mean is `n + O(1)`.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Theorem 1.5.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory SchubertPolynomial Filter Asymptotics
open scoped Classical

/-- From size two, the Boolean product expectation has a fixed additive upper bound. -/
theorem boolean_product_expectation_upper (r : ℕ+) (hr : 2 ≤ (r : ℕ)) :
    (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (boolean (r : ℕ))) ≤
      (r : ℝ) + 2 + ∑' k, booleanBacktrackBound k := by
  have h := integral_boolean_product_le_excess r
  have hMean := (booleanMeanWalk_last_bound r hr).2
  have hSum := sum_boolean_excess_le r
  linarith

/-- The mean Boolean Schubert product forward stability is ambient size plus a bounded error. -/
theorem boolean_product_expectation :
    IsBigO atTop (fun n : ℕ =>
      (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (boolean n)) - n)
      (fun _ => (1 : ℝ)) := by
  have hSum : (0 : ℝ) ≤ ∑' k, booleanBacktrackBound k :=
    tsum_nonneg booleanBacktrackBound_nonneg
  apply IsBigO.of_bound (2 + ∑' k, booleanBacktrackBound k)
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hUpper := boolean_product_expectation_upper ⟨n, by omega⟩ (by change 2 ≤ n; omega)
  change (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (boolean n)) ≤
    (n : ℝ) + 2 + ∑' k, booleanBacktrackBound k at hUpper
  have hLower := boolean_stability_lower n
  simp only [Real.norm_eq_abs, norm_one, mul_one]
  apply abs_le.mpr
  constructor <;> linarith

end RecordStability
