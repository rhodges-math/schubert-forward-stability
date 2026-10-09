import SchubertForwardStability.LimitTheorems.CentralLimit.MomentBounds
import SchubertForwardStability.LimitTheorems.CentralLimit.GaussianError

/-! # Gaussian comparison for finite independent rows

## Main results

* `norm_charFun_gaussian_le`: a characteristic function is close to the centered
  Gaussian function with the same second moment.
* `norm_charFun_prod_gaussian_le`: a normalized finite row has error controlled by
  its total third moment and the sum of its squared second moments.

## Implementation notes

The comparison is performed directly between factors of norm at most one.
The row bound does not need an upper bound on individual variances.
-/

open MeasureTheory Complex

namespace LimitTheorems

/-- For a centered law, Gaussian comparison is bounded by its third absolute moment
and the square of its second moment. -/
theorem norm_charFun_gaussian_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 3 μ) (hmean : (∫ x, x ∂μ) = 0) (t : ℝ) :
    ‖charFun μ t - exp (-((t ^ 2 * (∫ x, x ^ 2 ∂μ) / 2 : ℝ) : ℂ))‖ ≤
      |t| ^ 3 / 2 * (∫ x, |x| ^ 3 ∂μ) + t ^ 4 / 4 * (∫ x, x ^ 2 ∂μ) ^ 2 := by
  let a : ℝ := t ^ 2 * (∫ x, x ^ 2 ∂μ) / 2
  have ha : 0 ≤ a := div_nonneg
    (mul_nonneg (sq_nonneg t) (integral_nonneg (fun _ ↦ sq_nonneg _))) (by norm_num)
  have hcast : (a : ℂ) = (t : ℂ) ^ 2 * (∫ x, x ^ 2 ∂μ) / 2 := by
    dsimp only [a]
    norm_cast
  have hfirst : ‖charFun μ t - (1 - (a : ℂ))‖ ≤
      |t| ^ 3 / 2 * (∫ x, |x| ^ 3 ∂μ) := by
    rw [hcast]
    exact norm_charFun_centered_le hint hmean t
  have hsecond : ‖(1 - (a : ℂ)) - exp (-(a : ℂ))‖ ≤ a ^ 2 := by
    rw [norm_sub_rev]
    exact norm_exp_neg_remainder_le ha
  calc
    ‖charFun μ t - exp (-(a : ℂ))‖ =
        ‖(charFun μ t - (1 - (a : ℂ))) + ((1 - (a : ℂ)) - exp (-(a : ℂ)))‖ := by
      congr 1
      ring
    _ ≤ ‖charFun μ t - (1 - (a : ℂ))‖ + ‖(1 - (a : ℂ)) - exp (-(a : ℂ))‖ :=
      norm_add_le _ _
    _ ≤ |t| ^ 3 / 2 * (∫ x, |x| ^ 3 ∂μ) + a ^ 2 := add_le_add hfirst hsecond
    _ = |t| ^ 3 / 2 * (∫ x, |x| ^ 3 ∂μ) + t ^ 4 / 4 * (∫ x, x ^ 2 ∂μ) ^ 2 := by
      dsimp only [a]
      ring

/-- For a normalized finite row of centered probability laws, the characteristic-function
product differs from the standard Gaussian function by a sum of moment errors. -/
theorem norm_charFun_prod_gaussian_le {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hint : ∀ i, MemLp id 3 (μ i))
    (hmean : ∀ i, (∫ x, x ∂μ i) = 0)
    (hsecond : (∑ i, ∫ x, x ^ 2 ∂μ i) = 1) (t : ℝ) :
    ‖(∏ i, charFun (μ i) t) - exp (-((t ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      |t| ^ 3 / 2 * (∑ i, ∫ x, |x| ^ 3 ∂μ i) +
        t ^ 4 / 4 * (∑ i, (∫ x, x ^ 2 ∂μ i) ^ 2) := by
  simpa only [← Finset.mul_sum] using norm_charFun_prod_of_error_le μ
    (fun i ↦ |t| ^ 3 / 2 * (∫ x, |x| ^ 3 ∂μ i)) t hsecond
    (fun i ↦ norm_charFun_centered_le (hint i) (hmean i) t)

end LimitTheorems
