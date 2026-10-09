import SchubertForwardStability.LimitTheorems.CentralLimit.Taylor
import SchubertForwardStability.LimitTheorems.ForMathlib.ProductBounds
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # Finite-row Gaussian comparison from remainder bounds

## Main results

* `norm_charFun_prod_of_error_le`: pointwise quadratic remainders control a normalized row.

## Implementation notes

The factors are compared within the complex unit ball. No moment above order two is used.
-/

open MeasureTheory Complex

namespace LimitTheorems

/-- A normalized row of probability laws is close to the standard Gaussian function
when its individual quadratic characteristic-function remainders are small. -/
theorem norm_charFun_prod_of_error_le {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (B : ι → ℝ) (t : ℝ)
    (hsecond : (∑ i, ∫ x, x ^ 2 ∂μ i) = 1)
    (herror : ∀ i, ‖charFun (μ i) t -
      (1 - (t : ℂ) ^ 2 * (∫ x, x ^ 2 ∂μ i) / 2)‖ ≤ B i) :
    ‖(∏ i, charFun (μ i) t) - exp (-((t ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      (∑ i, B i) + t ^ 4 / 4 * (∑ i, (∫ x, x ^ 2 ∂μ i) ^ 2) := by
  classical
  let a (i : ι) : ℝ := t ^ 2 * (∫ x, x ^ 2 ∂μ i) / 2
  let g (i : ι) : ℂ := exp (-(a i : ℂ))
  have ha (i : ι) : 0 ≤ a i := div_nonneg
    (mul_nonneg (sq_nonneg t) (integral_nonneg (fun _ ↦ sq_nonneg _))) (by norm_num)
  have hcast (i : ι) : (a i : ℂ) = (t : ℂ) ^ 2 * (∫ x, x ^ 2 ∂μ i) / 2 := by
    dsimp only [a]
    norm_cast
  have hg (i : ι) : ‖g i‖ ≤ 1 := by
    rw [show g i = exp (-(a i : ℂ)) from rfl, norm_exp]
    simp only [neg_re, ofReal_re]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (ha i))
  have hfactor (i : ι) : ‖charFun (μ i) t - g i‖ ≤
      B i + t ^ 4 / 4 * (∫ x, x ^ 2 ∂μ i) ^ 2 := by
    have hfirst : ‖charFun (μ i) t - (1 - (a i : ℂ))‖ ≤ B i := by
      rw [hcast]
      exact herror i
    have hlast : ‖(1 - (a i : ℂ)) - g i‖ ≤ (a i) ^ 2 := by
      rw [norm_sub_rev]
      exact norm_exp_neg_remainder_le (ha i)
    calc
      _ = ‖(charFun (μ i) t - (1 - (a i : ℂ))) + ((1 - (a i : ℂ)) - g i)‖ := by
        congr 1
        ring
      _ ≤ ‖charFun (μ i) t - (1 - (a i : ℂ))‖ + ‖(1 - (a i : ℂ)) - g i‖ :=
        norm_add_le _ _
      _ ≤ B i + (a i) ^ 2 := add_le_add hfirst hlast
      _ = _ := by dsimp only [a]; ring
  have hsum : (∑ i, a i) = t ^ 2 / 2 := by
    dsimp only [a]
    rw [← Finset.sum_div, ← Finset.mul_sum, hsecond, mul_one]
  have hprod : (∏ i, g i) = exp (-((t ^ 2 / 2 : ℝ) : ℂ)) := by
    rw [show (∏ i, g i) = ∏ i, exp (-(a i : ℂ)) from rfl, ← Complex.exp_sum]
    congr 1
    simp only [← ofReal_neg, ← ofReal_sum, Finset.sum_neg_distrib, hsum]
  rw [← hprod]
  calc
    _ ≤ ∑ i, ‖charFun (μ i) t - g i‖ :=
      Finset.norm_prod_sub_prod_le_sum Finset.univ _ _
        (fun i _ ↦ norm_charFun_le_one t) (fun i _ ↦ hg i)
    _ ≤ ∑ i, (B i + t ^ 4 / 4 * (∫ x, x ^ 2 ∂μ i) ^ 2) :=
      Finset.sum_le_sum (fun i _ ↦ hfactor i)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end LimitTheorems
