import SchubertForwardStability.LimitTheorems.CentralLimit.Taylor
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.GCongr

/-! # Moment bounds for characteristic functions

## Main results

* `norm_charFun_quadratic_le`: the third absolute moment bounds the quadratic error.
* `norm_charFun_centered_le`: the corresponding estimate for centered measures.
* `norm_charFun_quad_le_integral`: an integrable pointwise remainder bound can be averaged.

## Implementation notes

Measures are probability measures on the real line. Random variables enter through
their pushforward laws. No uniform bound on the support is required.
-/

open MeasureTheory Complex

namespace LimitTheorems

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- An integrable pointwise bound on the quadratic exponential remainder also bounds
the quadratic characteristic-function remainder after integration. -/
theorem norm_charFun_quad_le_integral (hint : MemLp id 2 μ) (t : ℝ)
    {B : ℝ → ℝ} (hB : Integrable B μ)
    (hpoint : ∀ x : ℝ, ‖exp ((t : ℂ) * (x : ℂ) * I) -
      (1 + (t : ℂ) * (x : ℂ) * I - (t : ℂ) ^ 2 * (x : ℂ) ^ 2 / 2)‖ ≤ B x) :
    ‖charFun μ t - (1 + (t : ℂ) * (∫ x, x ∂μ) * I -
      (t : ℂ) ^ 2 * (∫ x, x ^ 2 ∂μ) / 2)‖ ≤
      ∫ x, B x ∂μ := by
  have hfirst : Integrable (fun x : ℝ ↦ x) μ := hint.integrable (by norm_num)
  have hsecond : Integrable (fun x : ℝ ↦ x ^ 2) μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mp hint
  let q : ℝ → ℂ := fun x ↦
    1 + (t : ℂ) * (x : ℂ) * I - (t : ℂ) ^ 2 * (x : ℂ) ^ 2 / 2
  have hlin := (hfirst.ofReal.const_mul (t : ℂ)).mul_const I
  have hsq : Integrable (fun x : ℝ ↦ (t : ℂ) ^ 2 * (x : ℂ) ^ 2 / 2) μ := by
    have hcsecond : Integrable (fun x : ℝ ↦ ((x ^ 2 : ℝ) : ℂ)) μ := hsecond.ofReal
    convert (hcsecond.const_mul ((t : ℂ) ^ 2)).div_const 2 using 1
    ext x
    norm_cast
  have hq : Integrable q μ := (integrable_const 1).add hlin |>.sub hsq
  have hsum : Integrable (fun x : ℝ ↦ (1 : ℂ) + (t : ℂ) * (x : ℂ) * I) μ :=
    (integrable_const 1).add hlin
  have he : Integrable (fun x : ℝ ↦ exp ((t : ℂ) * (x : ℂ) * I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x ↦ ?_)
    simpa only [ofReal_mul] using (norm_exp_ofReal_mul_I (t * x)).le
  have hsumIntegral : (∫ x : ℝ, (1 : ℂ) + (t : ℂ) * (x : ℂ) * I ∂μ) =
      1 + (t : ℂ) * (∫ x, x ∂μ) * I := by
    have hide : (∫ x : ℝ, (x : ℂ) ∂μ) = ((∫ x : ℝ, x ∂μ : ℝ) : ℂ) :=
      integral_complex_ofReal
    calc
      (∫ x : ℝ, (1 : ℂ) + (t : ℂ) * (x : ℂ) * I ∂μ) =
          (∫ _ : ℝ, (1 : ℂ) ∂μ) + ∫ x : ℝ, (t : ℂ) * (x : ℂ) * I ∂μ :=
        integral_add (integrable_const 1) hlin
      _ = _ := by
        simp only [integral_const, probReal_univ, one_smul, integral_mul_const,
          integral_const_mul]
        exact congrArg (fun z : ℂ ↦ 1 + (t : ℂ) * z * I) hide
  have hquadratic : (∫ x, q x ∂μ) =
      1 + (t : ℂ) * (∫ x, x ∂μ) * I -
        (t : ℂ) ^ 2 * (∫ x, x ^ 2 ∂μ) / 2 := by
    change (∫ x, (1 : ℂ) + (t : ℂ) * (x : ℂ) * I -
      (t : ℂ) ^ 2 * (x : ℂ) ^ 2 / 2 ∂μ) = _
    rw [integral_sub hsum hsq, hsumIntegral]
    simp only [integral_const_mul, integral_div, ← ofReal_pow, integral_complex_ofReal]
  rw [charFun_apply_real, ← hquadratic, ← integral_sub he hq]
  calc
    ‖∫ x, exp ((t : ℂ) * (x : ℂ) * I) - q x ∂μ‖ ≤
        ∫ x, ‖exp ((t : ℂ) * (x : ℂ) * I) - q x‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, B x ∂μ :=
      integral_mono_ae (he.sub hq).norm hB (Filter.Eventually.of_forall hpoint)

/-- The third absolute moment bounds the error of the quadratic characteristic-function
expansion, uniformly at every real argument. -/
theorem norm_charFun_quadratic_le (hint : MemLp id 3 μ) (t : ℝ) :
    ‖charFun μ t - (1 + (t : ℂ) * (∫ x, x ∂μ) * I -
      (t : ℂ) ^ 2 * (∫ x, x ^ 2 ∂μ) / 2)‖ ≤
      |t| ^ 3 / 2 * ∫ x, |x| ^ 3 ∂μ := by
  have hthird : Integrable (fun x : ℝ ↦ |x| ^ 3) μ := by
    simpa only [id_eq, Real.norm_eq_abs] using hint.integrable_norm_pow'
  have hbound := norm_charFun_quad_le_integral (hint.mono_exponent (by norm_num)) t
    (hthird.const_mul (|t| ^ 3 / 2)) (fun x ↦ ?_)
  · simpa only [integral_const_mul] using hbound
  · have hp := norm_exp_I_remainder_le (t * x)
    simp only [ofReal_mul, mul_pow, abs_mul] at hp
    convert hp using 1
    ring

/-- For a centered probability measure, the characteristic function differs from
`1 - t² E[X²]/2` by at most `|t|³ E|X|³/2`. -/
theorem norm_charFun_centered_le (hint : MemLp id 3 μ)
    (hmean : (∫ x, x ∂μ) = 0) (t : ℝ) :
    ‖charFun μ t - (1 - (t : ℂ) ^ 2 * (∫ x, x ^ 2 ∂μ) / 2)‖ ≤
      |t| ^ 3 / 2 * ∫ x, |x| ^ 3 ∂μ := by
  simpa only [hmean, ofReal_zero, mul_zero, zero_mul, add_zero] using
    norm_charFun_quadratic_le hint t

end LimitTheorems
