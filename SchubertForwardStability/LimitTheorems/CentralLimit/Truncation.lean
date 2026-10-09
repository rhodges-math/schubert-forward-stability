import SchubertForwardStability.LimitTheorems.CentralLimit.MomentBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

/-! # Second-moment truncation estimates

## Main results

* `tailSecond`: the second moment restricted to values of absolute size greater than a threshold.
* `second_moment_le_tail`: small values contribute at most the squared threshold.
* `norm_charFun_truncated_le`: a quadratic characteristic-function error split at a threshold.

## Implementation notes

The tail is represented by a measurable indicator. Only square integrability is needed.
-/

open MeasureTheory ProbabilityTheory Complex Set

namespace LimitTheorems

/-- The second moment in the strict tail `ε < |x|` of a real measure. -/
noncomputable def tailSecond (μ : Measure ℝ) (ε : ℝ) : ℝ :=
  ∫ x, {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) x ∂μ

/-- Tail second moments are nonnegative, even when the full second moment is not integrable. -/
theorem tailSecond_nonneg (μ : Measure ℝ) (ε : ℝ) : 0 ≤ tailSecond μ ε := by
  exact integral_nonneg (fun x ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) x)

/-- For a square-integrable probability law, the second moment is bounded by the squared
threshold plus its tail second moment. -/
theorem second_moment_le_tail {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ x, x ^ 2 ∂μ) ≤ ε ^ 2 + tailSecond μ ε := by
  have hsecond : Integrable (fun x : ℝ ↦ x ^ 2) μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mp hint
  have hset : MeasurableSet {x : ℝ | ε < |x|} := by measurability
  have htail := hsecond.indicator hset
  have hpoint (x : ℝ) : x ^ 2 ≤ ε ^ 2 +
      {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) x := by
    by_cases hx : ε < |x|
    · rw [indicator_of_mem (show x ∈ {x : ℝ | ε < |x|} from hx)]
      nlinarith [sq_nonneg ε]
    · rw [indicator_of_notMem (show x ∉ {x : ℝ | ε < |x|} from hx), add_zero]
      have habs := abs_nonneg x
      have hle := le_of_not_gt hx
      nlinarith [sq_abs x]
  have hb := integral_mono_ae hsecond ((integrable_const (ε ^ 2)).add htail)
    (Filter.Eventually.of_forall hpoint)
  simpa only [integral_add' (integrable_const (ε ^ 2)) htail, integral_const,
    probReal_univ, one_smul, tailSecond] using hb

/-- Splitting at `ε` bounds a centered characteristic-function remainder by a small
multiple of the second moment and a constant multiple of the tail second moment. -/
theorem norm_charFun_truncated_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hmean : (∫ x, x ∂μ) = 0) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    ‖charFun μ t - (1 - (t : ℂ) ^ 2 * (∫ x, x ^ 2 ∂μ) / 2)‖ ≤
      |t| ^ 3 / 2 * ε * (∫ x, x ^ 2 ∂μ) + 3 * t ^ 2 / 2 * tailSecond μ ε := by
  have hsecond : Integrable (fun x : ℝ ↦ x ^ 2) μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mp hint
  have hset : MeasurableSet {x : ℝ | ε < |x|} := by measurability
  let r : ℝ → ℝ := {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2)
  have hr : Integrable r μ := hsecond.indicator hset
  let B : ℝ → ℝ := fun x ↦ |t| ^ 3 / 2 * ε * x ^ 2 + 3 * t ^ 2 / 2 * r x
  have hB : Integrable B μ :=
    (hsecond.const_mul (|t| ^ 3 / 2 * ε)).add (hr.const_mul (3 * t ^ 2 / 2))
  have hpoint (x : ℝ) : ‖exp ((t : ℂ) * (x : ℂ) * I) -
      (1 + (t : ℂ) * (x : ℂ) * I - (t : ℂ) ^ 2 * (x : ℂ) ^ 2 / 2)‖ ≤ B x := by
    by_cases hx : ε < |x|
    · have hp := norm_exp_I_second_le (t * x)
      simp only [ofReal_mul, mul_pow] at hp
      have heq : 3 * (t ^ 2 * x ^ 2) / 2 = 3 * t ^ 2 / 2 * x ^ 2 := by ring
      rw [heq] at hp
      dsimp [B, r]
      rw [indicator_of_mem (show x ∈ {x : ℝ | ε < |x|} from hx)]
      exact hp.trans (le_add_of_nonneg_left
        (mul_nonneg (mul_nonneg (by positivity) hε) (sq_nonneg x)))
    · have hp := norm_exp_I_remainder_le (t * x)
      simp only [ofReal_mul, mul_pow, abs_mul] at hp
      have heq : |t| ^ 3 * |x| ^ 3 / 2 = |t| ^ 3 / 2 * |x| ^ 3 := by ring
      rw [heq] at hp
      have hcube : |x| ^ 3 ≤ ε * x ^ 2 := by
        have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hx) (sq_nonneg x)
        calc
          |x| ^ 3 = |x| * x ^ 2 := by rw [← sq_abs x]; ring
          _ ≤ ε * x ^ 2 := hm
      dsimp [B, r]
      rw [indicator_of_notMem (show x ∉ {x : ℝ | ε < |x|} from hx), mul_zero, add_zero]
      convert hp.trans (mul_le_mul_of_nonneg_left hcube (by positivity)) using 1
      ring
  have hb := norm_charFun_quad_le_integral hint t hB hpoint
  simp only [hmean, ofReal_zero, mul_zero, zero_mul, add_zero] at hb
  simpa only [B, integral_add (hsecond.const_mul (|t| ^ 3 / 2 * ε))
    (hr.const_mul (3 * t ^ 2 / 2)), integral_const_mul, r, tailSecond] using hb

end LimitTheorems
