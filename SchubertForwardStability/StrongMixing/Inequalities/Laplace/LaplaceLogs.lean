import SchubertForwardStability.StrongMixing.Inequalities.Laplace.PositiveLaplace
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.BoundedLaplace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Centered logarithmic Laplace decoupling

The centered exponential integral is at least one. This lower bound turns a
two-block Laplace error into an additive error for logarithms.
-/

open MeasureTheory ProbabilityTheory

namespace StrongMixing

/-- If `A > 0` and `B >= 1`, their logarithms differ above by at most `|A - B|`.
This is the scalar estimate used to pass from an additive Laplace error to a
logarithmic error for centered blocks. -/
theorem log_le_log_add_abs {A B : ℝ} (hA : 0 < A) (hB : 1 ≤ B) :
    Real.log A ≤ Real.log B + |A - B| := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hlog := Real.log_le_sub_one_of_pos (div_pos hA hBp)
  rw [Real.log_div hA.ne' hBp.ne'] at hlog
  have hid : A / B - 1 = (A - B) / B := by
    field_simp
  have hdiv : (A - B) / B ≤ |A - B| := by
    calc
      (A - B) / B ≤ |A - B| / B :=
        div_le_div_of_nonneg_right (le_abs_self _) hBp.le
      _ ≤ |A - B| := div_le_self (abs_nonneg _) hB
  rw [hid] at hlog
  linarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A centered integrable real random variable has exponential integral at least
one whenever that exponential is integrable. The assertion holds for every real
Laplace parameter, including zero and negative parameters. -/
theorem one_le_integral_exp_centered (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) (t : ℝ)
    (hE : Integrable (fun ω => Real.exp (t * f ω)) μ)
    (hmean : ∫ ω, f ω ∂μ = 0) :
    1 ≤ ∫ ω, Real.exp (t * f ω) ∂μ := by
  have hlin : Integrable (fun ω => t * f ω + 1) μ :=
    (hf.const_mul t).add (integrable_const 1)
  have hcomp := integral_mono hlin hE (fun ω => Real.add_one_le_exp (t * f ω))
  simpa [integral_add (hf.const_mul t) (integrable_const 1),
    integral_const_mul, hmean] using hcomp

/-- For two centered bounded random variables measurable in respective sigma fields,
the joint log-Laplace transform exceeds the sum of the individual transforms by at
most their strong-mixing coefficient times the uniform exponential bound. -/
theorem log_laplace_product_error_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : MeasurableSpace Ω) (hF : F ≤ mΩ) (hG : G ≤ mΩ)
    (f g : Ω → ℝ) (hf : @Measurable Ω ℝ F _ f) (hg : @Measurable Ω ℝ G _ g)
    {M N : ℝ} (hbf : ∀ ω, |f ω| ≤ M) (hbg : ∀ ω, |g ω| ≤ N)
    (hcf : ∫ ω, f ω ∂μ = 0) (hcg : ∫ ω, g ω ∂μ = 0) (t : ℝ) :
    Real.log (∫ ω, Real.exp (t * (f ω + g ω)) ∂μ) ≤
      Real.log (∫ ω, Real.exp (t * f ω) ∂μ) +
        Real.log (∫ ω, Real.exp (t * g ω) ∂μ) +
        Real.exp (|t| * (M + N)) * strongMixingCoeff (mΩ := mΩ) μ F G := by
  let : MeasurableSpace Ω := mΩ
  have hfm : Measurable f := hf.mono hF le_rfl
  have hgm : Measurable g := hg.mono hG le_rfl
  have hfi : Integrable f μ :=
    (MemLp.of_bound (p := 1) hfm.aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun ω => by simpa using hbf ω))).integrable le_rfl
  have hgi : Integrable g μ :=
    (MemLp.of_bound (p := 1) hgm.aestronglyMeasurable N
      (Filter.Eventually.of_forall (fun ω => by simpa using hbg ω))).integrable le_rfl
  have hEf := integrable_exp_of_abs_le (μ := μ) hfm.aemeasurable
    (Filter.Eventually.of_forall hbf) t
  have hEg := integrable_exp_of_abs_le (μ := μ) hgm.aemeasurable
    (Filter.Eventually.of_forall hbg) t
  have hEfg := integrable_exp_of_abs_le (μ := μ) (hfm.add hgm).aemeasurable
    (Filter.Eventually.of_forall (fun ω => (abs_add_le (f ω) (g ω)).trans
      (add_le_add (hbf ω) (hbg ω)))) t
  have hLf := one_le_integral_exp_centered μ f hfi t hEf hcf
  have hLg := one_le_integral_exp_centered μ g hgi t hEg hcg
  have hpF := integral_exp_pos hEf
  have hpG := integral_exp_pos hEg
  have hprod : 1 ≤ (∫ ω, Real.exp (t * f ω) ∂μ) *
      (∫ ω, Real.exp (t * g ω) ∂μ) := by
    simpa using mul_le_mul hLf hLg (by norm_num : (0 : ℝ) ≤ 1) hpF.le
  have hlog := log_le_log_add_abs (integral_exp_pos hEfg) hprod
  rw [Real.log_mul hpF.ne' hpG.ne'] at hlog
  exact hlog.trans (add_le_add le_rfl
    (laplace_product_error_le μ F G hF hG f g hf hg hbf hbg t))

end StrongMixing
