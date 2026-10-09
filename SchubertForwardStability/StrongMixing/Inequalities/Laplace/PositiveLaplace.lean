import SchubertForwardStability.StrongMixing.Inequalities.BoundedCovariance

/-! # Positive covariance and two-block Laplace estimates

For nonnegative bounded variables, normalization needs no affine shift and the
covariance factor is one. Applying this estimate to exponentials controls the error
in replacing a two-block Laplace transform by a product.
-/

open MeasureTheory ProbabilityTheory

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Nonnegative variables bounded by positive constants have covariance bounded
by the product of these bounds and the strong-mixing coefficient, with factor one. -/
theorem nonnegative_covariance_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : MeasurableSpace Ω) (hF : F ≤ mΩ) (hG : G ≤ mΩ)
    (f g : Ω → ℝ) (hf : @Measurable Ω ℝ F inferInstance f)
    (hg : @Measurable Ω ℝ G inferInstance g) {M N : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfM : ∀ ω, f ω ≤ M) (hgN : ∀ ω, g ω ≤ N) :
    |(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ| ≤
      M * N * strongMixingCoeff (mΩ := mΩ) μ F G := by
  have hf2 : MemLp f 2 μ := MemLp.of_bound (hf.mono hF le_rfl).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun ω ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)] using hfM ω)
  have hg2 : MemLp g 2 μ := MemLp.of_bound (hg.mono hG le_rfl).aestronglyMeasurable N
    (Filter.Eventually.of_forall fun ω ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 ω)] using hgN ω)
  let u : Ω → ℝ := fun ω ↦ f ω / M
  let v : Ω → ℝ := fun ω ↦ g ω / N
  have hu : @Measurable Ω ℝ F inferInstance u := hf.div_const M
  have hv : @Measurable Ω ℝ G inferInstance v := hg.div_const N
  have hu0 : ∀ ω, 0 ≤ u ω := fun ω ↦ div_nonneg (hf0 ω) hM.le
  have hv0 : ∀ ω, 0 ≤ v ω := fun ω ↦ div_nonneg (hg0 ω) hN.le
  have hu1 : ∀ ω, u ω ≤ 1 := fun ω ↦ (div_le_one hM).mpr (hfM ω)
  have hv1 : ∀ ω, v ω ≤ 1 := fun ω ↦ (div_le_one hN).mpr (hgN ω)
  have hu2 : MemLp u 2 μ := MemLp.of_bound (hu.mono hF le_rfl).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hu0 ω)] using hu1 ω)
  have hv2 : MemLp v 2 μ := MemLp.of_bound (hv.mono hG le_rfl).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hv0 ω)] using hv1 ω)
  have hb := unit_covariance_le (mΩ := mΩ) μ F G hF hG u v hu hv hu0 hu1 hv0 hv1
  have he : covariance u v μ = covariance f g μ / (M * N) := by
    dsimp [u, v]
    rw [covariance_fun_div_left, covariance_fun_div_right]
    simp only [div_div, mul_comm]
  have huv := covariance_eq_sub hu2 hv2
  change covariance u v μ =
    (∫ ω, u ω * v ω ∂μ) - (∫ ω, u ω ∂μ) * ∫ ω, v ω ∂μ at huv
  rw [← huv, he, abs_div, abs_of_pos (mul_pos hM hN)] at hb
  have hout := (div_le_iff₀ (mul_pos hM hN)).mp hb
  have hfg := covariance_eq_sub hf2 hg2
  change covariance f g μ =
    (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ at hfg
  rw [← hfg]
  simpa only [mul_comm] using hout

/-- The difference between a joint two-variable Laplace transform and the product
of the separate transforms is controlled by the event coefficient and the exponential
of the sum of the two uniform bounds. The Laplace parameter may have either sign. -/
theorem laplace_product_error_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : MeasurableSpace Ω) (hF : F ≤ mΩ) (hG : G ≤ mΩ)
    (f g : Ω → ℝ) (hf : @Measurable Ω ℝ F inferInstance f)
    (hg : @Measurable Ω ℝ G inferInstance g) {M N : ℝ}
    (hfM : ∀ ω, |f ω| ≤ M) (hgN : ∀ ω, |g ω| ≤ N) (t : ℝ) :
    |(∫ ω, Real.exp (t * (f ω + g ω)) ∂μ) -
      (∫ ω, Real.exp (t * f ω) ∂μ) * ∫ ω, Real.exp (t * g ω) ∂μ| ≤
      Real.exp (|t| * (M + N)) * strongMixingCoeff (mΩ := mΩ) μ F G := by
  have hfb (ω : Ω) : Real.exp (t * f ω) ≤ Real.exp (|t| * M) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |t * f ω| := le_abs_self _
      _ = |t| * |f ω| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hfM ω) (abs_nonneg _)
  have hgb (ω : Ω) : Real.exp (t * g ω) ≤ Real.exp (|t| * N) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |t * g ω| := le_abs_self _
      _ = |t| * |g ω| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgN ω) (abs_nonneg _)
  have hb := nonnegative_covariance_le (mΩ := mΩ) μ F G hF hG
    (fun ω ↦ Real.exp (t * f ω)) (fun ω ↦ Real.exp (t * g ω))
    (hf.const_mul t).exp (hg.const_mul t).exp
    (Real.exp_pos _) (Real.exp_pos _) (fun _ ↦ (Real.exp_pos _).le)
    (fun _ ↦ (Real.exp_pos _).le) hfb hgb
  simpa only [mul_add, Real.exp_add] using hb

end StrongMixing
