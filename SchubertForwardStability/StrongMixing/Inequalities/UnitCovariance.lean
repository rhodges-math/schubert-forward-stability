import SchubertForwardStability.StrongMixing.Coefficients.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity

/-! # Bounded covariance from event discrepancies

Threshold integration extends the event bound defining the strong-mixing coefficient
to bounded measurable functions. It is used for independent-row tensorization and
separated-block Laplace estimates.
-/

open MeasureTheory Set

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A unit-interval-valued variable times a bounded variable is the integral of its
threshold-weighted indicators; this equality follows directly from Fubini. -/
theorem integral_mul_unit_layers (μ : Measure Ω) [IsFiniteMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ ω, 0 ≤ f ω) (hf1 : ∀ ω, f ω ≤ 1)
    {M : ℝ} (hM : 0 ≤ M) (hgM : ∀ ω, |g ω| ≤ M) :
    ∫ ω, f ω * g ω ∂μ =
      ∫ t in Ioc (0 : ℝ) 1, ∫ ω, if t ≤ f ω then g ω else 0 ∂μ := by
  classical
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  let H : ℝ × Ω → ℝ := fun p ↦ if p.1 ≤ f p.2 then g p.2 else 0
  have hm : Measurable H :=
    Measurable.ite (measurableSet_le measurable_fst (hf.comp measurable_snd))
      (hg.comp measurable_snd) measurable_const
  have hb : Integrable H (ν.prod μ) :=
    (integrable_const M).mono' hm.aestronglyMeasurable (by
      filter_upwards [] with p
      dsimp [H]
      split_ifs
      · exact hgM p.2
      · simpa using hM)
  have hw (ω : Ω) : (∫ t, H (t, ω) ∂ν) = f ω * g ω := by
    have hs : {t : ℝ | t ≤ f ω} ∩ Ioc 0 1 = Ioc 0 (f ω) := by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioc]
      constructor
      · rintro ⟨ht, ht0, _⟩
        exact ⟨ht0, ht⟩
      · rintro ⟨ht0, ht⟩
        exact ⟨ht, ht0, ht.trans (hf1 ω)⟩
    change (∫ t, {t : ℝ | t ≤ f ω}.indicator (fun _ ↦ g ω) t ∂ν) = _
    have ht : MeasurableSet {t : ℝ | t ≤ f ω} :=
      measurableSet_le measurable_id measurable_const
    rw [integral_indicator ht]
    rw [setIntegral_const]
    simp [ν, measureReal_def, hs, hf0 ω]
  have he := integral_integral_swap (μ := ν) (ν := μ)
    (f := fun t ω ↦ H (t, ω)) hb
  change (∫ t, ∫ ω, H (t, ω) ∂μ ∂ν) = ∫ ω, ∫ t, H (t, ω) ∂ν ∂μ at he
  rw [show (fun ω ↦ ∫ t, H (t, ω) ∂ν) = fun ω ↦ f ω * g ω from funext hw] at he
  exact he.symm

/-- Integrating a unit-interval-valued variable on an event equals the integral of
the real probabilities of that event intersected with the variable's level sets. -/
theorem integral_indicator_unit_layers (μ : Measure Ω) [IsFiniteMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω)
    (hg1 : ∀ ω, g ω ≤ 1) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω in A, g ω ∂μ = ∫ t in Ioc (0 : ℝ) 1, μ.real (A ∩ {ω | t ≤ g ω}) := by
  classical
  have hi : Measurable (A.indicator (fun _ : Ω ↦ (1 : ℝ))) :=
    measurable_const.indicator hA
  have he := integral_mul_unit_layers μ g (A.indicator fun _ ↦ (1 : ℝ)) hg hi hg0 hg1
    (M := 1) (by norm_num) (by intro ω; simp [Set.indicator]; split_ifs <;> norm_num)
  have hf : (fun ω ↦ g ω * A.indicator (fun _ ↦ (1 : ℝ)) ω) = A.indicator g := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  rw [hf, integral_indicator hA] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with t
  have ht : MeasurableSet {ω | t ≤ g ω} := measurableSet_le measurable_const hg
  have hj : (fun ω ↦ if t ≤ g ω then A.indicator (fun _ ↦ (1 : ℝ)) ω else 0) =
      (A ∩ {ω | t ≤ g ω}).indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    by_cases hω : ω ∈ A <;> by_cases htw : t ≤ g ω <;>
      simp [Set.indicator, hω, htw]
  rw [hj, integral_indicator (hA.inter ht), setIntegral_const]
  simp

private theorem prob_layers_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) (g : Ω → ℝ) :
    Integrable (fun t : ℝ ↦ μ.real (A ∩ {ω | t ≤ g ω}))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hm : Antitone (fun t : ℝ ↦ μ.real (A ∩ {ω | t ≤ g ω})) := by
    intro s t hst
    exact measureReal_mono fun ω hω ↦ ⟨hω.1, hst.trans hω.2⟩
  refine (integrable_const (1 : ℝ)).mono' hm.measurable.aestronglyMeasurable ?_
  filter_upwards [] with t
  simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using
    (measureReal_le_one (μ := μ) (s := A ∩ {ω | t ≤ g ω}))

/-- An event from the first sigma-algebra and a unit-interval-valued measurable
variable from the second have covariance bounded by the event mixing coefficient. -/
theorem event_unit_covariance_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : MeasurableSpace Ω) (hF : F ≤ mΩ) (hG : G ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet[F] A) (g : Ω → ℝ)
    (hg : @Measurable Ω ℝ G inferInstance g)
    (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1) :
    |(∫ ω in A, g ω ∂μ) - μ.real A * ∫ ω, g ω ∂μ| ≤
      strongMixingCoeff (mΩ := mΩ) μ F G := by
  have hgm : @Measurable Ω ℝ mΩ inferInstance g := hg.mono hG le_rfl
  have hAm : MeasurableSet[mΩ] A := hF _ hA
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  let a : ℝ → ℝ := fun t ↦ μ.real (A ∩ {ω | t ≤ g ω})
  let b : ℝ → ℝ := fun t ↦ μ.real {ω | t ≤ g ω}
  have ha : Integrable a ν := prob_layers_integrable (mΩ := mΩ) μ A g
  have hb : Integrable b ν := by
    simpa [b] using (prob_layers_integrable (mΩ := mΩ) μ univ g)
  have heA : (∫ ω in A, g ω ∂μ) = ∫ t, a t ∂ν :=
    integral_indicator_unit_layers (mΩ := mΩ) μ g hgm hg0 hg1 hAm
  have heB : (∫ ω, g ω ∂μ) = ∫ t, b t ∂ν := by
    simpa [b, ν] using
      (integral_indicator_unit_layers (mΩ := mΩ) μ g hgm hg0 hg1
        (@MeasurableSet.univ Ω mΩ))
  rw [heA, heB, ← integral_const_mul, ← integral_sub ha (hb.const_mul (μ.real A))]
  have hbound : ∀ᵐ t ∂ν, ‖a t - μ.real A * b t‖ ≤
      strongMixingCoeff (mΩ := mΩ) μ F G := by
    filter_upwards [] with t
    exact event_le_strongMixingCoeff (mΩ := mΩ) μ F G hA
      (measurableSet_le measurable_const hg)
  have hn := norm_integral_le_of_norm_le_const hbound
  simpa [ν, measureReal_def] using hn

private theorem unit_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω)
    (hg1 : ∀ ω, g ω ≤ 1) : Integrable g μ :=
  (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 ω)] using hg1 ω)

private theorem weighted_layers_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω)
    (hg1 : ∀ ω, g ω ≤ 1) :
    Integrable (fun t : ℝ ↦ ∫ ω in {ω | t ≤ f ω}, g ω ∂μ)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hgi := unit_integrable μ g hg hg0 hg1
  have hm : Antitone (fun t : ℝ ↦ ∫ ω in {ω | t ≤ f ω}, g ω ∂μ) := by
    intro s t hst
    exact setIntegral_mono_set hgi.integrableOn
      (Filter.Eventually.of_forall hg0)
      (Filter.Eventually.of_forall fun ω hω ↦ hst.trans hω)
  refine (integrable_const (1 : ℝ)).mono' hm.measurable.aestronglyMeasurable ?_
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg hg0)]
  refine (setIntegral_le_integral hgi (Filter.Eventually.of_forall hg0)).trans ?_
  have he := integral_mono_ae hgi (integrable_const (1 : ℝ))
    (Filter.Eventually.of_forall hg1)
  simpa using he

/-- Two unit-interval-valued variables measurable for the respective sigma-algebras
have covariance bounded by their strong-mixing coefficient, with sharp factor one. -/
theorem unit_covariance_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : MeasurableSpace Ω) (hF : F ≤ mΩ) (hG : G ≤ mΩ)
    (f g : Ω → ℝ) (hf : @Measurable Ω ℝ F inferInstance f)
    (hg : @Measurable Ω ℝ G inferInstance g)
    (hf0 : ∀ ω, 0 ≤ f ω) (hf1 : ∀ ω, f ω ≤ 1)
    (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1) :
    |(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ| ≤
      strongMixingCoeff (mΩ := mΩ) μ F G := by
  have hfm : @Measurable Ω ℝ mΩ inferInstance f := hf.mono hF le_rfl
  have hgm : @Measurable Ω ℝ mΩ inferInstance g := hg.mono hG le_rfl
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  let a : ℝ → ℝ := fun t ↦ ∫ ω in {ω | t ≤ f ω}, g ω ∂μ
  let b : ℝ → ℝ := fun t ↦ μ.real {ω | t ≤ f ω}
  have ha : Integrable a ν :=
    weighted_layers_integrable (mΩ := mΩ) μ f g hgm hg0 hg1
  have hb : Integrable b ν := by
    simpa [b] using (prob_layers_integrable (mΩ := mΩ) μ univ f)
  have heA : (∫ ω, f ω * g ω ∂μ) = ∫ t, a t ∂ν := by
    rw [integral_mul_unit_layers (mΩ := mΩ) μ f g hfm hgm hf0 hf1
      (M := 1) (by norm_num) (fun ω ↦ by rw [abs_of_nonneg (hg0 ω)]; exact hg1 ω)]
    apply integral_congr_ae
    filter_upwards [] with t
    exact integral_indicator (measurableSet_le measurable_const hfm)
  have heB : (∫ ω, f ω ∂μ) = ∫ t, b t ∂ν := by
    simpa [b, ν] using
      (integral_indicator_unit_layers (mΩ := mΩ) μ f hfm hf0 hf1
        (@MeasurableSet.univ Ω mΩ))
  rw [heA, heB, ← integral_mul_const, ← integral_sub ha (hb.mul_const (∫ ω, g ω ∂μ))]
  have hbound : ∀ᵐ t ∂ν, ‖a t - b t * ∫ ω, g ω ∂μ‖ ≤
      strongMixingCoeff (mΩ := mΩ) μ F G := by
    filter_upwards [] with t
    exact event_unit_covariance_le (mΩ := mΩ) μ F G hF hG
      (measurableSet_le measurable_const hf) g hg hg0 hg1
  have hn := norm_integral_le_of_norm_le_const hbound
  simpa [ν, measureReal_def] using hn

end StrongMixing
