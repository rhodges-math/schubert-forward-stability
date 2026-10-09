import SchubertForwardStability.StrongMixing.Inequalities.UnitCovariance
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic.Ring

/-! # Product sigma-algebras and section probabilities

Section probabilities remain measurable for the unintegrated event sigma-algebra.
Restriction to a smaller sigma-algebra is expressed using measure trimming, not by
changing the ambient measurable-space instance of the original measure.
-/

open MeasureTheory
open scoped ENNReal

namespace StrongMixing

variable {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]

/-- Enlarging both factor sigma-algebras enlarges their product sigma-algebra. -/
theorem product_fields_mono {F : MeasurableSpace α} {G : MeasurableSpace β}
    (hF : F ≤ mα) (hG : G ≤ mβ) : F.prod G ≤ mα.prod mβ := by
  exact sup_le_sup (MeasurableSpace.comap_mono hF) (MeasurableSpace.comap_mono hG)

omit mβ in
/-- Integrating a product-measurable event's first-coordinate sections gives a
measurable real probability function for the event's second-coordinate sigma-algebra. -/
theorem measurable_section_prob (μ : Measure α) [IsFiniteMeasure μ]
    (F : MeasurableSpace α) (G : MeasurableSpace β) (hF : F ≤ mα)
    {A : Set (α × β)} (hA : MeasurableSet[F.prod G] A) :
    @Measurable β ℝ G inferInstance (fun y ↦ μ.real {x | (x, y) ∈ A}) := by
  have hm := @measurable_measure_prodMk_right α β F G (μ.trim hF) _ A hA
  have he : (fun y ↦ (μ.trim hF) {x | (x, y) ∈ A}) =
      fun y ↦ μ {x | (x, y) ∈ A} := by
    funext y
    exact trim_measurableSet_eq hF (@measurable_prodMk_right α β F G y A hA)
  change @Measurable β ℝ≥0∞ G inferInstance
    (fun y ↦ (μ.trim hF) {x | (x, y) ∈ A}) at hm
  rw [he] at hm
  exact hm.ennreal_toReal

/-- The real probability of a product-measurable event is the integral of its
first-coordinate real section probabilities over the second measure. -/
theorem product_prob_eq_integral (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set (α × β)} (hA : MeasurableSet A) :
    (μ.prod ν).real A = ∫ y, μ.real {x | (x, y) ∈ A} ∂ν := by
  rw [measureReal_def, Measure.prod_apply_symm hA]
  symm
  exact integral_toReal (measurable_measure_prodMk_right hA).aemeasurable
    (Filter.Eventually.of_forall fun y ↦ measure_lt_top μ _)

/-- For two independent factor spaces, a pair of events measurable for product
sub-sigma-algebras has discrepancy at most the sum of the two factor coefficients. -/
theorem product_event_discrepancy_le (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F₁ G₁ : MeasurableSpace α) (F₂ G₂ : MeasurableSpace β)
    (hF₁ : F₁ ≤ mα) (hG₁ : G₁ ≤ mα) (hF₂ : F₂ ≤ mβ) (hG₂ : G₂ ≤ mβ)
    {A B : Set (α × β)} (hA : MeasurableSet[F₁.prod F₂] A)
    (hB : MeasurableSet[G₁.prod G₂] B) :
    |(@Measure.prod α β mα mβ μ ν).real (A ∩ B) -
      (@Measure.prod α β mα mβ μ ν).real A * (@Measure.prod α β mα mβ μ ν).real B| ≤
      strongMixingCoeff (mΩ := mα) μ F₁ G₁ + strongMixingCoeff (mΩ := mβ) ν F₂ G₂ := by
  let : MeasurableSpace α := mα
  let : MeasurableSpace β := mβ
  let a : β → ℝ := fun y ↦ μ.real {x | (x, y) ∈ A}
  let b : β → ℝ := fun y ↦ μ.real {x | (x, y) ∈ B}
  let c : β → ℝ := fun y ↦ μ.real {x | (x, y) ∈ A ∩ B}
  have ham : @Measurable β ℝ F₂ inferInstance a :=
    measurable_section_prob (mα := mα) μ F₁ F₂ hF₁ hA
  have hbm : @Measurable β ℝ G₂ inferInstance b :=
    measurable_section_prob (mα := mα) μ G₁ G₂ hG₁ hB
  have hAm : MeasurableSet[mα.prod mβ] A := product_fields_mono hF₁ hF₂ _ hA
  have hBm : MeasurableSet[mα.prod mβ] B := product_fields_mono hG₁ hG₂ _ hB
  have hcm : @Measurable β ℝ mβ inferInstance c :=
    (measurable_measure_prodMk_right (hAm.inter hBm)).ennreal_toReal
  have ha2 : MemLp a 2 ν := MemLp.of_bound (ham.mono hF₂ le_rfl).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y ↦ by
      change |μ.real {x | (x, y) ∈ A}| ≤ 1
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)
  have hb2 : MemLp b 2 ν := MemLp.of_bound (hbm.mono hG₂ le_rfl).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y ↦ by
      change |μ.real {x | (x, y) ∈ B}| ≤ 1
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)
  have hc2 : MemLp c 2 ν := MemLp.of_bound hcm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y ↦ by
      change |μ.real {x | (x, y) ∈ A ∩ B}| ≤ 1
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)
  have hfirst : |(∫ y, c y ∂ν) - ∫ y, a y * b y ∂ν| ≤
      strongMixingCoeff (mΩ := mα) μ F₁ G₁ := by
    rw [← integral_sub (f := c) (g := fun y ↦ a y * b y)
      (hc2.integrable (by norm_num)) (ha2.integrable_mul hb2)]
    have he : ∀ᵐ y ∂ν, ‖c y - a y * b y‖ ≤ strongMixingCoeff (mΩ := mα) μ F₁ G₁ := by
      filter_upwards [] with y
      exact event_le_strongMixingCoeff (mΩ := mα) μ F₁ G₁
        (@measurable_prodMk_right α β F₁ F₂ y A hA)
        (@measurable_prodMk_right α β G₁ G₂ y B hB)
    simpa using norm_integral_le_of_norm_le_const he
  have hsecond := unit_covariance_le (mΩ := mβ) ν F₂ G₂ hF₂ hG₂ a b ham hbm
    (fun _ ↦ measureReal_nonneg) (fun _ ↦ measureReal_le_one)
    (fun _ ↦ measureReal_nonneg) (fun _ ↦ measureReal_le_one)
  rw [product_prob_eq_integral μ ν (hAm.inter hBm),
    product_prob_eq_integral μ ν hAm, product_prob_eq_integral μ ν hBm]
  change |(∫ y, c y ∂ν) - (∫ y, a y ∂ν) * ∫ y, b y ∂ν| ≤ _
  calc
    _ ≤ |(∫ y, c y ∂ν) - ∫ y, a y * b y ∂ν| +
        |(∫ y, a y * b y ∂ν) - (∫ y, a y ∂ν) * ∫ y, b y ∂ν| := by
      have he : (∫ y, c y ∂ν) - (∫ y, a y ∂ν) * ∫ y, b y ∂ν =
          ((∫ y, c y ∂ν) - ∫ y, a y * b y ∂ν) +
            ((∫ y, a y * b y ∂ν) - (∫ y, a y ∂ν) * ∫ y, b y ∂ν) := by ring
      rw [he]
      exact abs_add_le _ _
    _ ≤ _ := add_le_add hfirst hsecond

/-- Strong-mixing coefficients of product sigma-algebras are at most the sum of
the factor coefficients, for arbitrary probability spaces. -/
theorem strongMixingCoeff_prod_le (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F₁ G₁ : MeasurableSpace α) (F₂ G₂ : MeasurableSpace β)
    (hF₁ : F₁ ≤ mα) (hG₁ : G₁ ≤ mα) (hF₂ : F₂ ≤ mβ) (hG₂ : G₂ ≤ mβ) :
    strongMixingCoeff (mΩ := mα.prod mβ) (@Measure.prod α β mα mβ μ ν)
      (F₁.prod F₂) (G₁.prod G₂) ≤
      strongMixingCoeff (mΩ := mα) μ F₁ G₁ + strongMixingCoeff (mΩ := mβ) ν F₂ G₂ := by
  let : MeasurableSpace α := mα
  let : MeasurableSpace β := mβ
  apply ciSup_le
  intro A
  apply ciSup_le
  intro B
  exact product_event_discrepancy_le μ ν F₁ G₁ F₂ G₂ hF₁ hG₁ hF₂ hG₂ A.property B.property

end StrongMixing
