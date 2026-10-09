import SchubertForwardStability.LimitTheorems.TotalVariation.Product
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Comparison of finite probability laws

## Main results

Pushforward contracts finite-source total variation, products have a sum bound,
and the range of a real observable bounds its expectation difference. The latter
two estimates follow from maximal couplings.

## References

* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, second edition, American
  Mathematical Society, Providence, RI, 2017, Proposition 4.7.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

namespace LimitTheorems

variable {α β E : Type*} [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace E]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass E]

omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
/-- Finite-source pushforwards evaluate every event by its inverse image. -/
theorem map_apply_finite_source (μ : Measure α) (f : α → E) (A : Set E) :
    μ.map f A = μ (f ⁻¹' A) := by
  let s : Finset E := Finset.univ.image f
  let g : α → s := fun x => ⟨f x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
  have hcoe : MeasurableEmbedding (Subtype.val : s → E) :=
    ⟨Subtype.val_injective, measurable_subtype_coe,
      fun A _ => ((Set.toFinite A).image Subtype.val).measurableSet⟩
  have he : f = Subtype.val ∘ g := rfl
  rw [he, ← Measure.map_map measurable_subtype_coe (measurable_of_countable g),
    hcoe.map_apply,
    Measure.map_apply (measurable_of_countable g) (Set.toFinite _).measurableSet]
  rfl

omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
/-- Pushforward contracts total variation for finite source probability laws. -/
theorem totalVariation_map_le_finite (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : α → E) :
    totalVariation (μ.map f) (ν.map f) ≤ totalVariation μ ν := by
  unfold totalVariation at ⊢
  apply ciSup_le
  intro A
  simp only [measureReal_def, map_apply_finite_source]
  exact event_diff_le_totalVariation μ ν (f ⁻¹' A)

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- Product-law total variation is at most the sum of the marginal distances. -/
theorem totalVariation_prod_le (μ ν : Measure α) (κ η : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure κ] [IsProbabilityMeasure η] :
    totalVariation (μ.prod κ) (ν.prod η) ≤ totalVariation μ ν + totalVariation κ η := by
  let R : (α × α) × (β × β) → (α × β) × (α × β) := fun p =>
    ((p.1.1, p.2.1), (p.1.2, p.2.2))
  let ρ := (productCoupling μ ν κ η).map R
  have hR : Measurable R := measurable_of_countable _
  have hf : ρ.map Prod.fst = μ.prod κ := by
    dsimp only [ρ]
    rw [Measure.map_map measurable_fst hR]
    exact productCoupling_original μ ν κ η
  have hs : ρ.map Prod.snd = ν.prod η := by
    dsimp only [ρ]
    rw [Measure.map_map measurable_snd hR]
    exact productCoupling_comparison μ ν κ η
  have he : ρ.real {p | p.1 ≠ p.2} =
      (productCoupling μ ν κ η).real {p | p.1.1 ≠ p.1.2 ∨ p.2.1 ≠ p.2.2} := by
    dsimp only [ρ]
    rw [map_measureReal_apply hR (Set.toFinite _).measurableSet]
    congr 1
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, R, ne_eq, Prod.mk.injEq, not_and_or]
  exact (totalVariation_le_mismatch (μ.prod κ) (ν.prod η) ρ hf hs).trans
    (he.trans_le (productCoupling_mismatch_le μ ν κ η))

omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace E] [MeasurableSingletonClass E] in
private theorem finite_integrable (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) :
    Integrable f μ :=
  integrableOn_univ.mp (IntegrableOn.of_finite (Set.toFinite Set.univ))

omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- The range length of a real observable bounds its finite-law expectation difference. -/
theorem abs_integral_sub_le_tv_range (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : α → ℝ) (C : ℝ)
    (hf : ∀ x, f x ∈ Set.Icc 0 C) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ C * totalVariation μ ν := by
  let ρ := maximalCoupling μ ν
  have hfirst : (∫ x, f x ∂μ) = ∫ p, f p.1 ∂ρ := by
    rw [← maximalCoupling_fst μ ν]
    exact integral_map measurable_fst.aemeasurable
      (measurable_of_countable f).aestronglyMeasurable
  have hsecond : (∫ x, f x ∂ν) = ∫ p, f p.2 ∂ρ := by
    rw [← maximalCoupling_snd μ ν]
    exact integral_map measurable_snd.aemeasurable
      (measurable_of_countable f).aestronglyMeasurable
  rw [hfirst, hsecond, ← integral_sub (finite_integrable ρ _) (finite_integrable ρ _)]
  calc
    _ ≤ ∫ p, |f p.1 - f p.2| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ p, ({p | p.1 ≠ p.2} : Set (α × α)).indicator (fun _ => C) p ∂ρ := by
      apply integral_mono (finite_integrable ρ _) (finite_integrable ρ _)
      intro p
      by_cases he : p.1 = p.2
      · simp [he]
      · rw [Set.indicator_of_mem he]
        exact abs_le.mpr ⟨by linarith [(hf p.1).1, (hf p.2).2],
          by linarith [(hf p.1).2, (hf p.2).1]⟩
    _ = _ := by
      rw [integral_indicator_const C (Set.toFinite _).measurableSet, smul_eq_mul,
        mul_comm, maximalCoupling_mismatch]

end LimitTheorems
