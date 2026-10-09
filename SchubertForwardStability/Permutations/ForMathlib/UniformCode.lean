import SchubertForwardStability.Permutations.ForMathlib.UniformFinite
import Mathlib.Data.Fintype.BigOperators

/-!
# Uniform finite coordinate laws

This file contains general results that extend Mathlib.

## Main results

Dependent finite uniform coordinates have a product law and mutually independent
projections. Injective finite sampling and finite equivalences preserve uniform mass.

## Implementation notes

The dependent product-law identity permits empty factors. Projection independence
requires nonempty coordinate types, including the empty index family.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

noncomputable section

namespace ProbabilityTheory

/-- Uniform laws on finite dependent coordinate types are their product laws. -/
theorem uniformOn_univ_pi_dep {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] [∀ i, MeasurableSpace (β i)]
    [∀ i, MeasurableSingletonClass (β i)] :
    uniformOn (Set.univ : Set ((i : ι) → β i)) =
      Measure.pi (fun i => uniformOn (Set.univ : Set (β i))) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton, uniformOn_univ, Measure.count_singleton]
  simp_rw [uniformOn_univ, Measure.count_singleton, one_div]
  rw [Fintype.card_pi, Nat.cast_prod]
  exact ENNReal.prod_inv_distrib (by
    intro i _ j _ _
    right
    exact ENNReal.natCast_ne_top _)

/-- Coordinate projections under a finite uniform product law are mutually independent. -/
theorem iIndepFun_uniform_coordinates {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    [∀ i, MeasurableSpace (β i)] [∀ i, MeasurableSingletonClass (β i)] :
    iIndepFun (fun i (x : (i : ι) → β i) => x i)
      (uniformOn (Set.univ : Set ((i : ι) → β i))) := by
  rw [uniformOn_univ_pi_dep]
  exact iIndepFun_pi (fun _ => aemeasurable_id)

/-- Injective finite sampling transports uniform mass to the image family. -/
theorem map_uniformOn_finite_injective {α β : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [Countable β] (f : α → β) (hf : Function.Injective f) :
    (uniformOn (Set.univ : Set α)).map f = uniformOn (Finset.univ.image f : Set β) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_countable f) (measurableSet_singleton x),
    uniformOn_finset_singleton]
  by_cases hx : x ∈ Finset.univ.image f
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    have hp : f ⁻¹' {f a} = {a} := by
      ext b
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact hf.eq_iff
    rw [hp, uniformOn_univ, Measure.count_singleton, ite_eq_left hx,
      Finset.card_image_of_injective _ hf, Finset.card_univ, one_div]
  · have hp : f ⁻¹' {x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hx (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)
    rw [hp, measure_empty, ite_eq_right hx]

/-- A finite equivalence preserves the uniform law on the entire carrier. -/
theorem map_uniformOn_equiv {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (e : α ≃ β) :
    (uniformOn (Set.univ : Set α)).map e = uniformOn (Set.univ : Set β) := by
  rw [map_uniformOn_finite_injective e e.injective]
  congr 1
  ext b
  simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and,
    Set.mem_univ, iff_true]
  exact e.surjective b

end ProbabilityTheory

end
