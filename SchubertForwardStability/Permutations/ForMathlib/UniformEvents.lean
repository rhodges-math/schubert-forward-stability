import SchubertForwardStability.Permutations.ForMathlib.UniformFinite

/-! # Event probabilities for finite uniform laws

This file contains general results that extend Mathlib. Event probabilities are filtered
cardinality ratios, and finite uniform laws are concentrated on their sampling family.
-/

open MeasureTheory
open scoped Classical ENNReal

namespace ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The probability of any event under a finite uniform law is its filtered fraction. -/
theorem uniformOn_finset_event (s : Finset α) (A : Set α) :
    uniformOn (s : Set α) A = ((s.filter fun x ↦ x ∈ A).card : ℝ≥0∞) / s.card := by
  have hset : (s : Set α) ∩ A = (s.filter fun x ↦ x ∈ A : Set α) := by
    ext x
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter]
  rw [uniformOn, cond_apply s.measurableSet, Measure.count_apply_finset, hset,
    Measure.count_apply_finset]
  rw [div_eq_mul_inv, mul_comm]

/-- A nonempty finite uniform law is almost surely in its sampling family. -/
theorem ae_mem_uniformOn_finset (s : Finset α) (hs : s.Nonempty) :
    ∀ᵐ x ∂uniformOn (s : Set α), x ∈ s := by
  let := isProbabilityMeasure_uniformOn s.finite_toSet hs
  change (s : Set α) ∈ ae (uniformOn (s : Set α))
  exact (mem_ae_iff_prob_eq_one s.measurableSet).mpr (uniformOn_self s.finite_toSet hs)

end ProbabilityTheory
