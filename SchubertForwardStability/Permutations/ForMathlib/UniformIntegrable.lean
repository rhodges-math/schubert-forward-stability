import SchubertForwardStability.Permutations.ForMathlib.UniformFinite
import Mathlib.Tactic

/-! # Integrability under finite uniform laws

This file contains general results that extend Mathlib. Every function into a normed group
is integrable for the uniform measure on a finite set.
-/

namespace ProbabilityTheory

open MeasureTheory
open scoped Classical ENNReal

/-- Every function into a normed group is integrable under a finite uniform law. -/
theorem integrable_uniform_finset {α E : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [NormedAddCommGroup E]
    (s : Finset α) (f : α → E) : Integrable f (uniformOn (s : Set α)) := by
  by_cases hs : s.Nonempty
  · have hf : IntegrableOn f (s : Set α) Measure.count := by
      rw [← (s : Set α).biUnion_of_singleton,
        integrableOn_finite_biUnion s.finite_toSet]
      intro x _
      exact integrableOn_singleton (hx := by simp)
    rw [uniformOn, cond]
    exact hf.smul_measure (by
      simp only [Measure.count_apply_finset, ENNReal.inv_ne_top, Nat.cast_ne_zero]
      exact Finset.card_ne_zero.mpr hs)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

end ProbabilityTheory
