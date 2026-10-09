import SchubertForwardStability.Permutations.ForMathlib.UniformFinite
import Mathlib.Probability.Distributions.Uniform

/-! # Finite uniform PMFs and normalized counting measures

This file contains general results that extend Mathlib. On a countable carrier with
measurable singletons, the finite uniform PMF induces precisely the corresponding normalized
counting measure.
-/

open MeasureTheory

namespace PMF

/-- A uniform PMF on a nonempty finite subset of a countable measurable carrier
has measure equal to the normalized counting measure on that subset. -/
theorem toMeasure_uniform_finset {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] (s : Finset α) (hs : s.Nonempty) :
    (uniformOfFinset s hs).toMeasure = ProbabilityTheory.uniformOn (s : Set α) := by
  apply Measure.ext_of_singleton
  intro a
  rw [PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a),
    ProbabilityTheory.uniformOn_finset_singleton]
  exact uniformOfFinset_apply hs a

end PMF
