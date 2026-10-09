import SchubertForwardStability.Permutations.ForMathlib.UniformFinite

/-! # Uniform laws under finite-family bijections

This file contains general results that extend Mathlib. A bijection on two finite supports
preserves their normalized counting measures. The statement includes empty supports and does
not require global injectivity.
-/

open MeasureTheory
open scoped Classical ENNReal

namespace ProbabilityTheory

/-- A bijection between finite supports transports their uniform laws exactly. -/
theorem map_uniformOn_finset_bij {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Countable α] [Countable β] (s : Finset α) (t : Finset β) (f : α → β)
    (hf : Set.BijOn f (s : Set α) (t : Set β)) :
    (uniformOn (s : Set α)).map f = uniformOn (t : Set β) := by
  have hCard : s.card = t.card := Finset.card_nbij f hf.1 hf.2.1 hf.2.2
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_countable f) (measurableSet_singleton x),
    ← uniformOn_inter_self (s := (s : Set α)) (t := f ⁻¹' {x}) s.finite_toSet]
  by_cases hx : x ∈ t
  · obtain ⟨a, ha, rfl⟩ := hf.2.2 hx
    have ha' : a ∈ s := ha
    have hFiber : (s : Set α) ∩ f ⁻¹' {f a} = {a} := by
      ext b
      simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hb, hfb⟩
        exact hf.2.1 hb ha hfb
      · intro he
        subst b
        exact ⟨ha, rfl⟩
    rw [hFiber, uniformOn_finset_singleton, uniformOn_finset_singleton]
    simp only [ha', hx, ite_true, hCard]
  · have hFiber : (s : Set α) ∩ f ⁻¹' {x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro a ⟨ha, hfa⟩
      exact hx (hfa ▸ hf.1 ha)
    rw [hFiber, measure_empty, uniformOn_finset_singleton, ite_eq_right hx]

end ProbabilityTheory
