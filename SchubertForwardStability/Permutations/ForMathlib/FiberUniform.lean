import SchubertForwardStability.Permutations.ForMathlib.UniformEvents

/-! # Uniform pushforward measures from finite fibers

This file contains general results that extend Mathlib. Matching finite fiber cardinalities
determine the total domain cardinality and the pushforward of the uniform measure. Empty
finite families give zero laws.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace Finset

/-- Two finite maps with the same cardinality for every fiber have equal domain sizes. -/
theorem card_eq_of_filter_fibers {α β γ : Type*} (s : Finset α) (t : Finset γ)
    (f : α → β) (g : γ → β)
    (h : ∀ b, (s.filter fun a => f a = b).card = (t.filter fun a => g a = b).card) :
    s.card = t.card := by
  classical
  let u := s.image f ∪ t.image g
  have hs : (s : Set α).MapsTo f u := fun a ha =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem f ha)
  have ht : (t : Set γ).MapsTo g u := fun a ha =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem g ha)
  rw [Finset.card_eq_sum_card_fiberwise hs, Finset.card_eq_sum_card_fiberwise ht]
  exact Finset.sum_congr rfl fun b _ => h b

end Finset

namespace ProbabilityTheory

/-- Matching finite fiber counts give equal pushforward uniform measures. -/
theorem map_uniform_eq_of_fibers {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    (s : Finset α) (t : Finset γ) (f : α → β) (g : γ → β)
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ b, (s.filter fun a => f a = b).card = (t.filter fun a => g a = b).card) :
    (uniformOn (s : Set α)).map f = (uniformOn (t : Set γ)).map g := by
  classical
  have hc := Finset.card_eq_of_filter_fibers s t f g h
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply hf (measurableSet_singleton b),
    Measure.map_apply hg (measurableSet_singleton b),
    uniformOn_finset_event, uniformOn_finset_event]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [h b, hc]

end ProbabilityTheory
