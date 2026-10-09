import SchubertForwardStability.Paper.Boolean.TagConditioning
import SchubertForwardStability.Paper.Boolean.TagFutureEvents
import SchubertForwardStability.StrongMixing.MarkovChains.FiniteConditioning

/-! # Past/future event mixing under the uniform tag law

Prefix cylinders have uniform compatible suffix conditional probabilities.
Distant suffix-event probabilities contract across their two possible boundary
states. Finite history-fiber summation turns this into a past/future event bound.
-/

open MeasureTheory ProbabilityTheory FinitaryPerm StrongMixing
open scoped Classical

namespace RecordStability

/-- An invalid prefix has zero probability under the uniform valid tag-word law. -/
theorem tagLaw_invalid_prefix {t s : ℕ} (P : Fin t → BlockTag) (hP : ¬IsTagWord P) :
    (tagLaw (t + s)).real {T | ∀ i : Fin t, T (i.castAdd s) = P i} = 0 := by
  rw [tagLaw_real_set]
  simp only [Set.mem_ofPred_eq]
  have he : (tagWords (t + s)).filter
      (fun T => ∀ i : Fin t, T (i.castAdd s) = P i) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro T hT
    obtain ⟨hw, hp⟩ := Finset.mem_filter.mp hT
    have hv := isTagWord_prefix T ((mem_tagWords T).mp hw)
    have heq : (fun i : Fin t => T (i.castAdd s)) = P := funext hp
    exact hP (heq ▸ hv)
  rw [he]
  simp

/-- Every prefix cylinder factors with a distant suffix event through the
boundary-state future-event probability. Invalid prefixes contribute zero. -/
theorem tagLaw_prefix_factor {t m g : ℕ} (P : Fin t → BlockTag) (ht : 0 < t)
    (B : Set (Fin m → BlockTag)) :
    (tagLaw (t + (m + g))).real {T |
      (∀ i : Fin t, T (i.castAdd (m + g)) = P i) ∧
        tagDrop m g (fun j : Fin (m + g) => T (j.natAdd t)) ∈ B} =
      (tagLaw (t + (m + g))).real {T |
        ∀ i : Fin t, T (i.castAdd (m + g)) = P i} *
          tagFutureEventProb m g B (tagPrefixPresent P ht) := by
  by_cases hP : IsTagWord P
  · have hp := tagLaw_prefix_conditional (m := m + g) P ht hP
      {Q | tagDrop m g Q ∈ B}
    have he := (div_eq_iff hp.1.ne').mp hp.2
    simpa only [tagFutureEventProb, tagSuffixEventProb, tagSuffixEventCount,
      Set.mem_ofPred_eq, mul_comm] using he
  · have hp := tagLaw_invalid_prefix (s := m + g) P hP
    have hi : (tagLaw (t + (m + g))).real {T |
        (∀ i : Fin t, T (i.castAdd (m + g)) = P i) ∧
          tagDrop m g (fun j : Fin (m + g) => T (j.natAdd t)) ∈ B} = 0 := by
      apply le_antisymm _ measureReal_nonneg
      calc
        _ ≤ (tagLaw (t + (m + g))).real {T |
            ∀ i : Fin t, T (i.castAdd (m + g)) = P i} :=
          measureReal_mono (fun _ h => h.1)
        _ = 0 := hp
    rw [hi, hp, zero_mul]

/-- A past event determined by the first `t` tags and an event determined by the
last `m` tags, separated by `g` omitted tags, have probability discrepancy at most
`(1/6)^g` under the uniform valid tag law. -/
theorem tagLaw_past_future_discrepancy (t m g : ℕ) (ht : 0 < t)
    (A : Set (Fin (t + (m + g)) → BlockTag))
    (hA : MeasurableSet[MeasurableSpace.comap
      (fun T : Fin (t + (m + g)) → BlockTag => fun i : Fin t => T (i.castAdd (m + g)))
      inferInstance] A) (B : Set (Fin m → BlockTag)) :
    |(tagLaw (t + (m + g))).real (A ∩ {T |
        tagDrop m g (fun j : Fin (m + g) => T (j.natAdd t)) ∈ B}) -
      (tagLaw (t + (m + g))).real A * (tagLaw (t + (m + g))).real {T |
        tagDrop m g (fun j : Fin (m + g) => T (j.natAdd t)) ∈ B}| ≤ (1 / 6 : ℝ) ^ g := by
  let f (T : Fin (t + (m + g)) → BlockTag) (i : Fin t) := T (i.castAdd (m + g))
  let F : Set (Fin (t + (m + g)) → BlockTag) :=
    {T | tagDrop m g (fun j : Fin (m + g) => T (j.natAdd t)) ∈ B}
  let q (P : Fin t → BlockTag) := tagFutureEventProb m g B (tagPrefixPresent P ht)
  apply finite_conditioning_discrepancy (tagLaw (t + (m + g))) f
    (measurable_of_countable f) hA (Set.toFinite F).measurableSet q (by positivity)
  · intro P
    have he : {T | f T = P} = {T | ∀ i : Fin t, T (i.castAdd (m + g)) = P i} := by
      ext T
      simp only [f, Set.mem_ofPred_eq, funext_iff]
    have hi : {T | f T = P} ∩ F = {T |
        (∀ i : Fin t, T (i.castAdd (m + g)) = P i) ∧
          tagDrop m g (fun j : Fin (m + g) => T (j.natAdd t)) ∈ B} := by
      rw [he]
      rfl
    rw [hi, he]
    exact tagLaw_prefix_factor P ht B
  · intro P Q
    have h := tagFutureEventProb_contract m g B
    cases hp : tagPrefixPresent P ht <;> cases hq : tagPrefixPresent Q ht
    · simp only [q, hp, hq, sub_self, abs_zero]
      positivity
    · simpa only [q, hp, hq] using h
    · simpa only [q, hp, hq, abs_sub_comm] using h
    · simp only [q, hp, hq, sub_self, abs_zero]
      positivity

end RecordStability
