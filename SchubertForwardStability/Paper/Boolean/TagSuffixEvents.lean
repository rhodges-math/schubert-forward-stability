import SchubertForwardStability.Permutations.Random.Tags.TagKernel
import Mathlib.Tactic

/-! # Suffix-event probabilities and transition recursion

Uniform compatible suffix counts define event probabilities for either boundary
presence state. Splitting the first symbol proves their exact two-state transition
recursion, including zero remaining length and arbitrary events on the tail.
-/

open FinitaryPerm
open scoped Classical BigOperators

namespace RecordStability

/-- The number of compatible suffixes lying in an event. -/
noncomputable def tagSuffixEventCount (m : ℕ) (present : Bool)
    (B : Set (Fin m → BlockTag)) : ℕ :=
  (Finset.univ.filter fun Q : Fin m → BlockTag => ValidTagSuffix present Q ∧ Q ∈ B).card

/-- The event probability under the uniform law on compatible suffixes from a
specified boundary presence state. -/
noncomputable def tagSuffixEventProb (m : ℕ) (present : Bool)
    (B : Set (Fin m → BlockTag)) : ℝ :=
  tagSuffixEventCount m present B / (extensionCount m present : ℝ)

/-- A suffix-event count is bounded by the total compatible completion count. -/
theorem tagSuffixEventCount_le (m : ℕ) (present : Bool) (B : Set (Fin m → BlockTag)) :
    tagSuffixEventCount m present B ≤ extensionCount m present := by
  apply Finset.card_le_card
  intro Q hQ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hQ).2.1⟩

/-- Every compatible-suffix event probability is in the unit interval. -/
theorem tagSuffixEventProb_bounds (m : ℕ) (present : Bool) (B : Set (Fin m → BlockTag)) :
    0 ≤ tagSuffixEventProb m present B ∧ tagSuffixEventProb m present B ≤ 1 := by
  have hU : 0 < (extensionCount m present : ℝ) := by
    exact_mod_cast extensionCount_pos m present
  refine ⟨div_nonneg (Nat.cast_nonneg _) hU.le, (div_le_one hU).mpr ?_⟩
  exact_mod_cast tagSuffixEventCount_le m present B

/-- Compatible suffixes whose tails lie in an event split by their first symbol
into the next-state compatible event fibers. -/
private noncomputable def tailEventSplit (m : ℕ) (present : Bool)
    (B : Set (Fin m → BlockTag)) :
    {T : Fin (m + 1) → BlockTag // ValidTagSuffix present T ∧ Fin.tail T ∈ B} ≃
      Σ a : {a : BlockTag // a = .cont → present = true},
        {Q : Fin m → BlockTag // ValidTagSuffix (decide (a.val ≠ .zero)) Q ∧ Q ∈ B} where
  toFun T := by
    have hv := (validTagSuffix_cons present (T.val 0) (Fin.tail T.val)).mp
      (by rw [Fin.cons_self_tail]; exact T.property.1)
    exact ⟨⟨T.val 0, hv.1⟩, ⟨Fin.tail T.val, hv.2, T.property.2⟩⟩
  invFun a := ⟨Fin.cons a.1.val a.2.val,
    (validTagSuffix_cons present a.1.val a.2.val).mpr ⟨a.1.property, a.2.property.1⟩,
    by simpa only [Fin.tail_cons] using a.2.property.2⟩
  left_inv T := Subtype.ext (Fin.cons_self_tail T.val)
  right_inv a := by
    rcases a with ⟨⟨a, ha⟩, ⟨Q, hQ⟩⟩
    dsimp only
    refine Sigma.ext ?_ ?_
    · apply Subtype.ext
      exact @Fin.cons_zero m (fun _ : Fin (m + 1) => BlockTag) a Q
    · apply heq_of_eq
      exact Subtype.ext (@Fin.tail_cons m (fun _ : Fin (m + 1) => BlockTag) a Q)

/-- The first-symbol decomposition gives an exact sum of compatible tail-event counts. -/
private theorem tail_event_count_sum (m : ℕ) (present : Bool)
    (B : Set (Fin m → BlockTag)) :
    tagSuffixEventCount (m + 1) present {T | Fin.tail T ∈ B} =
      ∑ a ∈ (Finset.univ : Finset BlockTag).filter (fun a => a = .cont → present = true),
        tagSuffixEventCount m (decide (a ≠ .zero)) B := by
  have he : tagSuffixEventCount (m + 1) present {T | Fin.tail T ∈ B} =
      Fintype.card {T : Fin (m + 1) → BlockTag //
        ValidTagSuffix present T ∧ Fin.tail T ∈ B} := by
    rw [Fintype.card_subtype]
    rfl
  rw [he, Fintype.card_congr (tailEventSplit m present B), Fintype.card_sigma]
  simp only [Fintype.card_subtype]
  change (∑ a : {a : BlockTag // a = .cont → present = true},
      tagSuffixEventCount m (decide (a.val ≠ .zero)) B) = _
  apply Finset.sum_bij (fun a _ => a.val)
  · intro a _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.property⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro a ha
    exact ⟨⟨a, (Finset.mem_filter.mp ha).2⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl

/-- Dropping the first symbol gives one present next-state event fiber from an
absent boundary and two from a present boundary, plus one absent-state fiber. -/
theorem tagSuffixEventCount_tail (m : ℕ) (present : Bool) (B : Set (Fin m → BlockTag)) :
    tagSuffixEventCount (m + 1) present {T | Fin.tail T ∈ B} =
      tagSuffixEventCount m false B + (if present then 2 else 1) *
        tagSuffixEventCount m true B := by
  rw [tail_event_count_sum]
  have hU : (Finset.univ : Finset BlockTag) = {.zero, .start, .cont} := rfl
  rw [hU]
  cases present <;> simp [Finset.filter_insert]
  omega

/-- The uniform compatible-suffix probability of a tail event is the
two-state kernel average of that event's next-boundary probabilities. -/
theorem tagSuffixEventProb_tail (m : ℕ) (present : Bool) (B : Set (Fin m → BlockTag)) :
    tagSuffixEventProb (m + 1) present {T | Fin.tail T ∈ B} =
      ∑ b : Bool, tagKernel m present b * tagSuffixEventProb m b B := by
  have h0 : 0 < (extensionCount m false : ℝ) := by
    exact_mod_cast extensionCount_pos m false
  have h1 : 0 < (extensionCount m true : ℝ) := by
    exact_mod_cast extensionCount_pos m true
  cases present <;>
    simp only [tagSuffixEventProb, tagSuffixEventCount_tail, extensionCount_false_succ,
      extensionCount_true_succ, tagKernel, Fintype.univ_bool, Finset.sum_insert,
      Finset.mem_singleton, Bool.true_eq_false, Bool.false_eq_true, not_false_eq_true,
      Finset.sum_singleton,
      ite_false, ite_true, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, one_mul]
  all_goals (field_simp; ring)

end RecordStability
