import SchubertForwardStability.Permutations.Random.Tags.TagHistories
import SchubertForwardStability.Permutations.Classes.Tags.TagExtensions

/-! # Prefix-history and suffix-completion decomposition

The finite words sharing an initial presence path split into a compatible prefix
and a suffix that starts in its final presence state. This includes empty prefixes.
-/

namespace FinitaryPerm

open scoped Classical

/-- Presence through the prefix length is unchanged by appending a suffix. -/
theorem tagPresence_append_left {t m : ℕ} (P : Fin t → BlockTag) (Q : Fin m → BlockTag)
    (s : ℕ) (hs : s ≤ t) : tagPresence (Fin.append P Q) s = tagPresence P s := by
  by_cases hz : s = 0
  · subst s
    rw [tagPresence_zero, tagPresence_zero]
  · let i : Fin t := ⟨s - 1, by omega⟩
    have hi : i.val + 1 = s := by dsimp [i]; omega
    rw [← hi, tagPresence_fin P i]
    simpa using tagPresence_fin (Fin.append P Q) (i.castAdd m)

/-- Appending a suffix preserves membership in the prefix presence-history event. -/
theorem presenceHistory_append_iff {t m : ℕ} (P : Fin t → BlockTag) (Q : Fin m → BlockTag)
    (y : ℕ → Bool) : Fin.append P Q ∈ presenceHistory t y ↔ P ∈ presenceHistory t y := by
  constructor
  · intro h s hs
    rw [← tagPresence_append_left P Q s hs]
    exact h s hs
  · intro h s hs
    rw [tagPresence_append_left P Q s hs]
    exact h s hs

/-- A prefix from a prescribed full history has the prescribed final presence state. -/
theorem tagPrefixPresent_of_history {t : ℕ} (P : Fin t → BlockTag) (y : ℕ → Bool)
    (ht : 0 < t) (hP : P ∈ presenceHistory t y) : tagPrefixPresent P ht = y t := by
  have h := ((presenceHistory_full_iff P y).mp hP).2 ⟨t - 1, by omega⟩
  have hi : t - 1 + 1 = t := by omega
  simpa only [tagPrefixPresent, hi] using h

/-- Restricting a valid tag word to its prefix preserves validity. -/
theorem isTagWord_prefix {t m : ℕ} (T : Fin (t + m) → BlockTag) (hT : IsTagWord T) :
    IsTagWord (fun i : Fin t => T (i.castAdd m)) := by
  by_cases ht : 0 < t
  · have h := (validTagSuffix_append false (fun i : Fin t => T (i.castAdd m))
      (fun j : Fin m => T (j.natAdd t)) ht).mp
      (by rw [Fin.append_castAdd_natAdd]; exact hT)
    exact h.1
  · have ht0 : t = 0 := by omega
    subst t
    intro i
    exact Fin.elim0 i

private theorem validSuffix_cast {n m : ℕ} (present : Bool) (Q : Fin m → BlockTag)
    (hnm : n = m) : ValidTagSuffix present (Q ∘ Fin.cast hnm) ↔ ValidTagSuffix present Q := by
  cases hnm
  rfl

/-- After a compatible prefix, full-word validity is exactly its final-state suffix validity. -/
theorem isTagWord_append_history {t m : ℕ} (P : Fin t → BlockTag) (Q : Fin m → BlockTag)
    (y : ℕ → Bool) (hP : P ∈ tagHistoryWords t y) :
    IsTagWord (Fin.append P Q) ↔ ValidTagSuffix (y t) Q := by
  obtain ⟨hw, hh⟩ := Finset.mem_filter.mp hP
  have hv := (mem_tagWords P).mp hw
  by_cases ht : 0 < t
  · rw [IsTagWord, validTagSuffix_append false P Q ht, tagPrefixPresent_of_history P y ht hh]
    exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  · have ht0 : t = 0 := by omega
    subst t
    have hy0 := ((presenceHistory_full_iff P y).mp hh).1
    change ValidTagSuffix false (Fin.append P Q) ↔ ValidTagSuffix (y 0) Q
    rw [hy0, Fin.append_left_nil P Q rfl, validSuffix_cast]

/-- The valid words of length `t+m` sharing the initial presence history through `t`. -/
noncomputable def tagPrefixWords (t m : ℕ) (y : ℕ → Bool) :
    Finset (Fin (t + m) → BlockTag) :=
  (tagWords (t + m)).filter fun T => T ∈ presenceHistory t y

/-- Prefix-history membership consists of validity and the prescribed initial history. -/
theorem mem_tagPrefixWords {t m : ℕ} (T : Fin (t + m) → BlockTag) (y : ℕ → Bool) :
    T ∈ tagPrefixWords t m y ↔ IsTagWord T ∧ T ∈ presenceHistory t y := by
  simp only [tagPrefixWords, Finset.mem_filter, mem_tagWords]

/-- Partial-history words are a product of their compatible prefixes and final-state suffixes. -/
noncomputable def tagPrefixEquiv (t m : ℕ) (y : ℕ → Bool) :
    {T : Fin (t + m) → BlockTag // T ∈ tagPrefixWords t m y} ≃
      {P : Fin t → BlockTag // P ∈ tagHistoryWords t y} ×
        {Q : Fin m → BlockTag // ValidTagSuffix (y t) Q} where
  toFun T := by
    let P : Fin t → BlockTag := fun i => T.val (i.castAdd m)
    let Q : Fin m → BlockTag := fun j => T.val (j.natAdd t)
    have hT := (mem_tagPrefixWords T.val y).mp T.property
    have happ : Fin.append P Q = T.val := Fin.append_castAdd_natAdd
    have hh : P ∈ presenceHistory t y := (presenceHistory_append_iff P Q y).mp
      (by rw [happ]; exact hT.2)
    have hp : P ∈ tagHistoryWords t y := Finset.mem_filter.mpr
      ⟨(mem_tagWords P).mpr (isTagWord_prefix T.val hT.1), hh⟩
    exact (⟨P, hp⟩, ⟨Q, (isTagWord_append_history P Q y hp).mp
      (by rw [happ]; exact hT.1)⟩)
  invFun PQ := by
    let P := PQ.1
    let Q := PQ.2
    refine ⟨Fin.append P.val Q.val, (mem_tagPrefixWords _ _).mpr ⟨?_, ?_⟩⟩
    · exact (isTagWord_append_history P.val Q.val y P.property).mpr Q.property
    · exact (presenceHistory_append_iff P.val Q.val y).mpr
        (Finset.mem_filter.mp P.property).2
  left_inv T := by
    apply Subtype.ext
    exact Fin.append_castAdd_natAdd
  right_inv PQ := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      exact Fin.append_left PQ.1.val PQ.2.val i
    · apply Subtype.ext
      funext i
      exact Fin.append_right PQ.1.val PQ.2.val i

/-- The partial-history fiber count is prefix choices times final-state suffix completions. -/
theorem card_tagPrefixWords (t m : ℕ) (y : ℕ → Bool) :
    (tagPrefixWords t m y).card = (tagHistoryWords t y).card * extensionCount m (y t) := by
  rw [← Fintype.card_coe, Fintype.card_congr (tagPrefixEquiv t m y), Fintype.card_prod,
    Fintype.card_coe, Fintype.card_subtype, extensionCount]

/-- A partial history has compatible-prefix count times suffix count, divided by all words. -/
theorem tagLaw_prefix_history (t m : ℕ) (y : ℕ → Bool) :
    (tagLaw (t + m)).real (presenceHistory t y) =
      ((tagHistoryWords t y).card : ℝ) * extensionCount m (y t) / (tagWords (t + m)).card := by
  rw [tagLaw_real_set]
  change ((tagPrefixWords t m y).card : ℝ) / _ = _
  rw [card_tagPrefixWords, Nat.cast_mul]

/-- A partial prescribed history has positive probability exactly for absent external state. -/
theorem tagLaw_prefix_history_pos (t m : ℕ) (y : ℕ → Bool) :
    0 < (tagLaw (t + m)).real (presenceHistory t y) ↔ y 0 = false := by
  rw [tagLaw_prefix_history, card_tagHistoryWords]
  have ht : 0 < ((tagWords (t + m)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (tagWords_nonempty _)
  have hU : 0 < (extensionCount m (y t) : ℝ) := by exact_mod_cast extensionCount_pos m _
  by_cases hy0 : y 0 = false
  · rw [ite_eq_left hy0]
    simpa only [hy0, iff_true] using div_pos (mul_pos (by positivity :
      0 < ((2 ^ (freeTagPositions t y).card : ℕ) : ℝ)) hU) ht
  · rw [ite_eq_right hy0]
    simp only [Nat.cast_zero, zero_mul, zero_div, lt_self_iff_false, false_iff]
    exact hy0

end FinitaryPerm
