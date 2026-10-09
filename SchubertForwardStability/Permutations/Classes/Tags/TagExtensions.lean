import SchubertForwardStability.Permutations.Classes.Tags.TagCounts

/-!
# Boundary-state prefix completions

## Main definitions

* `tagPrefixPresent` records the final presence state of a nonempty prefix.
* `tagCompletionEquiv` identifies prefix completions with boundary-state suffixes.

## Main results

Append validity decomposes into prefix validity and suffix validity. The explicit
completion equivalence proves dependence of completion counts on the final state.

## Implementation notes

Prefixes are positive-length and valid. The suffix length may be zero.

-/

namespace FinitaryPerm

open scoped Classical

noncomputable section

/-- The presence state of the final symbol of a nonempty finite prefix. -/
def tagPrefixPresent {t : ℕ} (P : Fin t → BlockTag) (ht : 0 < t) : Bool :=
  decide (P ⟨t - 1, by omega⟩ ≠ .zero)

private theorem suffix_append_left {t m : ℕ} (present : Bool)
    (P : Fin t → BlockTag) (Q : Fin m → BlockTag)
    (h : ValidTagSuffix present (Fin.append P Q)) : ValidTagSuffix present P := by
  intro i hi
  obtain (⟨hz, hp⟩ | ⟨j, hj, hv⟩) := h (i.castAdd m) (by simpa using hi)
  · exact Or.inl ⟨hz, hp⟩
  · change j.val + 1 = i.val at hj
    let k : Fin t := ⟨j.val, by have := i.isLt; omega⟩
    have he : j = k.castAdd m := by apply Fin.ext; rfl
    refine Or.inr ⟨k, hj, ?_⟩
    simpa only [he, Fin.append_left] using hv

private theorem suffix_append_right {t m : ℕ} (present : Bool)
    (P : Fin t → BlockTag) (Q : Fin m → BlockTag) (ht : 0 < t)
    (h : ValidTagSuffix present (Fin.append P Q)) :
    ValidTagSuffix (tagPrefixPresent P ht) Q := by
  intro i hi
  obtain (⟨hz, _⟩ | ⟨j, hj, hv⟩) := h (i.natAdd t) (by simpa using hi)
  · change t + i.val = 0 at hz
    omega
  · change j.val + 1 = t + i.val at hj
    by_cases hz : i.val = 0
    · let k : Fin t := ⟨t - 1, by omega⟩
      have he : j = k.castAdd m := by apply Fin.ext; dsimp [k]; omega
      rw [he, Fin.append_left] at hv
      refine Or.inl ⟨hz, ?_⟩
      exact decide_eq_true hv
    · let k : Fin m := ⟨j.val - t, by have := j.isLt; omega⟩
      have he : j = k.natAdd t := by apply Fin.ext; dsimp [k]; omega
      refine Or.inr ⟨k, ?_, ?_⟩
      · dsimp [k]
        omega
      · simpa only [he, Fin.append_right] using hv

private theorem suffix_append_merge {t m : ℕ} (present : Bool)
    (P : Fin t → BlockTag) (Q : Fin m → BlockTag) (ht : 0 < t)
    (hP : ValidTagSuffix present P) (hQ : ValidTagSuffix (tagPrefixPresent P ht) Q) :
    ValidTagSuffix present (Fin.append P Q) := by
  intro r
  refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) r
  · obtain (⟨hz, hp⟩ | ⟨j, hj, hv⟩) := hP i (by simpa using hi)
    · exact Or.inl ⟨hz, hp⟩
    · exact Or.inr ⟨j.castAdd m, hj, by simpa only [Fin.append_left] using hv⟩
  · obtain (⟨hz, hp⟩ | ⟨j, hj, hv⟩) := hQ i (by simpa using hi)
    · let k : Fin t := ⟨t - 1, by omega⟩
      refine Or.inr ⟨k.castAdd m, ?_, ?_⟩
      · change t - 1 + 1 = t + i.val
        omega
      · rw [Fin.append_left]
        exact of_decide_eq_true hp
    · refine Or.inr ⟨j.natAdd t, ?_, ?_⟩
      · change t + j.val + 1 = t + i.val
        omega
      · simpa only [Fin.append_right] using hv

/-- Appending a suffix preserves validity exactly through the final prefix presence state. -/
theorem validTagSuffix_append {t m : ℕ} (present : Bool)
    (P : Fin t → BlockTag) (Q : Fin m → BlockTag) (ht : 0 < t) :
    ValidTagSuffix present (Fin.append P Q) ↔
      ValidTagSuffix present P ∧ ValidTagSuffix (tagPrefixPresent P ht) Q :=
  ⟨fun h => ⟨suffix_append_left present P Q h, suffix_append_right present P Q ht h⟩,
    fun h => suffix_append_merge present P Q ht h.1 h.2⟩

private theorem append_eq_completion {t m : ℕ} (P : Fin t → BlockTag)
    (T : Fin (t + m) → BlockTag) (hP : ∀ i : Fin t, T (i.castAdd m) = P i) :
    Fin.append P (fun j : Fin m => T (j.natAdd t)) = T := by
  funext r
  refine Fin.addCases (fun i => ?_) (fun j => ?_) r
  · rw [Fin.append_left, hP]
  · rw [Fin.append_right]

/-- Valid completions of a nonempty valid prefix are exactly its boundary-state suffixes. -/
def tagCompletionEquiv {t m : ℕ} (P : Fin t → BlockTag) (ht : 0 < t)
    (hP : IsTagWord P) :
    {T : Fin (t + m) → BlockTag // T ∈ tagExtensions P m} ≃
      {Q : Fin m → BlockTag // ValidTagSuffix (tagPrefixPresent P ht) Q} where
  toFun T := by
    obtain ⟨hword, hprefix⟩ := Finset.mem_filter.mp T.property
    have hfull := (mem_tagWords T.val).mp hword
    have h := (validTagSuffix_append false P
      (fun j : Fin m => T.val (j.natAdd t)) ht).mp
      (by rw [append_eq_completion P T.val hprefix]; exact hfull)
    exact ⟨fun j => T.val (j.natAdd t), h.2⟩
  invFun Q := ⟨Fin.append P Q.val, Finset.mem_filter.mpr
    ⟨(mem_tagWords _).mpr ((validTagSuffix_append false P Q.val ht).mpr ⟨hP, Q.property⟩),
      fun i => Fin.append_left P Q.val i⟩⟩
  left_inv T := by
    apply Subtype.ext
    exact append_eq_completion P T.val (Finset.mem_filter.mp T.property).2
  right_inv Q := by
    apply Subtype.ext
    funext j
    exact Fin.append_right P Q.val j

/-- The number of completions of a positive valid prefix depends only on its final presence. -/
theorem card_tagExtensions {t : ℕ} (P : Fin t → BlockTag) (ht : 0 < t)
    (hP : IsTagWord P) (m : ℕ) :
    (tagExtensions P m).card = extensionCount m (tagPrefixPresent P ht) := by
  calc
    _ = Fintype.card {T : Fin (t + m) → BlockTag // T ∈ tagExtensions P m} :=
      (Fintype.card_coe (tagExtensions P m)).symm
    _ = Fintype.card {Q : Fin m → BlockTag //
        ValidTagSuffix (tagPrefixPresent P ht) Q} :=
      Fintype.card_congr (tagCompletionEquiv P ht hP)
    _ = _ := by rw [Fintype.card_subtype, extensionCount]

end

end FinitaryPerm
