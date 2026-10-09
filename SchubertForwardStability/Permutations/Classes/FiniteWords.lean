import SchubertForwardStability.Permutations.Classes.ReducedWords

/-! # Finite realization of bounded positive words

## Main results

Every positive word with letters below n is the image of a finite adjacent word.
The finite word's identity-started permutation extends to the positive word product.

## Implementation notes

The finite adjacent position ending at positive letter i has left index i-1.
The empty word is included at every ambient size, including zero.
-/

namespace FinitaryPerm

open Schubert.FinPermutation

/-- Every word bounded by n is a finite adjacent word under positive reindexing. -/
theorem exists_finiteAdjacentWord {n : ℕ} (word : List ℕ+)
    (hbound : ∀ i ∈ word, (i : ℕ) < n) :
    ∃ finiteWord : List (AdjacentPosition n), finiteWord.map adjacentLetter = word := by
  induction word with
  | nil => exact ⟨[], rfl⟩
  | cons i word ih =>
    have hi : (i : ℕ) < n := hbound i (List.mem_cons_self)
    let a := AdjacentPosition.endingAt ⟨(i : ℕ), hi⟩ i.pos
    have ha : adjacentLetter a = i := by
      apply PNat.eq
      change (i : ℕ) - 1 + 1 = (i : ℕ)
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt i.pos)
    obtain ⟨finiteWord, hword⟩ := ih (fun j hj => hbound j (List.mem_cons_of_mem i hj))
    refine ⟨a :: finiteWord, ?_⟩
    rw [List.map_cons, ha, hword]

/-- A finite word's identity-started permutation extends to its positive word product. -/
theorem ofFinite_wordProduct {n : ℕ} (word : List (AdjacentPosition n)) :
    ofFinite n (applyRightAdjacentWord word (Equiv.refl (Fin n))) =
      wordProduct (word.map adjacentLetter) := by
  rw [ofFinite_apply_adjacentWord, ← Equiv.Perm.one_def, ofFinite_one, one_mul]

end FinitaryPerm
