import SchubertForwardStability.Permutations.Classes.ReducedWords
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Max

/-! # Finite reduced-word enumeration

## Main definitions

* `boundedWords`: all words of a fixed length in a bounded positive alphabet.
* `reducedWordsIn`: ambient reduced expressions of a given permutation.
* `lexFirstReducedWord`: the least reduced expression with letters below the forward
  stability.

## Implementation notes

Lexicographic order is Mathlib's linear order on lists. Existence of reduced words
supplies nonemptiness before the finite minimum is taken.
-/

namespace FinitaryPerm

open scoped Classical

/-- All length-`l` words with positive letters strictly below `n`. -/
noncomputable def boundedWords (n l : ℕ) : Finset (List ℕ+) :=
  (Finset.univ : Finset (Fin l → ↥(positions (n - 1)))).image
    fun f => List.ofFn fun i => (f i).val

/-- Bounded-word membership is the exact length and letter-bound condition. -/
@[simp]
theorem mem_boundedWords (n l : ℕ) (word : List ℕ+) :
    word ∈ boundedWords n l ↔ word.length = l ∧ ∀ i ∈ word, (i : ℕ) < n := by
  constructor
  · intro h
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp h
    refine ⟨List.length_ofFn, ?_⟩
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    have hb := (mem_positions (n - 1) (f j).val).mp (f j).property
    have hp := PNat.pos (f j).val
    omega
  · rintro ⟨hl, hb⟩
    let f : Fin l → ↥(positions (n - 1)) := fun i =>
      ⟨word.get (Fin.cast hl.symm i), (mem_positions _ _).mpr
        (Nat.le_sub_one_of_lt (hb _ (List.get_mem _ _)))⟩
    refine Finset.mem_image.mpr ⟨f, Finset.mem_univ _, ?_⟩
    exact (List.ofFn_congr hl (List.get word)).symm.trans (List.ofFn_get word)

/-- The finite set of reduced words of `w` with letters below `n`. -/
noncomputable def reducedWordsIn (n : ℕ) (w : FinitaryPerm ℕ+) : Finset (List ℕ+) :=
  (boundedWords n w.length).filter fun word => wordProduct word = w

/-- Membership in the finite reduced-word set is the ambient reduced-word predicate. -/
@[simp]
theorem mem_reducedWordsIn (n : ℕ) (w : FinitaryPerm ℕ+) (word : List ℕ+) :
    word ∈ reducedWordsIn n w ↔ IsReducedWordIn n w word := by
  rw [reducedWordsIn, Finset.mem_filter, mem_boundedWords]
  constructor
  · rintro ⟨⟨hl, hb⟩, hp⟩
    exact ⟨⟨hp, hl⟩, hb⟩
  · rintro ⟨⟨hp, hl⟩, hb⟩
    exact ⟨⟨hl, hb⟩, hp⟩

/-- A support bound ensures that the finite reduced-word set is nonempty. -/
theorem reducedWordsIn_nonempty {n : ℕ} (w : FinitaryPerm ℕ+) (hw : IsSupported n w) :
    (reducedWordsIn n w).Nonempty := by
  obtain ⟨word, hword⟩ := exists_reducedWordIn w hw
  exact ⟨word, (mem_reducedWordsIn n w word).mpr hword⟩

/-- The lexicographically least reduced word with letters below the forward stability. -/
noncomputable def lexFirstReducedWord (w : FinitaryPerm ℕ+) : List ℕ+ :=
  (reducedWordsIn w.forwardStability w).min'
    (reducedWordsIn_nonempty w w.isSupported_forwardStability)

/-- The lexicographic selector returns a reduced word with letters below the forward
stability. -/
theorem isReducedWordIn_lexFirst (w : FinitaryPerm ℕ+) :
    IsReducedWordIn w.forwardStability w w.lexFirstReducedWord :=
  (mem_reducedWordsIn _ _ _).mp (Finset.min'_mem _ _)

/-- The selected word is no larger than any reduced word with letters below the forward
stability. -/
theorem lexFirstReducedWord_le (w : FinitaryPerm ℕ+) (word : List ℕ+)
    (hword : IsReducedWordIn w.forwardStability w word) : w.lexFirstReducedWord ≤ word :=
  Finset.min'_le _ _ ((mem_reducedWordsIn _ _ _).mpr hword)

/-- The selected reduced word of identity is empty. -/
@[simp]
theorem lexFirstReducedWord_one : lexFirstReducedWord (1 : FinitaryPerm ℕ+) = [] := by
  apply List.eq_nil_of_length_eq_zero
  exact (isReducedWordIn_lexFirst 1).1.2.trans length_one

end FinitaryPerm
