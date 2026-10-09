import SchubertForwardStability.Permutations.Classes.Boolean
import Mathlib.Data.List.Infix
import Mathlib.Data.Fintype.Pi

/-! # Boolean block-boundary tags

## Main definitions

`BlockTag` records absence, a block start, or continuation of a decreasing block.
`blockTag` reads these symbols from the lexicographically first reduced word.
`tagWords` is the finite set of valid tag words, and `extensionCount` counts completions.

## Implementation notes

Tag-word coordinates use `Fin m`; permutation tag indices use natural numbers
so the external indices zero and at least the ambient size have value zero.
-/

namespace FinitaryPerm

open scoped Classical

/-- The three symbols of a decreasing-block boundary word. -/
inductive BlockTag
  | zero
  | start
  | cont
  deriving DecidableEq

/-- The boundary alphabet consists of its three displayed symbols. -/
instance instFintypeBlockTag : Fintype BlockTag :=
  ⟨{.zero, .start, .cont}, by intro x; cases x <;> simp⟩

/-- A generator is present when its positive index occurs in the selected reduced word. -/
def GeneratorPresent (w : FinitaryPerm ℕ+) (t : ℕ) : Prop :=
  ∃ i : ℕ+, (i : ℕ) = t ∧ i ∈ w.lexFirstReducedWord

/-- A generator continues a decreasing block when its predecessor follows immediately. -/
def GeneratorContinues (w : FinitaryPerm ℕ+) (t : ℕ) : Prop :=
  ∃ i j : ℕ+, (i : ℕ) = t ∧ j + 1 = i ∧ [i, j].IsInfix w.lexFirstReducedWord

/-- The tag at a natural index, with zero outside the ambient generator interval. -/
noncomputable def blockTag (n : ℕ) (w : FinitaryPerm ℕ+) (t : ℕ) : BlockTag :=
  if 0 < t ∧ t < n ∧ GeneratorPresent w t then
    if GeneratorContinues w t then .cont else .start
  else .zero

/-- The block-boundary vector in the first `n-1` generator positions. -/
noncomputable def booleanTags (n : ℕ) (w : FinitaryPerm ℕ+) :
    Fin (n - 1) → BlockTag := fun i => blockTag n w (i.val + 1)

/-- A valid suffix permits continuation only after a present preceding symbol. -/
def ValidTagSuffix {m : ℕ} (present : Bool) (T : Fin m → BlockTag) : Prop :=
  ∀ i, T i = .cont → (i.val = 0 ∧ present = true) ∨
    ∃ j : Fin m, j.val + 1 = i.val ∧ T j ≠ .zero

/-- A valid tag word begins after the absent external symbol. -/
def IsTagWord {m : ℕ} (T : Fin m → BlockTag) : Prop := ValidTagSuffix false T

/-- All valid boundary-symbol words of length `m`, including the unique empty word. -/
noncomputable def tagWords (m : ℕ) : Finset (Fin m → BlockTag) :=
  Finset.univ.filter IsTagWord

/-- Tag-word membership is exactly the local continuation condition. -/
@[simp]
theorem mem_tagWords {m : ℕ} (T : Fin m → BlockTag) :
    T ∈ tagWords m ↔ IsTagWord T := by
  simp only [tagWords, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The tag words completing a positive-length prefix by `m` symbols. -/
noncomputable def tagExtensions {t : ℕ} (P : Fin t → BlockTag) (m : ℕ) :
    Finset (Fin (t + m) → BlockTag) :=
  (tagWords (t + m)).filter fun T => ∀ i : Fin t, T (Fin.castAdd m i) = P i

/-- The number of suffixes of length `m` after an absent or present symbol. -/
noncomputable def extensionCount (m : ℕ) (present : Bool) : ℕ :=
  (Finset.univ.filter (ValidTagSuffix (m := m) present)).card

/-- No continuation symbol occurs at the external zero index. -/
@[simp]
theorem blockTag_zero (n : ℕ) (w : FinitaryPerm ℕ+) : blockTag n w 0 = .zero := by
  simp only [blockTag, Nat.lt_irrefl, false_and, ↓reduceIte]

/-- All indices at or beyond the ambient size have zero tag. -/
theorem blockTag_above {n t : ℕ} (w : FinitaryPerm ℕ+) (ht : n ≤ t) :
    blockTag n w t = .zero := by
  simp only [blockTag, not_lt_of_ge ht, and_false, false_and, ↓reduceIte]

/-- The all-zero vector is a valid tag word. -/
theorem zero_isTagWord (m : ℕ) : IsTagWord (fun _ : Fin m => .zero) := by
  intro i hi
  cases hi

/-- Every tag-word family, including the empty one, is nonempty. -/
theorem tagWords_nonempty (m : ℕ) : (tagWords m).Nonempty :=
  ⟨fun _ => .zero, (mem_tagWords _).mpr (zero_isTagWord m)⟩

/-- There is one empty suffix for either boundary state. -/
@[simp]
theorem extensionCount_zero (present : Bool) : extensionCount 0 present = 1 := by
  have h : ∀ T : Fin 0 → BlockTag, ValidTagSuffix present T := fun _ i => Fin.elim0 i
  rw [extensionCount, Finset.filter_true_of_mem fun _ _ => h _, Finset.card_univ]
  exact Fintype.card_unique

end FinitaryPerm
