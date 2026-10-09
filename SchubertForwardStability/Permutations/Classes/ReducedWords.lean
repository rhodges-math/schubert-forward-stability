import SchubertForwardStability.Permutations.Statistics.Inversions
import SchubertForwardStability.TypeA.Permutations.AdjacentLength
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Adjacent words and reduced expressions

## Main definitions

* `simpleTransposition`: the transposition of positions `i` and `i + 1`.
* `wordProduct`: the product of adjacent transpositions in displayed order.
* `IsReducedWord`, `IsReducedWordIn`: reduced expressions, with an optional ambient bound.

## Main results

`exists_reducedWordIn` transports finite reduced sorting words to positive-index expressions.

## Implementation notes

Multiplication composes functions. Letters are positive integers, and right multiplication
exchanges positions. A reduced word has length equal to the inversion count.
-/

namespace FinitaryPerm

/-- The adjacent transposition at the positive position `i`. -/
def simpleTransposition (i : ℕ+) : FinitaryPerm ℕ+ := swap i (i + 1)

/-- An adjacent transposition sends its left position to its right position. -/
@[simp]
theorem simpleTransposition_apply_left (i : ℕ+) : simpleTransposition i i = i + 1 :=
  swap_apply_left _ _

/-- An adjacent transposition sends its right position to its left position. -/
@[simp]
theorem simpleTransposition_apply_right (i : ℕ+) : simpleTransposition i (i + 1) = i :=
  swap_apply_right _ _

/-- The permutation represented by a word of adjacent transpositions in displayed order. -/
def wordProduct (word : List ℕ+) : FinitaryPerm ℕ+ := (word.map simpleTransposition).prod

/-- The empty word represents identity. -/
@[simp]
theorem wordProduct_nil : wordProduct [] = 1 := rfl

/-- Prepending a letter multiplies its transposition on the left of the remaining product. -/
@[simp]
theorem wordProduct_cons (i : ℕ+) (word : List ℕ+) :
    wordProduct (i :: word) = simpleTransposition i * wordProduct word := rfl

/-- Concatenating words multiplies their represented permutations. -/
theorem wordProduct_append (a b : List ℕ+) :
    wordProduct (a ++ b) = wordProduct a * wordProduct b := by
  simp only [wordProduct, List.map_append, List.prod_append]

/-- A reduced word represents the permutation and has its inversion length. -/
def IsReducedWord (w : FinitaryPerm ℕ+) (word : List ℕ+) : Prop :=
  wordProduct word = w ∧ word.length = w.length

/-- An ambient reduced word has every letter strictly below its ambient size. -/
def IsReducedWordIn (n : ℕ) (w : FinitaryPerm ℕ+) (word : List ℕ+) : Prop :=
  IsReducedWord w word ∧ ∀ i ∈ word, (i : ℕ) < n

/-- The empty word is reduced for identity in any ambient size. -/
theorem isReducedWordIn_one (n : ℕ) : IsReducedWordIn n 1 [] := by
  refine ⟨⟨wordProduct_nil, length_one.symm⟩, ?_⟩
  intro i hi
  exact False.elim (List.not_mem_nil hi)

/-- The positive-index letter of a finite adjacent transposition is its left position plus one. -/
def adjacentLetter {n : ℕ} (a : Schubert.FinPermutation.AdjacentPosition n) : ℕ+ :=
  ⟨a.left.val + 1, Nat.zero_lt_succ _⟩

/-- Finite extension sends an adjacent transposition to its positive-index transposition. -/
theorem ofFinite_adjacent {n : ℕ} (a : Schubert.FinPermutation.AdjacentPosition n) :
    ofFinite n (Schubert.FinPermutation.adjacentTransposition a) =
      simpleTransposition (adjacentLetter a) := by
  rw [Schubert.FinPermutation.adjacentTransposition, ofFinite_swap]
  change swap (adjacentLetter a) (positiveIndex n a.right).val =
    swap (adjacentLetter a) (adjacentLetter a + 1)
  have h : (positiveIndex n a.right).val = adjacentLetter a + 1 := PNat.eq rfl
  rw [h]

/-- Finite extension intertwines right adjacent words with their positive letter products. -/
theorem ofFinite_apply_adjacentWord {n : ℕ}
    (word : List (Schubert.FinPermutation.AdjacentPosition n)) (g : Equiv.Perm (Fin n)) :
    ofFinite n (Schubert.FinPermutation.applyRightAdjacentWord word g) =
      ofFinite n g * wordProduct (word.map adjacentLetter) := by
  induction word generalizing g with
  | nil => rw [Schubert.FinPermutation.applyRightAdjacentWord_nil, List.map_nil,
      wordProduct_nil, mul_one]
  | cons a word ih =>
    rw [Schubert.FinPermutation.applyRightAdjacentWord_cons, ih]
    change ofFinite n (g * Schubert.FinPermutation.adjacentTransposition a) *
      wordProduct (word.map adjacentLetter) = _
    rw [ofFinite_mul, ofFinite_adjacent, List.map_cons, wordProduct_cons, mul_assoc]

/-- Every supported permutation has a reduced word using only letters below that bound. -/
theorem exists_reducedWordIn {n : ℕ} (w : FinitaryPerm ℕ+) (hw : IsSupported n w) :
    ∃ word, IsReducedWordIn n w word := by
  let g := toFinite n w hw
  let word := Schubert.FinPermutation.reducedWordToRefl g.symm
  have hs : Schubert.FinPermutation.applyRightAdjacentWord word (Equiv.refl (Fin n)) = g :=
    Schubert.FinPermutation.applyRightAdjacentWord_refl_eq_symm_of_eq_refl
      (Schubert.FinPermutation.apply_reducedWordToRefl g.symm)
  refine ⟨word.map adjacentLetter, ⟨?_, ?_⟩, ?_⟩
  · have h := ofFinite_apply_adjacentWord word (Equiv.refl (Fin n))
    rw [hs, ← Equiv.Perm.one_def, ofFinite_one, one_mul] at h
    exact h.symm.trans (ofFinite_toFinite n w hw)
  · rw [List.length_map, Schubert.FinPermutation.length_reducedWordToRefl,
      Schubert.FinPermutation.length_symm]
    exact (length_ofFinite n g).symm.trans (congrArg length (ofFinite_toFinite n w hw))
  · intro i hi
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hi
    exact a.hasRight

end FinitaryPerm
