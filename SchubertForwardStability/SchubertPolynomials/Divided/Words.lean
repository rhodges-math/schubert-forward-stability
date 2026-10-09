import SchubertForwardStability.SchubertPolynomials.Divided.Relations
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Polynomial divided differences along words

## Main definitions

* `wordDividedDifference`: compose adjacent operators in displayed word order.

## Main results

Concatenation corresponds to composition. Braid moves and distant commutations
preserve the operator in every prefix and suffix, while adjacent repeated letters
give the zero operator. Coefficient maps commute with every word operator.

## Implementation notes

The leftmost letter acts last on the polynomial, matching multiplication of
endomorphisms by composition. Word letters are positive variable indices.
-/

namespace SchubertPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The R-linear divided-difference operator associated with a displayed adjacent word. -/
noncomputable def wordDividedDifference (R : Type*) [CommRing R] (word : List ℕ+) :
    Module.End R (MvPolynomial ℕ+ R) := (word.map (dividedDifference R)).prod

/-- The empty divided-difference word acts as identity. -/
@[simp]
theorem wordDividedDifference_nil : wordDividedDifference R [] = LinearMap.id := rfl

/-- The first letter acts on the result of the remaining word. -/
@[simp]
theorem wordDividedDifference_cons (i : ℕ+) (word : List ℕ+) :
    wordDividedDifference R (i :: word) =
      (dividedDifference R i).comp (wordDividedDifference R word) := rfl

/-- Concatenating words composes their divided-difference operators. -/
theorem wordDividedDifference_append (left right : List ℕ+) :
    wordDividedDifference R (left ++ right) =
      (wordDividedDifference R left).comp (wordDividedDifference R right) := by
  simp only [wordDividedDifference, List.map_append, List.prod_append, Module.End.mul_eq_comp]

/-- Coefficient homomorphisms commute with divided differences along every word. -/
theorem wordDividedDifference_map (f : R →+* S) (word : List ℕ+)
    (p : MvPolynomial ℕ+ R) :
    wordDividedDifference S word (MvPolynomial.map f p) =
      MvPolynomial.map f (wordDividedDifference R word p) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    simp only [wordDividedDifference_cons, LinearMap.comp_apply]
    rw [ih, dividedDifference_map]

/-- A three-letter braid move preserves a word operator in any prefix and suffix. -/
theorem wordDividedDifference_braid (pre suf : List ℕ+) (i : ℕ+) :
    wordDividedDifference R (pre ++ [i, i + 1, i] ++ suf) =
      wordDividedDifference R (pre ++ [i + 1, i, i + 1] ++ suf) := by
  ext p
  simp only [wordDividedDifference_append, wordDividedDifference_cons,
    wordDividedDifference_nil, LinearMap.comp_apply, LinearMap.id_apply]
  rw [dividedDifference_braid]

/-- A distant commutation preserves a word operator in any prefix and suffix. -/
theorem wordDividedDifference_commute (pre suf : List ℕ+) (i j : ℕ+)
    (hgap : i + 1 < j ∨ j + 1 < i) :
    wordDividedDifference R (pre ++ [i, j] ++ suf) =
      wordDividedDifference R (pre ++ [j, i] ++ suf) := by
  ext p
  simp only [wordDividedDifference_append, wordDividedDifference_cons,
    wordDividedDifference_nil, LinearMap.comp_apply, LinearMap.id_apply]
  rw [dividedDifference_commute i j hgap]

/-- Adjacent repeated letters make a word's divided-difference operator zero. -/
theorem wordDividedDifference_repeat (pre suf : List ℕ+) (i : ℕ+) :
    wordDividedDifference R (pre ++ [i, i] ++ suf) = 0 := by
  ext p
  simp only [wordDividedDifference_append, wordDividedDifference_cons,
    wordDividedDifference_nil, LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.zero_apply, dividedDifference_sq, map_zero]

end SchubertPolynomial
