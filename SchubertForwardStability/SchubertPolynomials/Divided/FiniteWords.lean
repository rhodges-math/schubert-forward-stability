import SchubertForwardStability.SchubertPolynomials.Divided.Words
import SchubertForwardStability.Permutations.Classes.SortingEvaluation

/-! # Finite reduced-word divided differences

## Main definitions

* `finiteWordDividedDifference`: the linear operator associated with a finite adjacent word.

## Main results

Reduced words for the same finite permutation give the same operator over every
commutative ring. Finite variable embeddings intertwine the associated word operators.

## Implementation notes

The proof specializes monoid-valued sorting independence to linear endomorphisms.
Finite letter zero corresponds to positive variable index one.
-/

namespace SchubertPolynomial

open Schubert (FinPermutation)
open Schubert.FinPermutation

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The linear divided-difference operator of a finite adjacent word in displayed order. -/
noncomputable def finiteWordDividedDifference (R : Type*) [CommRing R]
    (word : List (AdjacentPosition n)) : Module.End R (MvPolynomial (Fin n) R) :=
  (word.map (finiteDividedDifference R)).prod

/-- The empty finite word acts as identity. -/
@[simp]
theorem finiteWordDividedDifference_nil :
    finiteWordDividedDifference R ([] : List (AdjacentPosition n)) = LinearMap.id := rfl

/-- A finite word's first operator acts on the result of its remaining letters. -/
@[simp]
theorem finiteWordDividedDifference_cons (a : AdjacentPosition n)
    (word : List (AdjacentPosition n)) :
    finiteWordDividedDifference R (a :: word) =
      (finiteDividedDifference R a).comp (finiteWordDividedDifference R word) := rfl

/-- Concatenation composes finite divided-difference words. -/
theorem finiteWordDividedDifference_append (left right : List (AdjacentPosition n)) :
    finiteWordDividedDifference R (left ++ right) =
      (finiteWordDividedDifference R left).comp (finiteWordDividedDifference R right) := by
  simp only [finiteWordDividedDifference, List.map_append, List.prod_append,
    Module.End.mul_eq_comp]

/-- Finite divided differences respect the type-A monoid braid and commutation relations. -/
theorem finiteDividedDifference_relations :
    FinitaryPerm.SatisfiesAdjacentRelations
      (finiteDividedDifference R : AdjacentPosition n → Module.End R (MvPolynomial (Fin n) R)) := by
  constructor
  · intro a b hab
    apply LinearMap.ext
    intro p
    exact finiteDividedDifference_braid a b hab p
  · intro a b hgap
    apply LinearMap.ext
    intro p
    exact finiteDividedDifference_commute a b hgap p

/-- Finite reduced words representing the same permutation give equal polynomial operators. -/
theorem finiteWordDividedDifference_eq (w : FinPermutation n)
    (u v : List (AdjacentPosition n))
    (hsu : applyRightAdjacentWord u (Equiv.refl (Fin n)) = w)
    (hsv : applyRightAdjacentWord v (Equiv.refl (Fin n)) = w)
    (hlu : u.length = w.length) (hlv : v.length = w.length) :
    finiteWordDividedDifference R u = finiteWordDividedDifference R v :=
  FinitaryPerm.reducedWord_eval_eq (finiteDividedDifference R)
    finiteDividedDifference_relations w u v hsu hsv hlu hlv

/-- Initial variable embeddings intertwine finite words with their positive-index words. -/
theorem initialRename_wordDividedDifference (word : List (AdjacentPosition n))
    (p : MvPolynomial (Fin n) R) :
    wordDividedDifference R (word.map fun a => (FinitaryPerm.positiveIndex n a.left).val)
      (initialRename R n p) = initialRename R n (finiteWordDividedDifference R word p) := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    simp only [List.map_cons, wordDividedDifference_cons, finiteWordDividedDifference_cons,
      LinearMap.comp_apply]
    rw [ih, initialRename_dividedDifference]

end SchubertPolynomial
