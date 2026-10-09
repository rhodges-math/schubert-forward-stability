import SchubertForwardStability.SchubertPolynomials.Divided.FiniteRelations
import SchubertForwardStability.Permutations.Finitary.Finite
import Mathlib.Algebra.MvPolynomial.Variables

/-! # Initial finite variable intervals

## Main definitions

* `initialRename`: embed finite variables in the initial positive interval.

## Main results

Every polynomial with positive-indexed variables is supported in a sufficiently
large initial interval. The embedding intertwines adjacent divided differences.

## Implementation notes

Finite variable zero corresponds to positive variable one, using `positiveIndex`.
The interval can be chosen above any prescribed natural-number bound.
-/

namespace SchubertPolynomial

variable {R : Type*} [CommRing R]

/-- Embed finite polynomial variables as positive positions one through n. -/
noncomputable abbrev initialRename (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial ℕ+ R :=
  MvPolynomial.rename fun k => (FinitaryPerm.positiveIndex n k).val

/-- The initial-interval polynomial embedding is injective. -/
theorem initialRename_injective (n : ℕ) : Function.Injective (initialRename R n) :=
  MvPolynomial.rename_injective _ fun _ _ h =>
    (FinitaryPerm.positiveIndex n).injective (Subtype.ext h)

/-- Every polynomial comes from a finite initial interval above any prescribed bound. -/
theorem exists_initialRename (p : MvPolynomial ℕ+ R) (bound : ℕ) :
    ∃ n, bound ≤ n ∧ ∃ q : MvPolynomial (Fin n) R, initialRename R n q = p := by
  classical
  let n := max bound (p.vars.sup fun j => (j : ℕ))
  refine ⟨n, le_max_left _ _, ?_⟩
  apply MvPolynomial.exists_rename_eq_of_vars_subset_range p
    (fun k => (FinitaryPerm.positiveIndex n k).val)
    (fun _ _ h => (FinitaryPerm.positiveIndex n).injective (Subtype.ext h))
  intro j hj
  have hjn : (j : ℕ) ≤ n := (Finset.le_sup hj).trans (le_max_right _ _)
  refine ⟨(FinitaryPerm.positiveIndex n).symm ⟨j, hjn⟩, ?_⟩
  exact congrArg Subtype.val ((FinitaryPerm.positiveIndex n).apply_symm_apply ⟨j, hjn⟩)

/-- Initial variable embeddings intertwine the finite and positive adjacent operators. -/
theorem initialRename_dividedDifference {n : ℕ}
    (a : Schubert.FinPermutation.AdjacentPosition n) (p : MvPolynomial (Fin n) R) :
    dividedDifference R (FinitaryPerm.positiveIndex n a.left).val (initialRename R n p) =
      initialRename R n (finiteDividedDifference R a p) := by
  let f : Fin n → ℕ+ := fun k => (FinitaryPerm.positiveIndex n k).val
  have hf : Function.Injective f := fun _ _ h =>
    (FinitaryPerm.positiveIndex n).injective (Subtype.ext h)
  have hright : f a.right = f a.left + 1 := by
    apply PNat.eq
    rfl
  change variableDividedDifference R (f a.left) (f a.left + 1) (MvPolynomial.rename f p) =
    MvPolynomial.rename f (variableDividedDifference R a.left a.right p)
  rw [← hright]
  exact variableDividedDifference_rename f hf a.left_ne_right p

end SchubertPolynomial
