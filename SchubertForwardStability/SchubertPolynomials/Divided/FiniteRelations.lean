import SchubertForwardStability.SchubertPolynomials.Divided.Naturality
import SchubertForwardStability.TypeA.Polynomials.DividedDifferenceRelations

/-! # Finite divided-difference relations over commutative rings

## Main definitions

* `finiteDividedDifference`: the generic operator at a finite adjacent position.

## Main results

The finite integral operator agrees with the quotient-defined operator. Its braid
and distant-commutation relations extend to every commutative coefficient ring.

## Implementation notes

Coefficient-one monomials are images of integral monomials under the coefficient
map. Linearity then extends the integral identities to all polynomials.
-/

namespace SchubertPolynomial

open Schubert.FinPermutation

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

/-- Divided difference at a finite adjacent position, over any commutative ring. -/
noncomputable abbrev finiteDividedDifference (R : Type*) [CommRing R]
    (a : AdjacentPosition n) : MvPolynomial (Fin n) R →ₗ[R] MvPolynomial (Fin n) R :=
  variableDividedDifference R a.left a.right

private theorem integral_swap_eq (a : AdjacentPosition n) (p : MvPolynomial (Fin n) ℤ) :
    Schubert.adjacentVariableSwap a p = variableSwap ℤ a.left a.right p := by
  classical
  apply congrArg (fun s : Equiv.Perm (Fin n) => MvPolynomial.renameEquiv ℤ s p)
  ext k
  simp only [Schubert.FinPermutation.adjacentTransposition, Equiv.swap_apply_def]
  split_ifs <;> rfl

/-- The generic integral operator equals the finite type-A integral operator. -/
theorem finiteDividedDifference_int (a : AdjacentPosition n)
    (p : MvPolynomial (Fin n) ℤ) :
    finiteDividedDifference ℤ a p = Schubert.adjacentDividedDifference a p := by
  apply (variableDividedDifference_eq_iff a.left_ne_right _ _).mpr
  simpa only [integral_swap_eq] using Schubert.adjacentRoot_mul_adjacentDividedDifference a p

/-- Finite divided differences commute with any coefficient homomorphism. -/
theorem finiteDividedDifference_map (f : R →+* S) (a : AdjacentPosition n)
    (p : MvPolynomial (Fin n) R) :
    finiteDividedDifference S a (MvPolynomial.map f p) =
      MvPolynomial.map f (finiteDividedDifference R a p) :=
  variableDividedDifference_map f a.left_ne_right p

/-- Consecutive finite divided differences satisfy the three-letter braid relation. -/
theorem finiteDividedDifference_braid (a b : AdjacentPosition n) (hab : a.right = b.left)
    (p : MvPolynomial (Fin n) R) :
    finiteDividedDifference R a (finiteDividedDifference R b (finiteDividedDifference R a p)) =
      finiteDividedDifference R b
        (finiteDividedDifference R a (finiteDividedDifference R b p)) := by
  have hlinear : (finiteDividedDifference R a).comp
      ((finiteDividedDifference R b).comp (finiteDividedDifference R a)) =
      (finiteDividedDifference R b).comp
        ((finiteDividedDifference R a).comp (finiteDividedDifference R b)) := by
    apply (MvPolynomial.basisMonomials (Fin n) R).ext
    intro m
    have hint := Schubert.adjacentDividedDifference_braid a b hab
      (MvPolynomial.monomial m (1 : ℤ))
    simp only [← finiteDividedDifference_int] at hint
    have hmap := congrArg (MvPolynomial.map (Int.castRingHom R)) hint
    simpa only [← finiteDividedDifference_map, MvPolynomial.map_monomial,
      map_one, LinearMap.comp_apply, MvPolynomial.coe_basisMonomials] using hmap
  exact LinearMap.congr_fun hlinear p

/-- Finite divided differences at separated adjacent positions commute. -/
theorem finiteDividedDifference_commute (a b : AdjacentPosition n)
    (hgap : Schubert.SeparatedAdjacentPositions a b) (p : MvPolynomial (Fin n) R) :
    finiteDividedDifference R a (finiteDividedDifference R b p) =
      finiteDividedDifference R b (finiteDividedDifference R a p) := by
  have hlinear : (finiteDividedDifference R a).comp (finiteDividedDifference R b) =
      (finiteDividedDifference R b).comp (finiteDividedDifference R a) := by
    apply (MvPolynomial.basisMonomials (Fin n) R).ext
    intro m
    have hint := Schubert.adjacentDividedDifference_commute_of_separated a b hgap
      (MvPolynomial.monomial m (1 : ℤ))
    simp only [← finiteDividedDifference_int] at hint
    have hmap := congrArg (MvPolynomial.map (Int.castRingHom R)) hint
    simpa only [← finiteDividedDifference_map, MvPolynomial.map_monomial,
      map_one, LinearMap.comp_apply, MvPolynomial.coe_basisMonomials] using hmap
  exact LinearMap.congr_fun hlinear p

end SchubertPolynomial
