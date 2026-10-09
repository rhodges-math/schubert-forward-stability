import SchubertForwardStability.SchubertPolynomials.Divided.Multiplication
import SchubertForwardStability.SchubertPolynomials.Stability.Staircase
import SchubertForwardStability.Permutations.Finitary.Relative

/-! # The divided-difference construction of Schubert polynomials

## Main definitions

* `ambientSchubert`: apply the inverse-relative longest operator to the staircase.
* `schubert`: use the least positive support bound as the ambient size.

## Main results

The defining formula agrees with every reduced expression for its operator.
Coefficient homomorphisms preserve these polynomials. The identity polynomial is
one, and the ambient longest polynomial is the staircase monomial.

## Implementation notes

The permutation and variable carriers are positive-indexed. Polynomial operators
compose in displayed reduced-word order. Coefficient rings are arbitrary CommRing.

## References

L. Manivel, *Symmetric functions, Schubert polynomials and degeneracy loci*, Sections 2.3--2.5.
-/

namespace SchubertPolynomial

/-- The ambient divided-difference formula for the Schubert polynomial. -/
noncomputable def ambientSchubert (R : Type*) [CommRing R] (n : ℕ)
    (w : FinitaryPerm ℕ+) : MvPolynomial ℕ+ R :=
  permutationDividedDifference R (w⁻¹ * FinitaryPerm.longestElement n) (staircaseMonomial R n)

/-- The Schubert polynomial constructed at the permutation's least positive support bound. -/
noncomputable def schubert (R : Type*) [CommRing R] (w : FinitaryPerm ℕ+) :
    MvPolynomial ℕ+ R := ambientSchubert R w.forwardStability w

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Every reduced relative expression evaluates the ambient Schubert formula. -/
theorem ambientSchubert_eq_word (n : ℕ) (w : FinitaryPerm ℕ+) (word : List ℕ+)
    (hword : FinitaryPerm.IsReducedWord (w⁻¹ * FinitaryPerm.longestElement n) word) :
    ambientSchubert R n w = wordDividedDifference R word (staircaseMonomial R n) := by
  rw [ambientSchubert, permutationDividedDifference_eq word hword]

/-- The ambient longest Schubert polynomial is its staircase monomial. -/
theorem ambientSchubert_longest (n : ℕ) :
    ambientSchubert R n (FinitaryPerm.longestElement n) = staircaseMonomial R n := by
  rw [ambientSchubert, FinitaryPerm.longestElement_inv, FinitaryPerm.longestElement_mul_self,
    permutationDividedDifference_one, LinearMap.id_apply]

/-- Identity has ambient polynomial one at size zero. -/
theorem ambientSchubert_zero : ambientSchubert R 0 (1 : FinitaryPerm ℕ+) = 1 := by
  rw [ambientSchubert, inv_one, one_mul, FinitaryPerm.longestElement_zero,
    permutationDividedDifference_one, LinearMap.id_apply, staircaseMonomial_zero]

/-- The identity Schubert polynomial is one. -/
@[simp]
theorem schubert_one : schubert R (1 : FinitaryPerm ℕ+) = 1 := by
  rw [schubert, FinitaryPerm.forwardStability_one, ambientSchubert, inv_one, one_mul,
    FinitaryPerm.longestElement_one, permutationDividedDifference_one,
    LinearMap.id_apply, staircaseMonomial_one]

/-- Coefficient homomorphisms preserve the ambient Schubert construction. -/
theorem ambientSchubert_map (f : R →+* S) (n : ℕ) (w : FinitaryPerm ℕ+) :
    MvPolynomial.map f (ambientSchubert R n w) = ambientSchubert S n w := by
  rw [ambientSchubert, ambientSchubert, ← staircaseMonomial_map f n,
    permutationDividedDifference_map]

/-- Coefficient homomorphisms preserve Schubert polynomials. -/
theorem schubert_map (f : R →+* S) (w : FinitaryPerm ℕ+) :
    MvPolynomial.map f (schubert R w) = schubert S w :=
  ambientSchubert_map f w.forwardStability w

end SchubertPolynomial
