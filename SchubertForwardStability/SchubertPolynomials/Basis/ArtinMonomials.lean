import SchubertForwardStability.SchubertPolynomials.Basis.ArtinSpan
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# A monomial basis of the Artin span

## Main definitions

* `artinMonomialBasis R n` is the basis indexed by Artin-bounded exponent vectors.

## Main results

The basis vectors are coefficient-one monomials, and their coordinates are polynomial coefficients.

## Implementation notes

The basis is constructed from the coefficient linear equivalence on the supported submodule.
It is defined over any commutative semiring, without a nontriviality assumption.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

variable {R : Type*} [CommSemiring R]

/-- The coefficient-one monomial basis of the Artin span. -/
def artinMonomialBasis (R : Type*) [CommSemiring R] (n : ℕ) :
    Module.Basis {a : ℕ+ →₀ ℕ // IsArtinExponent n a} R (artinSpan R n) where
  repr := AddMonoidAlgebra.supportedEquivFinsupp {a | IsArtinExponent n a}

/-- The coordinate of a polynomial at a bounded exponent is its polynomial coefficient. -/
@[simp] theorem artinMonomialBasis_repr (n : ℕ) (p : artinSpan R n)
    (a : {a : ℕ+ →₀ ℕ // IsArtinExponent n a}) :
    (artinMonomialBasis R n).repr p a = p.1.coeff a.1 := rfl

/-- Every Artin monomial basis vector is the coefficient-one monomial of its exponent. -/
@[simp] theorem artinMonomialBasis_apply (n : ℕ)
    (a : {a : ℕ+ →₀ ℕ // IsArtinExponent n a}) :
    (artinMonomialBasis R n a : MvPolynomial ℕ+ R) = MvPolynomial.monomial a.1 1 := by
  change AddMonoidAlgebra.ofCoeff
      ((Finsupp.supportedEquivFinsupp {a | IsArtinExponent n a}).symm
        (Finsupp.single a (1 : R)) : (ℕ+ →₀ ℕ) →₀ R) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

end

end SchubertPolynomial
