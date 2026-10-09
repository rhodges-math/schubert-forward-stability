import SchubertForwardStability.SchubertPolynomials.Basis.ArtinCoordinates
import SchubertForwardStability.SchubertPolynomials.Basis.ArtinMonomials
import Mathlib.Data.Fintype.EquivFin

/-!
# Equal finite index cardinalities

## Main definitions

* `artinIndexEquiv` matches the finite Artin exponent index type with finite permutations.
* `artinPermutationBasis` reindexes the monomial basis by finite permutations.

## Implementation notes

The equivalence comes from the equality of the two factorial cardinalities; it is not
the Lehmer-code map.
-/

namespace SchubertPolynomial

noncomputable section

/-- The finite Artin exponent index type and the finite permutation index type have
an equivalence because both have cardinality `n!`. -/
def artinIndexEquiv (n : ℕ) :
    {a : ℕ+ →₀ ℕ // IsArtinExponent n a} ≃ Equiv.Perm (Fin n) :=
  Fintype.equivOfCardEq (by rw [card_artinExponent, Fintype.card_perm, Fintype.card_fin])

/-- The Artin monomial basis reindexed by the equally large finite permutation type. -/
def artinPermutationBasis (R : Type*) [CommSemiring R] (n : ℕ) :
    Module.Basis (Equiv.Perm (Fin n)) R (artinSpan R n) :=
  (artinMonomialBasis R n).reindex (artinIndexEquiv n)

end

end SchubertPolynomial
