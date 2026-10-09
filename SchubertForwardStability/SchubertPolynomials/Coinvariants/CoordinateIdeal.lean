import SchubertForwardStability.SchubertPolynomials.Coinvariants.ArtinRemainder
import SchubertForwardStability.SchubertPolynomials.Coinvariants.SymmetricFunctionals
import SchubertForwardStability.SchubertPolynomials.Basis.Support

/-! # The symmetric ideal and supported Schubert coordinates

The Artin remainder and extraction duality identify the original symmetric
ideal with the joint kernel of all Schubert coordinates supported in the
finite interval. The characterization holds over every commutative ring.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial FinitaryPerm
open scoped Classical

variable {R : Type*} [CommRing R]

/-- An Artin polynomial with zero supported Schubert coordinates is zero. -/
theorem artin_eq_zero_of_coordinates {n : ℕ} {p : MvPolynomial ℕ+ R}
    (hp : p ∈ artinSpan R n)
    (hc : ∀ w : FinitaryPerm ℕ+, IsSupported n w → schubertFunctional R w p = 0) :
    p = 0 := by
  apply (schubertBasis R).repr.injective
  ext w
  simp only [map_zero, Finsupp.zero_apply]
  by_cases hw : IsSupported n w
  · rw [schubertBasis_repr]
    exact hc w hw
  · exact schubert_repr_eq_zero hp w hw

/-- Membership in the symmetric ideal is equivalent to vanishing supported Schubert coordinates. -/
theorem mem_symmetricIdeal_iff_coordinates (n : ℕ) (p : MvPolynomial (Fin n) R) :
    p ∈ symmetricIdeal R n ↔
      ∀ w : FinitaryPerm ℕ+, IsSupported n w →
        schubertFunctional R w (initialRename R n p) = 0 := by
  constructor
  · intro hp w hw
    exact schubertFunctional_symmetricIdeal hp w hw
  · intro hc
    obtain ⟨r, hr, hb⟩ := exists_artin_remainder n p
    have hz : initialRename R n r = 0 := by
      apply artin_eq_zero_of_coordinates hb
      intro w hw
      have h := schubertFunctional_symmetricIdeal hr w hw
      rw [map_sub, map_sub, hc w hw, zero_sub] at h
      exact neg_eq_zero.mp h
    have hrzero : r = 0 := initialRename_injective n (by simpa only [map_zero] using hz)
    simpa only [hrzero, sub_zero] using hr

end

end SchubertPolynomial
