import SchubertForwardStability.SchubertPolynomials.Coinvariants.FiniteArtinLift
import SchubertForwardStability.SchubertPolynomials.Coinvariants.CoordinateIdeal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Schubert coordinates in the symmetric-generator quotient

The Artin representatives give an isomorphism onto the quotient by the
original symmetric-generator ideal. Transporting the finite Schubert basis
through this isomorphism identifies quotient coordinates with polynomial
divided-difference extraction coordinates.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial FinitaryPerm
open scoped Classical

variable {R : Type*} [CommRing R]

/-- The coinvariant ring with its symmetric-generator ideal presentation. -/
abbrev Coinvariant (R : Type*) [CommRing R] (n : ℕ) :=
  MvPolynomial (Fin n) R ⧸ symmetricIdeal R n

/-- Send an Artin representative to its class in the original coinvariant quotient. -/
def artinQuotientMap (R : Type*) [CommRing R] (n : ℕ) :
    artinSpan R n →ₗ[R] Coinvariant R n :=
  (Ideal.Quotient.mkₐ R (symmetricIdeal R n)).toLinearMap.comp (artinLiftLinear R n)

/-- Distinct Artin representatives have distinct classes in the symmetric quotient. -/
theorem artinQuotientMap_injective (n : ℕ) : Function.Injective (artinQuotientMap R n) := by
  intro p q he
  change Ideal.Quotient.mk (symmetricIdeal R n) (artinLiftLinear R n p) =
    Ideal.Quotient.mk (symmetricIdeal R n) (artinLiftLinear R n q) at he
  have hi := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply artin_eq_zero_of_coordinates ((artinSpan R n).sub_mem p.property q.property)
  intro w hw
  have h := schubertFunctional_symmetricIdeal hi w hw
  simpa only [map_sub, initialRename_artinLiftLinear] using h

/-- Every original quotient class is represented by an Artin polynomial. -/
theorem artinQuotientMap_surjective (n : ℕ) : Function.Surjective (artinQuotientMap R n) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (symmetricIdeal R n) x
  obtain ⟨r, hr, hb⟩ := exists_artin_remainder n p
  refine ⟨⟨initialRename R n r, hb⟩, ?_⟩
  have hl : artinLiftLinear R n ⟨initialRename R n r, hb⟩ = r := by
    apply initialRename_injective n
    rw [initialRename_artinLiftLinear]
  change Ideal.Quotient.mk (symmetricIdeal R n)
    (artinLiftLinear R n ⟨initialRename R n r, hb⟩) = Ideal.Quotient.mk (symmetricIdeal R n) p
  rw [hl]
  exact ((Ideal.Quotient.mk_eq_mk_iff_sub_mem p r).mpr hr).symm

/-- The Artin span is linearly isomorphic to the original symmetric-generator quotient. -/
def artinQuotientEquiv (R : Type*) [CommRing R] (n : ℕ) :
    artinSpan R n ≃ₗ[R] Coinvariant R n :=
  LinearEquiv.ofBijective (artinQuotientMap R n)
    ⟨artinQuotientMap_injective n, artinQuotientMap_surjective n⟩

/-- The finite Schubert basis descends to the original symmetric-generator quotient. -/
def coinvariantSchubertBasis (R : Type*) [CommRing R] (n : ℕ) :
    Module.Basis (Equiv.Perm (Fin n)) R (Coinvariant R n) :=
  (finiteSchubertBasis R n).map (artinQuotientEquiv R n)

/-- A quotient Schubert basis vector is the class of its finite Schubert representative. -/
@[simp] theorem coinvariantSchubertBasis_apply (n : ℕ) (w : Equiv.Perm (Fin n)) :
    coinvariantSchubertBasis R n w =
      Ideal.Quotient.mk (symmetricIdeal R n) (finiteSchubert R n w) := rfl

/-- Quotient Schubert coordinates equal the extraction coordinates of the polynomial. -/
theorem coinvariantSchubertBasis_repr (n : ℕ) (p : MvPolynomial (Fin n) R)
    (w : Equiv.Perm (Fin n)) :
    (coinvariantSchubertBasis R n).repr (Ideal.Quotient.mk (symmetricIdeal R n) p) w =
      schubertFunctional R (ofFinite n w) (initialRename R n p) := by
  obtain ⟨r, hr, hb⟩ := exists_artin_remainder n p
  have hl : artinLiftLinear R n ⟨initialRename R n r, hb⟩ = r := by
    apply initialRename_injective n
    rw [initialRename_artinLiftLinear]
  have he : artinQuotientEquiv R n ⟨initialRename R n r, hb⟩ =
      Ideal.Quotient.mk (symmetricIdeal R n) p := by
    change Ideal.Quotient.mk (symmetricIdeal R n)
      (artinLiftLinear R n ⟨initialRename R n r, hb⟩) = _
    rw [hl]
    exact ((Ideal.Quotient.mk_eq_mk_iff_sub_mem p r).mpr hr).symm
  change (finiteSchubertBasis R n).repr
    ((artinQuotientEquiv R n).symm (Ideal.Quotient.mk (symmetricIdeal R n) p)) w = _
  rw [←he, LinearEquiv.symm_apply_apply, finiteSchubertBasis_repr]
  have h := schubertFunctional_symmetricIdeal hr (ofFinite n w) (isSupported_ofFinite n w)
  rw [map_sub, map_sub] at h
  exact (sub_eq_zero.mp h).symm

end

end SchubertPolynomial
