import SchubertForwardStability.SchubertPolynomials.Products.Constants

/-!
# Coefficient-ring naturality of Schubert coordinates

## Main results

* `schubertFunctional_map` makes extraction commute with coefficient homomorphisms.
* `structureCoefficients_map` transports every product coordinate to a new ring.
* `structureCoefficients_intCast` recovers all ring coordinates from integer constants.
* `structureCoefficients_support_map` gives support inclusion under specialization.

## Implementation notes

Coefficient maps may identify nonzero scalars with zero. Coordinate supports can
therefore shrink; none of the results require injectivity of the ring homomorphism.
-/

namespace SchubertPolynomial

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Divided-difference extraction commutes with coefficient-ring homomorphisms. -/
theorem schubertFunctional_map (f : R →+* S) (w : FinitaryPerm ℕ+)
    (p : MvPolynomial ℕ+ R) :
    schubertFunctional S w (MvPolynomial.map f p) = f (schubertFunctional R w p) := by
  rw [schubertFunctional_apply, permutationDividedDifference_map,
    MvPolynomial.coeff_map, schubertFunctional_apply]

/-- Each Schubert basis coordinate commutes with coefficient-ring homomorphisms. -/
theorem schubertBasis_repr_map (f : R →+* S) (p : MvPolynomial ℕ+ R)
    (w : FinitaryPerm ℕ+) :
    (schubertBasis S).repr (MvPolynomial.map f p) w = f ((schubertBasis R).repr p w) := by
  rw [schubertBasis_repr, schubertFunctional_map, schubertBasis_repr]

/-- The finite Schubert coordinate vector is mapped coefficient by coefficient. -/
theorem schubertBasis_repr_mapRange (f : R →+* S) (p : MvPolynomial ℕ+ R) :
    (schubertBasis S).repr (MvPolynomial.map f p) =
      ((schubertBasis R).repr p).mapRange f f.map_zero := by
  ext w
  rw [schubertBasis_repr_map, Finsupp.mapRange_apply]

/-- Changing coefficient rings cannot enlarge a polynomial's Schubert coordinate
support. -/
theorem schubert_repr_support_map (f : R →+* S) (p : MvPolynomial ℕ+ R) :
    ((schubertBasis S).repr (MvPolynomial.map f p)).support ⊆
      ((schubertBasis R).repr p).support := by
  rw [schubertBasis_repr_mapRange]
  exact Finsupp.support_mapRange

/-- Every Schubert product coordinate commutes with coefficient-ring homomorphisms. -/
theorem structureCoefficients_map (f : R →+* S) (u v w : FinitaryPerm ℕ+) :
    structureCoefficients S u v w = f (structureCoefficients R u v w) := by
  rw [structureCoefficients_apply, structureCoefficients_apply,
    ← schubert_map f u, ← schubert_map f v, ← map_mul, schubertFunctional_map]

/-- The finite coordinate vector of a Schubert product is mapped coefficient by
coefficient under a ring homomorphism. -/
theorem structureCoefficients_mapRange (f : R →+* S) (u v : FinitaryPerm ℕ+) :
    structureCoefficients S u v = (structureCoefficients R u v).mapRange f f.map_zero := by
  ext w
  rw [Finsupp.mapRange_apply, structureCoefficients_map f]

/-- The integer Schubert structure constants recover every commutative-ring
product coordinate by integer casting. -/
theorem structureCoefficients_intCast (u v w : FinitaryPerm ℕ+) :
    structureCoefficients R u v w = (structureConst u v w : R) :=
  structureCoefficients_map (Int.castRingHom R) u v w

/-- Changing coefficient rings cannot enlarge a Schubert product's coordinate support. -/
theorem structureCoefficients_support_map (f : R →+* S) (u v : FinitaryPerm ℕ+) :
    (structureCoefficients S u v).support ⊆ (structureCoefficients R u v).support := by
  rw [structureCoefficients_mapRange f]
  exact Finsupp.support_mapRange

/-- Every commutative-ring product coordinate support is contained in the integer
product coordinate support. -/
theorem structureCoefficients_support_int (u v : FinitaryPerm ℕ+) :
    (structureCoefficients R u v).support ⊆ (structureCoefficients ℤ u v).support :=
  structureCoefficients_support_map (Int.castRingHom R) u v

end

end SchubertPolynomial
