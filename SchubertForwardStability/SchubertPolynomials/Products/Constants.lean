import SchubertForwardStability.SchubertPolynomials.Basis.Global

/-! # Schubert structure constants

## Main definitions

* `structureCoefficients`: the finitely supported coordinates of a Schubert product.
* `structureConst`: the integral coordinate at a specified permutation.

## Main results

Products have a unique finite Schubert expansion. The identity factor gives the
single corresponding basis vector, and exchanging the factors preserves coordinates.

## Implementation notes

Coordinates are defined over any commutative ring; the integral scalar constants
are the specialization used for integer Schubert products.
-/

namespace SchubertPolynomial

noncomputable section

open scoped Classical BigOperators

variable {R : Type*} [CommRing R]

/-- The finitely supported Schubert coordinates of a product over a commutative ring. -/
def structureCoefficients (R : Type*) [CommRing R] (u v : FinitaryPerm ℕ+) :
    FinitaryPerm ℕ+ →₀ R :=
  (schubertBasis R).repr (schubert R u * schubert R v)

/-- Every product coordinate is its divided-difference extraction functional. -/
theorem structureCoefficients_apply (u v w : FinitaryPerm ℕ+) :
    structureCoefficients R u v w = schubertFunctional R w (schubert R u * schubert R v) :=
  schubertBasis_repr _ _

/-- A Schubert product is the finite sum of its Schubert coordinate multiples. -/
theorem schubert_mul_expansion (u v : FinitaryPerm ℕ+) :
    (∑ w ∈ (structureCoefficients R u v).support,
      structureCoefficients R u v w • schubert R w) = schubert R u * schubert R v := by
  simpa only [structureCoefficients, Finsupp.linearCombination_apply, Finsupp.sum,
    schubertBasis_apply] using
      (schubertBasis R).linearCombination_repr (schubert R u * schubert R v)

/-- A finite Schubert expansion has exactly the product's prescribed coordinates. -/
theorem structureCoefficients_unique (u v : FinitaryPerm ℕ+)
    (a : FinitaryPerm ℕ+ →₀ R)
    (ha : a.sum (fun w c => c • schubert R w) = schubert R u * schubert R v) :
    structureCoefficients R u v = a := by
  have he : Finsupp.linearCombination R (schubertBasis R) a =
      schubert R u * schubert R v := by
    simpa only [Finsupp.linearCombination_apply, schubertBasis_apply] using ha
  have hr := congrArg (schubertBasis R).repr he
  simpa only [Module.Basis.repr_linearCombination, structureCoefficients] using hr.symm

/-- Exchanging the two factors preserves every Schubert product coordinate. -/
theorem structureCoefficients_comm (u v : FinitaryPerm ℕ+) :
    structureCoefficients R u v = structureCoefficients R v u := by
  rw [structureCoefficients, structureCoefficients, mul_comm]

/-- Multiplication by the identity Schubert polynomial has a single basis coordinate. -/
@[simp] theorem structureCoefficients_one_left (v : FinitaryPerm ℕ+) :
    structureCoefficients R 1 v = Finsupp.single v 1 := by
  rw [structureCoefficients, schubert_one, one_mul, ← schubertBasis_apply,
    Module.Basis.repr_self]

/-- The right identity factor has the same single basis coordinate. -/
@[simp] theorem structureCoefficients_one_right (u : FinitaryPerm ℕ+) :
    structureCoefficients R u 1 = Finsupp.single u 1 := by
  rw [structureCoefficients_comm, structureCoefficients_one_left]

/-- Over a domain a Schubert product has a nonzero coordinate vector. -/
theorem structureCoefficients_ne_zero [IsDomain R] (u v : FinitaryPerm ℕ+) :
    structureCoefficients R u v ≠ 0 := by
  intro he
  have hp : schubert R u * schubert R v = 0 :=
    (schubertBasis R).repr.injective (by simpa only [structureCoefficients, map_zero] using he)
  exact (mul_ne_zero (schubert_ne_zero u) (schubert_ne_zero v)) hp

/-- The integer Schubert structure constant at a specified permutation. -/
def structureConst (u v w : FinitaryPerm ℕ+) : ℤ := structureCoefficients ℤ u v w

/-- The structure constant agrees with the defining integer Schubert basis coordinate. -/
theorem structureConst_eq_repr (u v w : FinitaryPerm ℕ+) :
    structureConst u v w = (schubertBasis ℤ).repr (schubert ℤ u * schubert ℤ v) w := rfl

/-- The integer structure constant is extracted by the divided-difference functional. -/
theorem structureConst_eq_functional (u v w : FinitaryPerm ℕ+) :
    structureConst u v w = schubertFunctional ℤ w (schubert ℤ u * schubert ℤ v) :=
  structureCoefficients_apply u v w

/-- Integer Schubert structure constants have finite support in their output index. -/
theorem structureConst_finite_support (u v : FinitaryPerm ℕ+) :
    Set.Finite {w | structureConst u v w ≠ 0} := by
  exact (structureCoefficients ℤ u v).support.finite_toSet.subset
    (fun _ hw => Finsupp.mem_support_iff.mpr hw)

/-- Integer Schubert products have the expansion by their integral structure constants. -/
theorem structureConst_expansion (u v : FinitaryPerm ℕ+) :
    (∑ w ∈ (structureCoefficients ℤ u v).support,
      structureConst u v w • schubert ℤ w) = schubert ℤ u * schubert ℤ v :=
  schubert_mul_expansion u v

/-- Exchanging the input permutations preserves the integer structure constants. -/
theorem structureConst_comm (u v w : FinitaryPerm ℕ+) :
    structureConst u v w = structureConst v u w :=
  congrArg (fun a : FinitaryPerm ℕ+ →₀ ℤ => a w) (structureCoefficients_comm u v)

/-- The identity left factor has the Kronecker-delta structure constant. -/
@[simp] theorem structureConst_one_left (v w : FinitaryPerm ℕ+) :
    structureConst 1 v w = if v = w then 1 else 0 := by
  simp only [structureConst, structureCoefficients_one_left, Finsupp.single_apply]

/-- The identity right factor has the Kronecker-delta structure constant. -/
@[simp] theorem structureConst_one_right (u w : FinitaryPerm ℕ+) :
    structureConst u 1 w = if u = w then 1 else 0 := by
  rw [structureConst_comm, structureConst_one_left]

end

end SchubertPolynomial
