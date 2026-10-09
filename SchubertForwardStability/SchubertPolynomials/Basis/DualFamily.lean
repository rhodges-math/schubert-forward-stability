import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# Bases from finite dual families

## Main definitions

* `basisOfDualFamily` turns a finite biorthogonal vector family into a basis when
  a basis indexed by the same finite type is already available.

## Implementation notes

A left inverse on a finite free module over a commutative ring is a right inverse.
This applies also to the zero ring and does not require a field or a domain.
-/

namespace SchubertPolynomial

noncomputable section

open scoped Classical

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]

private def dualReconstruction (b : Module.Basis ι R M) (f : ι → M →ₗ[R] R) :
    M →ₗ[R] M :=
  b.equivFun.symm.toLinearMap.comp (LinearMap.pi f)

private theorem dual_left_inverse (b : Module.Basis ι R M) (v : ι → M)
    (f : ι → M →ₗ[R] R) (hf : ∀ i j, f i (v j) = if i = j then 1 else 0) :
    (dualReconstruction b f).comp (b.constr R v) = LinearMap.id := by
  apply b.ext
  intro j
  apply b.equivFun.injective
  ext i
  simp [dualReconstruction, hf, Module.Basis.equivFun_self]

private def dualFamilyEquiv (b : Module.Basis ι R M) (v : ι → M)
    (f : ι → M →ₗ[R] R) (hf : ∀ i j, f i (v j) = if i = j then 1 else 0) :
    M ≃ₗ[R] M := by
  letI : Module.Free R M := Module.Free.of_basis b
  letI : Module.Finite R M := Module.Finite.of_basis b
  have hleft := dual_left_inverse b v f hf
  have hright := (LinearMap.comp_eq_id_comm R M).mp hleft
  exact LinearEquiv.ofLinearMap (b.constr R v) (dualReconstruction b f) hright hleft

/-- A finite vector family with a biorthogonal functional family is a basis whenever
the module has a basis indexed by the same finite type. -/
def basisOfDualFamily (b : Module.Basis ι R M) (v : ι → M)
    (f : ι → M →ₗ[R] R) (hf : ∀ i j, f i (v j) = if i = j then 1 else 0) :
    Module.Basis ι R M :=
  b.map (dualFamilyEquiv b v f hf)

/-- The basis constructed from a biorthogonal family has the prescribed vectors. -/
@[simp] theorem basisOfDualFamily_apply (b : Module.Basis ι R M) (v : ι → M)
    (f : ι → M →ₗ[R] R) (hf : ∀ i j, f i (v j) = if i = j then 1 else 0) (i : ι) :
    basisOfDualFamily b v f hf i = v i := by
  simp [basisOfDualFamily, dualFamilyEquiv]

/-- The coordinates of the basis constructed from a biorthogonal family are its
prescribed functionals. -/
@[simp] theorem basisOfDualFamily_repr (b : Module.Basis ι R M) (v : ι → M)
    (f : ι → M →ₗ[R] R) (hf : ∀ i j, f i (v j) = if i = j then 1 else 0)
    (p : M) (i : ι) : (basisOfDualFamily b v f hf).repr p i = f i p := by
  change b.repr ((dualFamilyEquiv b v f hf).symm p) i = f i p
  change b.equivFun (dualReconstruction b f p) i = f i p
  simp [dualReconstruction, Finsupp.single_apply]

end

end SchubertPolynomial
