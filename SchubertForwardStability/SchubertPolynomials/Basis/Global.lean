import SchubertForwardStability.SchubertPolynomials.Basis.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The global Schubert basis

## Main definitions

* `schubertBasis` is the basis of polynomials indexed by all finitary permutations.

## Main results

* `schubert_linearIndependent` follows from divided-difference functionals.
* `schubert_span_eq_top` follows from finite Artin span exhaustion.
* `schubertBasis_repr` identifies every coordinate with its extraction functional.

## Implementation notes

Every polynomial lies in one finite Artin span. The finite basis theorem therefore
gives global spanning.
-/

namespace SchubertPolynomial

noncomputable section

open scoped Classical

variable {R : Type*} [CommRing R]

/-- All finitary Schubert polynomials are linearly independent over every
commutative coefficient ring. -/
theorem schubert_linearIndependent : LinearIndependent R (schubert R) := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one (schubert R) (schubertFunctional R)
  · intro u v hne
    rw [schubertFunctional_schubert, ite_eq_right hne]
  · intro w
    rw [schubertFunctional_schubert, ite_eq_left rfl]

/-- The finitary Schubert polynomials span the full polynomial module. -/
theorem schubert_span_eq_top :
    Submodule.span R (Set.range (schubert R)) = ⊤ := by
  apply eq_top_iff.mpr
  intro p _
  obtain ⟨n, hp⟩ := exists_mem_artinSpan p
  have hle : artinSpan R n ≤ Submodule.span R (Set.range (schubert R)) := by
    rw [artinSpan_eq_span_schubert]
    apply Submodule.span_mono
    rintro p ⟨w, _, rfl⟩
    exact ⟨w, rfl⟩
  exact hle hp

/-- The Schubert polynomials form a basis of polynomials over every
commutative coefficient ring. -/
def schubertBasis (R : Type*) [CommRing R] :
    Module.Basis (FinitaryPerm ℕ+) R (MvPolynomial ℕ+ R) :=
  Module.Basis.mk schubert_linearIndependent (le_of_eq schubert_span_eq_top.symm)

/-- A global Schubert basis vector is its indexed Schubert polynomial. -/
@[simp] theorem schubertBasis_apply (w : FinitaryPerm ℕ+) :
    schubertBasis R w = schubert R w := by
  exact Module.Basis.mk_apply _ _ _

/-- Global Schubert coordinates are the divided-difference functionals. -/
@[simp] theorem schubertBasis_repr (p : MvPolynomial ℕ+ R) (w : FinitaryPerm ℕ+) :
    (schubertBasis R).repr p w = schubertFunctional R w p := by
  have he : (schubertBasis R).coord w = schubertFunctional R w := by
    apply (schubertBasis R).ext
    intro v
    change (schubertBasis R).repr (schubertBasis R v) w =
      schubertFunctional R w (schubertBasis R v)
    rw [Module.Basis.repr_self_apply, schubertBasis_apply, schubertFunctional_schubert]
    simp only [eq_comm]
  exact congrArg (fun f : MvPolynomial ℕ+ R →ₗ[R] R => f p) he

end

end SchubertPolynomial
