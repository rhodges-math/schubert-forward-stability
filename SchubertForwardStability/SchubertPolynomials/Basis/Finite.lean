import SchubertForwardStability.SchubertPolynomials.Basis.DualFamily
import SchubertForwardStability.SchubertPolynomials.Basis.FiniteIndices
import SchubertForwardStability.SchubertPolynomials.Basis.ArtinSchubert
import SchubertForwardStability.SchubertPolynomials.Stability.Duality

/-!
# The finite Schubert basis

## Main definitions

* `finiteSchubertBasis` is the Schubert basis of the Artin span in a fixed size.

## Main results

* `finiteSchubertBasis_repr` gives coordinates by divided-difference functionals.
* `artinSpan_eq_span_schubert` identifies the Artin span with supported Schubert vectors.

## Implementation notes

The monomial basis has factorial cardinality. Biorthogonality then constructs
the Schubert basis over every commutative ring.
-/

namespace SchubertPolynomial

noncomputable section

open scoped Classical BigOperators

variable {R : Type*} [CommRing R]

private def finiteVector (R : Type*) [CommRing R] (n : ℕ) (w : Equiv.Perm (Fin n)) :
    artinSpan R n :=
  ⟨schubert R (FinitaryPerm.ofFinite n w),
    schubert_mem_artinSpan _ (FinitaryPerm.isSupported_ofFinite n w)⟩

private def finiteFunctional (R : Type*) [CommRing R] (n : ℕ)
    (w : Equiv.Perm (Fin n)) : artinSpan R n →ₗ[R] R :=
  (schubertFunctional R (FinitaryPerm.ofFinite n w)).comp (artinSpan R n).subtype

private theorem finite_biorthogonal (n : ℕ) (u v : Equiv.Perm (Fin n)) :
    finiteFunctional R n u (finiteVector R n v) = if u = v then 1 else 0 := by
  change schubertFunctional R (FinitaryPerm.ofFinite n u)
    (schubert R (FinitaryPerm.ofFinite n v)) = _
  rw [schubertFunctional_schubert]
  simp only [(FinitaryPerm.ofFinite_injective n).eq_iff]

/-- The Schubert polynomials indexed by the size-`n` symmetric group form a basis
of the size-`n` Artin span over every commutative coefficient ring. -/
def finiteSchubertBasis (R : Type*) [CommRing R] (n : ℕ) :
    Module.Basis (Equiv.Perm (Fin n)) R (artinSpan R n) :=
  basisOfDualFamily (artinPermutationBasis R n) (finiteVector R n)
    (finiteFunctional R n) (by
      intro i j
      by_cases hij : i = j
      · simpa only [ite_eq_left hij] using (finite_biorthogonal (R := R) n i j)
      · simpa only [ite_eq_right hij] using (finite_biorthogonal (R := R) n i j))

/-- The finite Schubert basis vector is the polynomial of the extended permutation. -/
@[simp] theorem finiteSchubertBasis_apply (n : ℕ) (w : Equiv.Perm (Fin n)) :
    (finiteSchubertBasis R n w : MvPolynomial ℕ+ R) =
      schubert R (FinitaryPerm.ofFinite n w) := by
  rw [finiteSchubertBasis, basisOfDualFamily_apply]
  rfl

/-- Finite Schubert coordinates are the divided-difference functionals. -/
@[simp] theorem finiteSchubertBasis_repr (n : ℕ) (p : artinSpan R n)
    (w : Equiv.Perm (Fin n)) : (finiteSchubertBasis R n).repr p w =
      schubertFunctional R (FinitaryPerm.ofFinite n w) p.1 := by
  rw [finiteSchubertBasis, basisOfDualFamily_repr]
  rfl

/-- The Artin span consists exactly of linear combinations of Schubert polynomials
whose permutations are supported in its ambient size. -/
theorem artinSpan_eq_span_schubert (n : ℕ) :
    artinSpan R n = Submodule.span R
      (schubert R '' {w : FinitaryPerm ℕ+ | FinitaryPerm.IsSupported n w}) := by
  apply le_antisymm
  · intro p hp
    have he := congrArg Subtype.val ((finiteSchubertBasis R n).sum_repr ⟨p, hp⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, finiteSchubertBasis_apply] at he
    rw [← he]
    apply Submodule.sum_mem
    intro w _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨FinitaryPerm.ofFinite n w, FinitaryPerm.isSupported_ofFinite n w, rfl⟩
  · apply Submodule.span_le.mpr
    rintro p ⟨w, hw, rfl⟩
    exact schubert_mem_artinSpan w hw

end

end SchubertPolynomial
