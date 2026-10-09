import SchubertForwardStability.SchubertPolynomials.Coinvariants.ArtinRemainder
import SchubertForwardStability.SchubertPolynomials.Basis.Finite

/-! # Finite-variable lifts of Artin polynomials

Artin degree bounds force all variables into the initial finite interval.
The unique finite-variable lift is linear, and embeds the finite Schubert
basis as its positive-indexed polynomial representatives.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial
open scoped Classical

variable {R : Type*} [CommRing R]

/-- Every Artin-bounded polynomial has a finite-variable representative in the same size. -/
theorem exists_initialRename_of_artin {n : ℕ} {p : MvPolynomial ℕ+ R}
    (hp : p ∈ artinSpan R n) :
    ∃ q : MvPolynomial (Fin n) R, initialRename R n q = p := by
  apply exists_rename_eq_of_vars_subset_range p
    (fun i => (FinitaryPerm.positiveIndex n i).val)
    (fun _ _ h => (FinitaryPerm.positiveIndex n).injective (Subtype.ext h))
  intro j hj
  have hd := (mem_artinSpan_iff_degree n p).mp hp j
  have hpos := Nat.pos_of_ne_zero (mem_vars_iff_degreeOf_ne_zero.mp hj)
  have hjn : (j : ℕ) ≤ n := by omega
  refine ⟨(FinitaryPerm.positiveIndex n).symm ⟨j, hjn⟩, ?_⟩
  exact congrArg Subtype.val ((FinitaryPerm.positiveIndex n).apply_symm_apply ⟨j, hjn⟩)

/-- The unique finite-variable lift of an Artin-bounded polynomial. -/
def artinFiniteLift (R : Type*) [CommRing R] (n : ℕ) (p : artinSpan R n) :
    MvPolynomial (Fin n) R := Classical.choose (exists_initialRename_of_artin p.property)

/-- Embedding the finite Artin lift recovers the original polynomial. -/
@[simp] theorem initialRename_artinFiniteLift (n : ℕ) (p : artinSpan R n) :
    initialRename R n (artinFiniteLift R n p) = p.1 :=
  Classical.choose_spec (exists_initialRename_of_artin p.property)

/-- The finite Artin lift is linear in the polynomial. -/
def artinLiftLinear (R : Type*) [CommRing R] (n : ℕ) :
    artinSpan R n →ₗ[R] MvPolynomial (Fin n) R where
  toFun := artinFiniteLift R n
  map_add' p q := by
    apply initialRename_injective n
    simp only [initialRename_artinFiniteLift, map_add, Submodule.coe_add]
  map_smul' c p := by
    apply initialRename_injective n
    simp only [initialRename_artinFiniteLift, map_smul, Submodule.coe_smul, RingHom.id_apply]

/-- The finite Artin lift embeds back to the Artin polynomial. -/
@[simp] theorem initialRename_artinLiftLinear (n : ℕ) (p : artinSpan R n) :
    initialRename R n (artinLiftLinear R n p) = p.1 := initialRename_artinFiniteLift n p

/-- A finite-variable Schubert representative is obtained from the finite Artin basis. -/
def finiteSchubert (R : Type*) [CommRing R] (n : ℕ) (w : Equiv.Perm (Fin n)) :
    MvPolynomial (Fin n) R := artinLiftLinear R n (finiteSchubertBasis R n w)

/-- The finite-variable Schubert representative maps to the Schubert polynomial of the
corresponding finitary permutation. -/
@[simp] theorem initialRename_finiteSchubert (n : ℕ) (w : Equiv.Perm (Fin n)) :
    initialRename R n (finiteSchubert R n w) =
      schubert R (FinitaryPerm.ofFinite n w) := by
  rw [finiteSchubert, initialRename_artinLiftLinear, finiteSchubertBasis_apply]

end

end SchubertPolynomial
