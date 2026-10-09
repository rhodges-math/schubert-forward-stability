import SchubertForwardStability.SchubertPolynomials.Coinvariants.SymmetricIdeal
import SchubertForwardStability.SchubertPolynomials.Divided.Basic
import Mathlib.RingTheory.Ideal.Maps

/-! # Signed permutations of polynomial variables

The substitution sending each variable to the negative of its permuted variable
is an algebra equivalence. It preserves the symmetric-generator ideal and
intertwines divided differences with the order of the root reversed.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial
open scoped Classical

variable {σ R : Type*} [CommRing R]

/-- Permute all polynomial variables and change the sign of each variable. -/
def signedRename (R : Type*) [CommRing R] (e : Equiv.Perm σ) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval fun i => -X (e i)) (aeval fun i => -X (e.symm i))
    (by ext i; simp) (by ext i; simp)

/-- A signed variable permutation sends the indexed variable to its negative image. -/
@[simp] theorem signedRename_X (e : Equiv.Perm σ) (i : σ) :
    signedRename R e (X i) = -X (e i) := by
  change aeval (fun j => -X (e j)) (X i) = -X (e i)
  exact aeval_X _ _

/-- A signed variable permutation fixes coefficient constants. -/
@[simp] theorem signedRename_C (e : Equiv.Perm σ) (r : R) :
    signedRename R e (C r) = C r := by
  change aeval (fun j => -X (e j)) (C r) = C r
  simp

/-- The inverse signed substitution uses the inverse permutation. -/
theorem signedRename_symm (e : Equiv.Perm σ) :
    (signedRename R e).symm = signedRename R e.symm := by
  rfl

/-- Signed variable permutation preserves the constant coefficient. -/
@[simp] theorem constantCoeff_signedRename (e : Equiv.Perm σ) (p : MvPolynomial σ R) :
    constantCoeff (signedRename R e p) = constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i _ => simp only [map_mul, signedRename_X, map_neg, constantCoeff_X, neg_zero,
      mul_zero]

/-- A variable rename transports across the signed substitution by conjugation. -/
theorem rename_signedRename (e f : Equiv.Perm σ) (p : MvPolynomial σ R) :
    rename f (signedRename R e p) =
      signedRename R e (rename ((e.trans f).trans e.symm) p) := by
  have he : (rename f).comp (signedRename R e).toAlgHom =
      (signedRename R e).toAlgHom.comp (rename ((e.trans f).trans e.symm)) := by
    ext i
    simp
  exact AlgHom.congr_fun he p

/-- Signed variable permutation preserves symmetry. -/
theorem isSymmetric_signedRename {p : MvPolynomial σ R} (hp : p.IsSymmetric)
    (e : Equiv.Perm σ) : (signedRename R e p).IsSymmetric := by
  intro f
  rw [rename_signedRename, hp]

/-- A signed variable permutation preserves the symmetric-generator ideal. -/
theorem signedRename_mem_symmetricIdeal {n : ℕ} (e : Equiv.Perm (Fin n))
    {p : MvPolynomial (Fin n) R} (hp : p ∈ symmetricIdeal R n) :
    signedRename R e p ∈ symmetricIdeal R n := by
  have hi : symmetricIdeal R n ≤
      Ideal.comap (signedRename R e).toRingHom (symmetricIdeal R n) := by
    apply Ideal.span_le.mpr
    rintro q ⟨hq, hc⟩
    exact Ideal.subset_span ⟨isSymmetric_signedRename hq e,
      (constantCoeff_signedRename e q).trans hc⟩
  exact hi hp

/-- Symmetric-ideal membership is unchanged by signed variable permutation. -/
theorem signedRename_mem_symmetricIdeal_iff {n : ℕ} (e : Equiv.Perm (Fin n))
    (p : MvPolynomial (Fin n) R) :
    signedRename R e p ∈ symmetricIdeal R n ↔ p ∈ symmetricIdeal R n := by
  constructor
  · intro hp
    have hi := signedRename_mem_symmetricIdeal e.symm hp
    rw [←signedRename_symm, AlgEquiv.symm_apply_apply] at hi
    exact hi
  · exact signedRename_mem_symmetricIdeal e

private theorem signedRename_swap (e : Equiv.Perm σ) (i j : σ)
    (p : MvPolynomial σ R) :
    signedRename R e (variableSwap R i j p) =
      variableSwap R (e i) (e j) (signedRename R e p) := by
  have he : (signedRename R e).toAlgHom.comp (variableSwap R i j).toAlgHom =
      (variableSwap R (e i) (e j)).toAlgHom.comp (signedRename R e).toAlgHom := by
    ext k
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      variableSwap, renameEquiv_apply, rename_X, signedRename_X, map_neg]
    congr 2
    by_cases hki : k = i
    · subst k; simp
    by_cases hkj : k = j
    · subst k; simp
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj,
      Equiv.swap_apply_of_ne_of_ne (e.injective.ne hki) (e.injective.ne hkj)]
  exact AlgHom.congr_fun he p

/-- Signed permutation intertwines divided differences with the root order reversed. -/
theorem divided_signedRename (e : Equiv.Perm σ) {i j : σ} (hij : i ≠ j)
    (p : MvPolynomial σ R) :
    variableDividedDifference R (e j) (e i) (signedRename R e p) =
      signedRename R e (variableDividedDifference R i j p) := by
  apply (variableDividedDifference_eq_iff (e.injective.ne hij.symm) _ _).mpr
  have he := congrArg (signedRename R e) (root_mul_variableDividedDifference hij p)
  simp only [map_mul, map_sub, signedRename_X, signedRename_swap] at he
  rw [variableSwap] at he
  rw [variableSwap, Equiv.swap_comm (e j) (e i)]
  simpa only [neg_sub_neg] using he

end

end SchubertPolynomial
