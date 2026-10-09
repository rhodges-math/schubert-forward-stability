import SchubertForwardStability.SchubertPolynomials.Coinvariants.AscendingRemainder
import SchubertForwardStability.SchubertPolynomials.Divided.FiniteVariables
import SchubertForwardStability.SchubertPolynomials.Basis.ArtinSpan

/-! # Artin remainders of the symmetric-generator quotient

Ordinary reversal of finite variables converts ascending bounds into the
descending Artin bounds. The original symmetric ideal is invariant under
variable permutations, so every quotient class has an Artin representative.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial
open scoped Classical

variable {R : Type*} [CommRing R]

/-- Permuting finite variables preserves the symmetric-generator ideal. -/
theorem rename_mem_symmetricIdeal (n : ℕ) (e : Equiv.Perm (Fin n))
    {p : MvPolynomial (Fin n) R} (hp : p ∈ symmetricIdeal R n) :
    rename e p ∈ symmetricIdeal R n := by
  have hle : symmetricIdeal R n ≤ Ideal.comap (rename e).toRingHom (symmetricIdeal R n) := by
    apply Ideal.span_le.mpr
    rintro q ⟨hq, hc⟩
    change rename e q ∈ symmetricIdeal R n
    exact Ideal.subset_span ⟨hq.rename e, by rw [constantCoeff_rename, hc]⟩
  exact hle hp

/-- Descending finite-variable degree bounds give membership in the positive-indexed Artin span. -/
theorem initialRename_mem_artinSpan {n : ℕ} (p : MvPolynomial (Fin n) R)
    (hp : ∀ i : Fin n, degreeOf i p ≤ n - (i.val + 1)) :
    initialRename R n p ∈ artinSpan R n := by
  let f : Fin n → ℕ+ := fun i => (FinitaryPerm.positiveIndex n i).val
  have hf : Function.Injective f := fun _ _ h =>
    (FinitaryPerm.positiveIndex n).injective (Subtype.ext h)
  rw [mem_artinSpan_iff_degree]
  intro j
  by_cases hj : (j : ℕ) ≤ n
  · let i := (FinitaryPerm.positiveIndex n).symm ⟨j, hj⟩
    have he : f i = j := congrArg Subtype.val
      ((FinitaryPerm.positiveIndex n).apply_symm_apply ⟨j, hj⟩)
    change degreeOf j (rename f p) ≤ _
    rw [←he, degreeOf_rename_of_injective hf]
    simpa only [f, FinitaryPerm.positiveIndex_val] using hp i
  · have hz : degreeOf j (rename f p) = 0 := by
      by_contra h
      obtain ⟨i, _, he⟩ := mem_vars_rename f p (mem_vars_iff_degreeOf_ne_zero.mpr h)
      have hi := (FinitaryPerm.positiveIndex n i).property
      exact hj (he ▸ hi)
    change degreeOf j (rename f p) ≤ _
    rw [hz]
    exact Nat.zero_le _

/-- Every class modulo the original symmetric ideal has an Artin-bounded representative. -/
theorem exists_artin_remainder (n : ℕ) (p : MvPolynomial (Fin n) R) :
    ∃ r : MvPolynomial (Fin n) R, p - r ∈ symmetricIdeal R n ∧
      initialRename R n r ∈ artinSpan R n := by
  obtain ⟨r, hr, hb⟩ := exists_ascending_remainder n (rename Fin.rev p)
  refine ⟨rename Fin.rev r, ?_, initialRename_mem_artinSpan _ ?_⟩
  · have h := rename_mem_symmetricIdeal n Fin.revPerm hr
    change rename Fin.rev (rename Fin.rev p - r) ∈ symmetricIdeal R n at h
    simp only [map_sub, rename_rename, Function.comp_def, Fin.rev_rev] at h
    change rename id p - rename Fin.rev r ∈ symmetricIdeal R n at h
    simpa only [rename_id, AlgHom.id_apply] using h
  · intro i
    have hd : degreeOf i.rev r ≤ i.rev.val := degreeOf_le_iff.mpr fun a ha => hb a ha i.rev
    have he := degreeOf_rename_of_injective (p := r) Fin.rev_injective i.rev
    rw [Fin.rev_rev] at he
    rw [he]
    exact hd

end

end SchubertPolynomial
