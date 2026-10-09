import SchubertForwardStability.SchubertPolynomials.Coinvariants.LongestOperators
import SchubertForwardStability.SchubertPolynomials.Coinvariants.QuotientBasis
import SchubertForwardStability.SchubertPolynomials.Products.Constants

/-! # Longest symmetry of Schubert product coordinates

Signed reversal of finite variables carries each Schubert class to its
longest conjugate. Multiplicativity in the original symmetric-generator
quotient then preserves supported product coordinates under conjugation.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial FinitaryPerm
open scoped Classical

variable {R : Type*} [CommRing R]

private theorem longest_conjugate_eq_iff (n : ℕ) (a b : FinitaryPerm ℕ+) :
    longestElement n * a * longestElement n = b ↔
      a = longestElement n * b * longestElement n := by
  constructor
  · intro h
    have he := congrArg (fun w => longestElement n * w * longestElement n) h
    simpa only [conjugate_longest_twice] using he
  · intro h
    have he := congrArg (fun w => longestElement n * w * longestElement n) h
    simpa only [conjugate_longest_twice] using he

/-- Signed reversal sends finite Schubert representatives to the longest-conjugate class. -/
theorem signedRev_schubert_class (n : ℕ) (u : FinitaryPerm ℕ+)
    (p q : MvPolynomial (Fin n) R) (hp : initialRename R n p = schubert R u)
    (hq : initialRename R n q = schubert R (longestElement n * u * longestElement n)) :
    Ideal.Quotient.mk (symmetricIdeal R n) (signedRename R Fin.revPerm p) =
      Ideal.Quotient.mk (symmetricIdeal R n) q := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply (mem_symmetricIdeal_iff_coordinates n _).mpr
  intro w hw
  rw [map_sub, map_sub, initialRename_signedRev, hp, hq]
  have he := schubertFunctional_signed_longest (longestElement n * w * longestElement n)
    hw.conjugate_longest (schubert R u)
  rw [conjugate_longest_twice] at he
  rw [he, schubertFunctional_schubert, schubertFunctional_schubert]
  simp only [longest_conjugate_eq_iff, sub_self]

/-- Longest conjugation preserves every supported Schubert product coordinate over any ring. -/
theorem structureCoefficients_conjugate_longest (n : ℕ) (u v w : FinitaryPerm ℕ+)
    (hu : IsSupported n u) (hv : IsSupported n v) (hw : IsSupported n w) :
    structureCoefficients R u v w = structureCoefficients R
      (longestElement n * u * longestElement n) (longestElement n * v * longestElement n)
      (longestElement n * w * longestElement n) := by
  obtain ⟨pu, hpu⟩ := exists_initialRename_of_artin (schubert_mem_artinSpan (R := R) u hu)
  obtain ⟨pv, hpv⟩ := exists_initialRename_of_artin (schubert_mem_artinSpan (R := R) v hv)
  obtain ⟨qu, hqu⟩ := exists_initialRename_of_artin
    (schubert_mem_artinSpan (R := R) _ hu.conjugate_longest)
  obtain ⟨qv, hqv⟩ := exists_initialRename_of_artin
    (schubert_mem_artinSpan (R := R) _ hv.conjugate_longest)
  have huclass := signedRev_schubert_class n u pu qu hpu hqu
  have hvclass := signedRev_schubert_class n v pv qv hpv hqv
  have hprod : signedRename R Fin.revPerm (pu * pv) - qu * qv ∈ symmetricIdeal R n := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    rw [map_mul, map_mul, map_mul, huclass, hvclass]
  have h := schubertFunctional_symmetricIdeal hprod
    (longestElement n * w * longestElement n) hw.conjugate_longest
  rw [map_sub, map_sub, initialRename_signedRev] at h
  have hp : initialRename R n (pu * pv) = schubert R u * schubert R v := by
    rw [map_mul, hpu, hpv]
  have hq : initialRename R n (qu * qv) = schubert R (longestElement n * u * longestElement n) *
      schubert R (longestElement n * v * longestElement n) := by rw [map_mul, hqu, hqv]
  rw [hp, hq, schubertFunctional_signed_longest w hw] at h
  rw [structureCoefficients_apply, structureCoefficients_apply]
  exact sub_eq_zero.mp h

/-- Integer Schubert structure constants are preserved by ambient longest conjugation. -/
theorem structureConst_conjugate_longest (n : ℕ) (u v w : FinitaryPerm ℕ+)
    (hu : IsSupported n u) (hv : IsSupported n v) (hw : IsSupported n w) :
    structureConst u v w = structureConst
      (longestElement n * u * longestElement n) (longestElement n * v * longestElement n)
      (longestElement n * w * longestElement n) :=
  structureCoefficients_conjugate_longest n u v w hu hv hw

end

end SchubertPolynomial
