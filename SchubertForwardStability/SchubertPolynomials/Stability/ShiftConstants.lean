import SchubertForwardStability.SchubertPolynomials.Coinvariants.LongestProducts
import SchubertForwardStability.SchubertPolynomials.Stability.RightShift

/-! # Transported Schubert coordinates under an initial fixed position

Longest reversal turns insertion of an initial fixed position into extension
by a final fixed position. The finite longest coefficient symmetry therefore
preserves the coordinates whose three indices are all shifted together.

## References

* N. Li, *A canonical expansion of the product of two Stanley symmetric functions*, 2014.
-/

namespace FinitaryPerm

/-- Inserting an initial fixed position increases an ambient support bound by one. -/
theorem IsSupported.shiftRight {n : ℕ} {w : FinitaryPerm ℕ+} (hw : IsSupported n w) :
    IsSupported (n + 1) (shiftRight w) := by
  intro j hj
  let i : ℕ+ := ⟨(j : ℕ) - 1, by have hp := j.pos; omega⟩
  have he : i + 1 = j := by
    apply PNat.eq
    change (j : ℕ) - 1 + 1 = (j : ℕ)
    have hp := j.pos
    omega
  rw [←he, shiftRight_apply_add_one, hw i (by dsimp [i]; omega)]

/-- Longest reversal of an initially shifted permutation is the original longest conjugate. -/
theorem conjugate_longest_shiftRight {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) :
    longestElement (n + 1) * shiftRight w * longestElement (n + 1) =
      longestElement n * w * longestElement n := by
  apply ext
  intro i
  by_cases hi : (i : ℕ) ≤ n
  · have hleft : longestElement (n + 1) i = longestElement n i + 1 := by
      simpa only [Nat.add_sub_cancel] using
        (longestElement_left_letter (n := n + 1) (i := i) (by omega))
    have hb : (w (longestElement n i) : ℕ) ≤ n :=
      (hw.apply_le_iff _).mpr (((isSupported_longestElement n).apply_le_iff i).mpr hi)
    have hnext : longestElement (n + 1) (w (longestElement n i) + 1) =
        longestElement n (w (longestElement n i)) := by
      simpa only [Nat.add_sub_cancel] using
        (longestElement_next_letter (n := n + 1) (i := w (longestElement n i)) (by omega))
    simp only [mul_apply]
    rw [hleft, shiftRight_apply_add_one, hnext]
  · by_cases hj : (i : ℕ) ≤ n + 1
    · have hone : longestElement (n + 1) i = 1 := by
        apply PNat.eq
        rw [longestElement_apply_val (n + 1) i hj]
        change n + 1 + 1 - (i : ℕ) = 1
        omega
      have hlast : longestElement (n + 1) 1 = i := by
        apply PNat.eq
        rw [longestElement_apply_val (n + 1) 1 (by change 1 ≤ n + 1; omega)]
        change n + 1 + 1 - 1 = (i : ℕ)
        omega
      rw [hw.conjugate_longest i (by omega)]
      simp only [mul_apply, hone, shiftRight_apply_one, hlast]
    · exact (hw.shiftRight.conjugate_longest i (by omega)).trans
        (hw.conjugate_longest i (by omega)).symm

end FinitaryPerm

namespace SchubertPolynomial

noncomputable section

open FinitaryPerm

variable {R : Type*} [CommRing R]

/-- Inserting the same initial fixed position in all three indices preserves product coordinates. -/
theorem structureCoefficients_shiftRight (u v w : FinitaryPerm ℕ+) :
    structureCoefficients R (shiftRight u) (shiftRight v) (shiftRight w) =
      structureCoefficients R u v w := by
  let n := max u.forwardStability (max v.forwardStability w.forwardStability)
  have hu : IsSupported n u := u.isSupported_forwardStability.mono (le_max_left _ _)
  have hv : IsSupported n v := v.isSupported_forwardStability.mono
    ((le_max_left _ _).trans (le_max_right _ _))
  have hw : IsSupported n w := w.isSupported_forwardStability.mono
    ((le_max_right _ _).trans (le_max_right _ _))
  have h := structureCoefficients_conjugate_longest (R := R) (n + 1)
    (shiftRight u) (shiftRight v) (shiftRight w) hu.shiftRight hv.shiftRight hw.shiftRight
  rw [conjugate_longest_shiftRight hu, conjugate_longest_shiftRight hv,
    conjugate_longest_shiftRight hw] at h
  exact h.trans (structureCoefficients_conjugate_longest n u v w hu hv hw).symm

/-- Integer structure constants are unchanged when all three indices acquire
an initial fixed point. -/
theorem structureConst_shiftRight (u v w : FinitaryPerm ℕ+) :
    structureConst (shiftRight u) (shiftRight v) (shiftRight w) = structureConst u v w :=
  structureCoefficients_shiftRight u v w

end

end SchubertPolynomial
