import SchubertForwardStability.SchubertPolynomials.Stability.ShiftConstants

/-! # Signed translation and finite reversal

Permutations in two initial intervals are signed translates exactly when
reversing their respective intervals gives the same permutation. The fixed
positions removed or inserted by the translation are part of this equivalence.
-/

namespace FinitaryPerm

/-- The value of a finite reversal written without truncated subtraction. -/
theorem longestElement_apply_int {n : ℕ} {i : ℕ+} (hi : (i : ℕ) ≤ n) :
    ((longestElement n i : ℕ) : ℤ) = (n : ℤ) + 1 - ((i : ℕ) : ℤ) := by
  have he := longestElement_apply_val n i hi
  have hp := i.pos
  omega

private theorem conjugate_reflect_int {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    (((longestElement n * w * longestElement n) (longestElement n i) : ℕ) : ℤ) =
      (n : ℤ) + 1 - ((w i : ℕ) : ℤ) := by
  simp only [mul_apply, longestElement_apply_twice]
  exact longestElement_apply_int ((hw.apply_le_iff i).mpr hi)

/-- Equal finite reversals give an admissible signed translation between the intervals. -/
theorem signedShift_of_conjugate_longest_eq {n m : ℕ} {u v : FinitaryPerm ℕ+}
    (hu : IsSupported n u) (hv : IsSupported m v)
    (h : longestElement n * u * longestElement n =
      longestElement m * v * longestElement m) : SignedShift ((m : ℤ) - (n : ℤ)) u v := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hp := i.pos
    have hin : (i : ℕ) ≤ n := by omega
    have hr := longestElement_apply_int hin
    have hab : m < (longestElement n i : ℕ) := by omega
    have he := congrArg (fun w : FinitaryPerm ℕ+ => w (longestElement n i)) h
    rw [hv.conjugate_longest _ hab] at he
    simp only [mul_apply, longestElement_apply_twice] at he
    exact (longestElement n).injective he
  · intro j hj
    have hp := j.pos
    have hjm : (j : ℕ) ≤ m := by omega
    have hr := longestElement_apply_int hjm
    have hab : n < (longestElement m j : ℕ) := by omega
    have he := congrArg (fun w : FinitaryPerm ℕ+ => w (longestElement m j)) h
    rw [hu.conjugate_longest _ hab] at he
    simp only [mul_apply, longestElement_apply_twice] at he
    exact (longestElement m).injective he.symm
  · intro i j hij
    by_cases hi : (i : ℕ) ≤ n
    · have hj : (j : ℕ) ≤ m := by omega
      have ha : longestElement n i = longestElement m j := by
        apply PNat.eq
        have hn := longestElement_apply_int hi
        have hm := longestElement_apply_int hj
        omega
      have he := congrArg
        (fun w : FinitaryPerm ℕ+ => ((w (longestElement n i) : ℕ) : ℤ)) h
      rw [conjugate_reflect_int hu i hi, ha, conjugate_reflect_int hv j hj] at he
      omega
    · have hj : m < (j : ℕ) := by omega
      rw [hu i (by omega), hv j hj]
      exact hij

/-- An admissible signed translation gives equal reversals of its source and target intervals. -/
theorem conjugate_longest_eq_of_signedShift {n m : ℕ} {u v : FinitaryPerm ℕ+}
    (hu : IsSupported n u) (hv : IsSupported m v)
    (h : SignedShift ((m : ℤ) - (n : ℤ)) u v) :
    longestElement n * u * longestElement n =
      longestElement m * v * longestElement m := by
  apply ext
  intro a
  by_cases hn : (a : ℕ) ≤ n
  · have hi : (longestElement n a : ℕ) ≤ n :=
      ((isSupported_longestElement n).apply_le_iff a).mpr hn
    have hir := longestElement_apply_int hn
    by_cases hm : (a : ℕ) ≤ m
    · have hj : (longestElement m a : ℕ) ≤ m :=
        ((isSupported_longestElement m).apply_le_iff a).mpr hm
      have hjr := longestElement_apply_int hm
      have ht := h.translate (longestElement n a) (longestElement m a) (by omega)
      have huval := longestElement_apply_int
        ((hu.apply_le_iff (longestElement n a)).mpr hi)
      have hvval := longestElement_apply_int
        ((hv.apply_le_iff (longestElement m a)).mpr hj)
      apply PNat.eq
      simp only [mul_apply]
      omega
    · have hfix := h.removed_fixed (longestElement n a) (by omega)
      rw [hv.conjugate_longest a (by omega)]
      simp only [mul_apply, hfix, longestElement_apply_twice]
  · by_cases hm : (a : ℕ) ≤ m
    · have hjr := longestElement_apply_int hm
      have hfix := h.inserted_fixed (longestElement m a) (by omega)
      rw [hu.conjugate_longest a (by omega)]
      simp only [mul_apply, hfix, longestElement_apply_twice]
    · exact (hu.conjugate_longest a (by omega)).trans
        (hv.conjugate_longest a (by omega)).symm

/-- Signed translation is equivalent to equality after reversing the two finite intervals. -/
theorem signedShift_iff_conjugate_longest {n m : ℕ} {u v : FinitaryPerm ℕ+}
    (hu : IsSupported n u) (hv : IsSupported m v) :
    SignedShift ((m : ℤ) - (n : ℤ)) u v ↔
      longestElement n * u * longestElement n =
        longestElement m * v * longestElement m :=
  ⟨conjugate_longest_eq_of_signedShift hu hv, signedShift_of_conjugate_longest_eq hu hv⟩

/-- A signed translate is supported in the translated interval, with a zero floor. -/
theorem SignedShift.isSupported {k : ℤ} {u v : FinitaryPerm ℕ+} {n : ℕ}
    (h : SignedShift k u v) (hu : IsSupported n u) :
    IsSupported ((n : ℤ) + k).toNat v := by
  intro j hj
  have hp : 0 < (((j : ℕ) : ℤ) - k).toNat := by omega
  let i : ℕ+ := ⟨(((j : ℕ) : ℤ) - k).toNat, hp⟩
  have hi : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) - k := by dsimp [i]; omega
  have hn : n < (i : ℕ) := by omega
  have ht := h.translate i j (by omega)
  rw [hu i hn] at ht
  apply PNat.eq
  omega

end FinitaryPerm
