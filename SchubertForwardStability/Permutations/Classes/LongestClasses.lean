import SchubertForwardStability.Permutations.Classes.LongestWords
import SchubertForwardStability.Permutations.Classes.Grassmannian

/-! # Longest conjugation of permutation classes

The reflected descent sets have the same cardinality. Longest conjugation
preserves support, Booleanity and the Grassmannian property, including at size zero.
-/

namespace FinitaryPerm

open scoped Classical

/-- Longest conjugation preserves support containment in both directions. -/
theorem isSupported_conjugate_longest_iff (n : ℕ) (w : FinitaryPerm ℕ+) :
    IsSupported n (longestElement n * w * longestElement n) ↔ IsSupported n w := by
  constructor
  · intro hw
    simpa only [conjugate_longest_twice] using hw.conjugate_longest
  · exact IsSupported.conjugate_longest

/-- Longest conjugation reflects an adjacent descent to the reflected diagram letter. -/
theorem hasDescent_conjugate_longest {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) {i : ℕ+} (hi : (i : ℕ) < n) :
    HasDescent (longestElement n * w * longestElement n) (longestElement (n - 1) i) ↔
      HasDescent w i := by
  have hl : longestElement n (longestElement (n - 1) i) = i + 1 := by
    rw [←longestElement_next_letter hi, longestElement_apply_twice]
  have hr : longestElement n (longestElement (n - 1) i + 1) = i := by
    rw [←longestElement_left_letter hi, longestElement_apply_twice]
  simp only [HasDescent, mul_apply, hl, hr]
  exact longestElement_lt_iff ((hw.apply_le_iff i).mpr (Nat.le_of_lt hi))
    ((hw.apply_le_iff (i + 1)).mpr (by change (i : ℕ) + 1 ≤ n; omega))

/-- The descent cardinality is unchanged by ambient longest conjugation. -/
theorem descent_card_conjugate_longest {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) :
    (longestElement n * w * longestElement n).descentSet.card = w.descentSet.card := by
  symm
  refine Finset.card_bij (fun i _ => longestElement (n - 1) i) ?_ ?_ ?_
  · intro i hi
    have hd := (mem_descentSet w i).mp hi
    exact (mem_descentSet _ _).mpr
      ((hasDescent_conjugate_longest hw (hw.descent_lt hd)).mpr hd)
  · intro i _ j _ hij
    exact (longestElement (n - 1)).injective hij
  · intro i hi
    have hd := (mem_descentSet _ i).mp hi
    have hr := (hasDescent_conjugate_longest hw.conjugate_longest
      (hw.conjugate_longest.descent_lt hd)).mpr hd
    rw [conjugate_longest_twice] at hr
    exact ⟨longestElement (n - 1) i, (mem_descentSet _ _).mpr hr,
      longestElement_apply_twice (n - 1) i⟩

/-- Ambient longest conjugation preserves the Grassmannian property. -/
theorem isGrassmannian_conjugate_longest {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) :
    IsGrassmannian (longestElement n * w * longestElement n) ↔ IsGrassmannian w := by
  simp only [IsGrassmannian, descent_card_conjugate_longest hw]

/-- Longest conjugation preserves membership in the ambient symmetric group. -/
theorem mem_symmetric_conjugate_longest (n : ℕ) (w : FinitaryPerm ℕ+) :
    longestElement n * w * longestElement n ∈ symmetricGroup n ↔ w ∈ symmetricGroup n := by
  simp only [mem_symmetricGroup, isSupported_conjugate_longest_iff]

/-- Longest conjugation preserves membership in the ambient Boolean family. -/
theorem mem_boolean_conjugate_longest (n : ℕ) (w : FinitaryPerm ℕ+) :
    longestElement n * w * longestElement n ∈ boolean n ↔ w ∈ boolean n := by
  simp only [mem_boolean, isSupported_conjugate_longest_iff]
  constructor
  · rintro ⟨hw, hb⟩
    exact ⟨hw, (isBoolean_conjugate_longest hw).mp hb⟩
  · rintro ⟨hw, hb⟩
    exact ⟨hw, (isBoolean_conjugate_longest hw).mpr hb⟩

/-- Longest conjugation preserves membership in the ambient Grassmannian family. -/
theorem mem_grass_conjugate_longest (n : ℕ) (w : FinitaryPerm ℕ+) :
    longestElement n * w * longestElement n ∈ grassmannian n ↔ w ∈ grassmannian n := by
  simp only [mem_grassmannian, isSupported_conjugate_longest_iff]
  constructor
  · rintro ⟨hw, hg⟩
    exact ⟨hw, (isGrassmannian_conjugate_longest hw).mp hg⟩
  · rintro ⟨hw, hg⟩
    exact ⟨hw, (isGrassmannian_conjugate_longest hw).mpr hg⟩

end FinitaryPerm
