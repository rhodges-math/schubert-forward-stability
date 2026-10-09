import SchubertForwardStability.Permutations.Classes.Patterns.PatternJoin
import SchubertForwardStability.Permutations.Statistics.Records

/-! # Records in a lower-left maximum join

The records of `joinLow a b u v` in size `a+b+1` are the records of `u` together with the
maximum position `a+1`.
-/

namespace PermutationPattern

open FinitaryPerm
open scoped Classical

/-- Records before a joined maximum are exactly the records of its left factor. -/
theorem joinLow_isRecord_left (a b : ℕ) (u v : FinitaryPerm ℕ+) (i : ℕ+)
    (hi : (i : ℕ) ≤ a) : IsRecord (joinLow a b u v) i ↔ IsRecord u i := by
  constructor <;> intro h j hj
  · have hjBound : (j : ℕ) ≤ a := by
      change (j : ℕ) < (i : ℕ) at hj
      omega
    have hx := h j hj
    rwa [joinLow_apply_left a b u v j hjBound, joinLow_apply_left a b u v i hi] at hx
  · have hjBound : (j : ℕ) ≤ a := by
      change (j : ℕ) < (i : ℕ) at hj
      omega
    rw [joinLow_apply_left a b u v j hjBound, joinLow_apply_left a b u v i hi]
    exact h j hj

/-- The newly inserted maximum is a record of the joined permutation. -/
theorem joinLow_isRecord_max (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) :
    IsRecord (joinLow a b u v) a.succPNat := by
  intro i hi
  have hiBound : (i : ℕ) ≤ a := by
    change (i : ℕ) < a + 1 at hi
    omega
  rw [joinLow_apply_left a b u v i hiBound, joinLow_apply_max a b u v hu hv]
  have hValue := (hu.apply_le_iff i).mpr hiBound
  change (u i : ℕ) < a + b + 1
  omega

/-- No ambient position after the inserted maximum is a joined record. -/
theorem joinLow_notRecord_right (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) (j : ℕ+)
    (hj : a + 1 < (j : ℕ)) (hn : (j : ℕ) ≤ a + b + 1) :
    ¬IsRecord (joinLow a b u v) j := by
  intro hRecord
  have h := hRecord a.succPNat hj
  rw [joinLow_apply_max a b u v hu hv] at h
  have hBound := ((joinLow_supported a b u v hu hv).apply_le_iff j).mpr hn
  change a + b + 1 < (joinLow a b u v j : ℕ) at h
  omega

/-- The ambient joined record set is the left record set with the maximum position inserted. -/
theorem joinLow_recordSet (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) :
    recordSet (a + b + 1) (joinLow a b u v) = insert a.succPNat (recordSet a u) := by
  ext j
  simp only [mem_recordSet, Finset.mem_insert]
  constructor
  · rintro ⟨hj, hRecord⟩
    by_cases he : j = a.succPNat
    · exact Or.inl he
    · have hNe : (j : ℕ) ≠ a + 1 := fun h => he (PNat.eq h)
      have hLeft : (j : ℕ) ≤ a := by
        by_contra hn
        exact (joinLow_notRecord_right a b u v hu hv j (by omega) hj) hRecord
      exact Or.inr ⟨hLeft, (joinLow_isRecord_left a b u v j hLeft).mp hRecord⟩
  · rintro (he | ⟨hj, hRecord⟩)
    · subst j
      exact ⟨by change a + 1 ≤ a + b + 1; omega, joinLow_isRecord_max a b u v hu hv⟩
    · exact ⟨by omega, (joinLow_isRecord_left a b u v j hj).mpr hRecord⟩

end PermutationPattern
