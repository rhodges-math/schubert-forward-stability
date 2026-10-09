import SchubertForwardStability.Permutations.Classes.Patterns.PatternJoin
import SchubertForwardStability.Permutations.Classes.Patterns.PatternTriples

/-! # Pattern avoidance in a lower-left maximum join

Every `231` occurrence in `joinLow a b u v` lies in one of its two factors, so the join
avoids `231` exactly when both factors do.
-/

namespace PermutationPattern

open FinitaryPerm

/-- A `231` occurrence in the left factor remains an occurrence in the joined permutation. -/
theorem contains231_joinLow_left (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (h : Contains a p231 u) : Contains (a + b + 1) p231 (joinLow a b u v) := by
  obtain ⟨i, j, k, hij, hjk, hk, hki, hijv⟩ := (contains231_iff a u).mp h
  have hi : (i : ℕ) ≤ a := by
    change (i : ℕ) < (j : ℕ) at hij
    change (j : ℕ) < (k : ℕ) at hjk
    omega
  have hj : (j : ℕ) ≤ a := by
    change (j : ℕ) < (k : ℕ) at hjk
    omega
  apply (contains231_iff _ _).mpr
  refine ⟨i, j, k, hij, hjk, by omega, ?_, ?_⟩
  · rwa [joinLow_apply_left a b u v k hk, joinLow_apply_left a b u v i hi]
  · rwa [joinLow_apply_left a b u v i hi, joinLow_apply_left a b u v j hj]

/-- A `231` occurrence in the right factor remains an occurrence in the joined permutation. -/
theorem contains231_joinLow_right (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (h : Contains b p231 v) :
    Contains (a + b + 1) p231 (joinLow a b u v) := by
  obtain ⟨i, j, k, hij, hjk, hk, hki, hijv⟩ := (contains231_iff b v).mp h
  have hi : (i : ℕ) ≤ b := by
    change (i : ℕ) < (j : ℕ) at hij
    change (j : ℕ) < (k : ℕ) at hjk
    omega
  have hj : (j : ℕ) ≤ b := by
    change (j : ℕ) < (k : ℕ) at hjk
    omega
  apply (contains231_iff _ _).mpr
  refine ⟨shiftPosition (a + 1) i, shiftPosition (a + 1) j,
    shiftPosition (a + 1) k, ?_, ?_, ?_, ?_, ?_⟩
  · change a + 1 + (i : ℕ) < a + 1 + (j : ℕ)
    exact Nat.add_lt_add_left hij _
  · change a + 1 + (j : ℕ) < a + 1 + (k : ℕ)
    exact Nat.add_lt_add_left hjk _
  · change a + 1 + (k : ℕ) ≤ a + b + 1
    omega
  · rw [joinLow_apply_right a b u v hu k hk, joinLow_apply_right a b u v hu i hi]
    change a + (v k : ℕ) < a + (v i : ℕ)
    exact Nat.add_lt_add_left hki _
  · rw [joinLow_apply_right a b u v hu i hi, joinLow_apply_right a b u v hu j hj]
    change a + (v i : ℕ) < a + (v j : ℕ)
    exact Nat.add_lt_add_left hijv _

/-- Every `231` occurrence in a bounded join lies wholly in one of its two factors. -/
theorem contains231_joinLow_iff (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) :
    Contains (a + b + 1) p231 (joinLow a b u v) ↔
      Contains a p231 u ∨ Contains b p231 v := by
  constructor
  · intro h
    obtain ⟨i, j, k, hij, hjk, hk, hki, hijv⟩ := (contains231_iff _ _).mp h
    change (i : ℕ) < (j : ℕ) at hij
    change (j : ℕ) < (k : ℕ) at hjk
    by_cases hLeft : (k : ℕ) ≤ a
    · have hi : (i : ℕ) ≤ a := by omega
      have hj : (j : ℕ) ≤ a := by omega
      rw [joinLow_apply_left a b u v k hLeft, joinLow_apply_left a b u v i hi] at hki
      rw [joinLow_apply_left a b u v i hi, joinLow_apply_left a b u v j hj] at hijv
      exact Or.inl ((contains231_iff a u).mpr ⟨i, j, k, hij, hjk, hLeft, hki, hijv⟩)
    by_cases hRight : a + 1 < (i : ℕ)
    · obtain ⟨ti, hiEq⟩ := (mem_range_shiftPosition (a + 1) i).mpr hRight
      obtain ⟨tj, hjEq⟩ := (mem_range_shiftPosition (a + 1) j).mpr (by omega)
      obtain ⟨tk, hkEq⟩ := (mem_range_shiftPosition (a + 1) k).mpr (by omega)
      simp only [← hiEq, ← hjEq, ← hkEq] at hij hjk hk hki hijv
      change a + 1 + (ti : ℕ) < a + 1 + (tj : ℕ) at hij
      change a + 1 + (tj : ℕ) < a + 1 + (tk : ℕ) at hjk
      change a + 1 + (tk : ℕ) ≤ a + b + 1 at hk
      have hiB : (ti : ℕ) ≤ b := by omega
      have hjB : (tj : ℕ) ≤ b := by omega
      have hkB : (tk : ℕ) ≤ b := by omega
      rw [joinLow_apply_right a b u v hu tk hkB,
        joinLow_apply_right a b u v hu ti hiB] at hki
      rw [joinLow_apply_right a b u v hu ti hiB,
        joinLow_apply_right a b u v hu tj hjB] at hijv
      change a + (v tk : ℕ) < a + (v ti : ℕ) at hki
      change a + (v ti : ℕ) < a + (v tj : ℕ) at hijv
      exact Or.inr ((contains231_iff b v).mpr
        ⟨ti, tj, tk, by change (ti : ℕ) < (tj : ℕ); omega,
          by change (tj : ℕ) < (tk : ℕ); omega, hkB,
          by change (v tk : ℕ) < (v ti : ℕ); omega,
          by change (v ti : ℕ) < (v tj : ℕ); omega⟩)
    by_cases hi : (i : ℕ) ≤ a
    · have hiValue : (joinLow a b u v i : ℕ) ≤ a := by
        rw [joinLow_apply_left a b u v i hi]
        exact (hu.apply_le_iff i).mpr hi
      by_cases hkMax : (k : ℕ) = a + 1
      · have hkEq : k = a.succPNat := PNat.eq hkMax
        rw [hkEq, joinLow_apply_max a b u v hu hv] at hki
        change a + b + 1 < (joinLow a b u v i : ℕ) at hki
        omega
      · obtain ⟨tk, hkEq⟩ := (mem_range_shiftPosition (a + 1) k).mpr (by omega)
        have hkB : (tk : ℕ) ≤ b := by
          have h := congrArg PNat.val hkEq
          change a + 1 + (tk : ℕ) = (k : ℕ) at h
          omega
        rw [← hkEq, joinLow_apply_right a b u v hu tk hkB] at hki
        change a + (v tk : ℕ) < (joinLow a b u v i : ℕ) at hki
        have := (v tk).pos
        omega
    · have hiEq : i = a.succPNat := PNat.eq (by change (i : ℕ) = a + 1; omega)
      rw [hiEq, joinLow_apply_max a b u v hu hv] at hijv
      change a + b + 1 < (joinLow a b u v j : ℕ) at hijv
      have hjBound : (joinLow a b u v j : ℕ) ≤ a + b + 1 :=
        ((joinLow_supported a b u v hu hv).apply_le_iff j).mpr (by omega)
      omega
  · rintro (h | h)
    · exact contains231_joinLow_left a b u v h
    · exact contains231_joinLow_right a b u v hu h

/-- A bounded maximum join avoids `231` exactly when both factors avoid it. -/
theorem joinLow_avoiding231_iff (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) :
    joinLow a b u v ∈ avoiding (a + b + 1) p231 ↔
      u ∈ avoiding a p231 ∧ v ∈ avoiding b p231 := by
  simp only [mem_avoiding, hu, hv, joinLow_supported a b u v hu hv, true_and,
    contains231_joinLow_iff a b u v hu hv, not_or]

end PermutationPattern
