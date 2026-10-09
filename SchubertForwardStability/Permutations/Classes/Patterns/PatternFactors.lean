import SchubertForwardStability.Permutations.Finitary.SuffixMap
import SchubertForwardStability.Permutations.Classes.Patterns.PatternJoinAvoidance
import SchubertForwardStability.Permutations.Classes.Patterns.PatternValues

/-! # Recovering the factors on either side of a maximum

A permutation of size `a+b+1` with its maximum at position `a+1`, whose first `a` values are
at most `a`, is a lower-left maximum join `joinLow a b u v`. In particular, every
`231`-avoider with its maximum at position `a+1` is the join of two `231`-avoiders.
-/

namespace PermutationPattern

open FinitaryPerm

/-- A bounded permutation with a closed low prefix reconstructs as a maximum join. -/
theorem exists_joinLow (a b : ℕ) (w : FinitaryPerm ℕ+)
    (hw : IsSupported (a + b + 1) w)
    (hm : (w a.succPNat : ℕ) = a + b + 1)
    (hLeft : ∀ i : ℕ+, (i : ℕ) ≤ a → (w i : ℕ) ≤ a) :
    ∃ u v : FinitaryPerm ℕ+, IsSupported a u ∧ IsSupported b v ∧
      w = joinLow a b u v := by
  obtain ⟨u, hu, hAgree⟩ := exists_initial_agree a w hLeft
  have hRight : ∀ t : ℕ+, (t : ℕ) ≤ b →
      a < (w (shiftPosition (a + 1) t) : ℕ) ∧
        (w (shiftPosition (a + 1) t) : ℕ) ≤ a + b := by
    intro t ht
    have hPos := t.pos
    have hAbove : a < (shiftPosition (a + 1) t : ℕ) := by
      change a < a + 1 + (t : ℕ)
      omega
    have hLow := values_above_prefix a w u hu hAgree _ hAbove
    have hBound : (w (shiftPosition (a + 1) t) : ℕ) ≤ a + b + 1 :=
      (hw.apply_le_iff _).mpr (by change a + 1 + (t : ℕ) ≤ a + b + 1; omega)
    have hNe : (w (shiftPosition (a + 1) t) : ℕ) ≠ a + b + 1 := by
      intro he
      have hEqual := w.injective (PNat.eq (he.trans hm.symm))
      have hValue := congrArg PNat.val hEqual
      change a + 1 + (t : ℕ) = a + 1 at hValue
      omega
    exact ⟨hLow, by omega⟩
  obtain ⟨v, hv, hSuffix⟩ := exists_suffix_agree a b w hRight
  refine ⟨u, v, hu, hv, ?_⟩
  apply FinitaryPerm.ext
  intro j
  by_cases hjLeft : (j : ℕ) ≤ a
  · rw [joinLow_apply_left a b u v j hjLeft]
    exact (hAgree j hjLeft).symm
  by_cases hjAbove : a + b + 1 < (j : ℕ)
  · rw [hw j hjAbove, joinLow_supported a b u v hu hv j hjAbove]
  have hj : (j : ℕ) ≤ a + b + 1 := le_of_not_gt hjAbove
  by_cases hjMax : (j : ℕ) = a + 1
  · have he : j = a.succPNat := PNat.eq hjMax
    rw [he, joinLow_apply_max a b u v hu hv]
    exact PNat.eq hm
  · obtain ⟨t, hEq⟩ := (mem_range_shiftPosition (a + 1) j).mpr (by omega)
    have ht : (t : ℕ) ≤ b := by
      have hValue := congrArg PNat.val hEq
      change a + 1 + (t : ℕ) = (j : ℕ) at hValue
      omega
    rw [← hEq, joinLow_apply_right a b u v hu t ht]
    exact (hSuffix t ht).symm

/-- Every `231`-avoider with a specified maximum position has two avoiding join factors. -/
theorem exists_joinLow_avoiding231 (a b : ℕ) (w : FinitaryPerm ℕ+)
    (hw : w ∈ avoiding (a + b + 1) p231)
    (hm : (w a.succPNat : ℕ) = a + b + 1) :
    ∃ u v : FinitaryPerm ℕ+, u ∈ avoiding a p231 ∧ v ∈ avoiding b p231 ∧
      w = joinLow a b u v := by
  have hs := ((mem_avoiding _ _ _).mp hw).1
  have hLeft : ∀ i : ℕ+, (i : ℕ) ≤ a → (w i : ℕ) ≤ a := by
    intro i hi
    have h := avoiding231_left_values (a + b + 1) w hw a.succPNat
      (by change a + 1 ≤ a + b + 1; omega) hm i
      (by change (i : ℕ) < a + 1; omega)
    change (w i : ℕ) < a + 1 at h
    omega
  obtain ⟨u, v, hu, hv, hEqual⟩ := exists_joinLow a b w hs hm hLeft
  have hAvoid := (joinLow_avoiding231_iff a b u v hu hv).mp (hEqual ▸ hw)
  exact ⟨u, v, hAvoid.1, hAvoid.2, hEqual⟩

end PermutationPattern
