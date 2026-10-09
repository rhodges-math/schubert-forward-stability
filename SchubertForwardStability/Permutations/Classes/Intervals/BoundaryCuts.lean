import SchubertForwardStability.Permutations.Classes.Intervals.IntervalProducts

/-! # Boundary absence and endpoint fixing

The predecessor boundary symbol vanishes exactly when the initial factor
fixes the shared endpoint. This follows from cut preservation.
-/

namespace FinitaryPerm

/-- A zero boundary symbol is equivalent to preserving its positive initial cut. -/
theorem blockTag_eq_zero_iff_cut (n : ℕ) (w : FinitaryPerm ℕ+) (hw : w ∈ boolean n)
    (i : ℕ+) : blockTag n w (i : ℕ) = .zero ↔ PreservesInitial w i := by
  have h := (mem_boolean _ _).mp hw
  have hTag : blockTag n w (i : ℕ) = .zero ↔ i ∉ w.lexFirstReducedWord := by
    constructor
    · intro hZero hi
      exact ((blockTag_ne_zero_iff n w i).mpr ⟨i.pos,
        lexFirst_letter_bound w h.1 i hi, (generatorPresent_iff_mem w i).mpr hi⟩) hZero
    · intro hAbsent
      by_contra hZero
      exact hAbsent ((generatorPresent_iff_mem w i).mp
        ((blockTag_ne_zero_iff n w i).mp hZero).2.2)
  have hCut := (preservesInitial_word_iff w.lexFirstReducedWord h.2.lexFirst_nodup i).symm
  rw [(isReducedWordIn_lexFirst w).1.1] at hCut
  exact hTag.trans hCut

/-- Multiplication by an initial-cut-preserving right factor does not change that property. -/
theorem PreservesInitial.product_right_iff (u v : FinitaryPerm ℕ+) (i : ℕ+)
    (hv : PreservesInitial v i) : PreservesInitial (u * v) i ↔ PreservesInitial u i := by
  constructor
  · intro h
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using h.mul hv.inv
  · intro h
    exact h.mul hv

/-- At a supported last position, preserving the preceding cut is exactly endpoint fixing. -/
theorem IsSupported.preserves_prev_iff {w : FinitaryPerm ℕ+} (r i : ℕ+)
    (hw : IsSupported (r : ℕ) w) (hr : r = i + 1) :
    PreservesInitial w i ↔ w r = r := by
  have hLess : i < r := by rw [hr]; exact Nat.lt_succ_self (i : ℕ)
  constructor
  · intro h
    have hAbove : i < w r := lt_of_not_ge fun hLe => (not_le_of_gt hLess) ((h r).mp hLe)
    have hBound : w r ≤ r := (hw.apply_le_iff r).mpr le_rfl
    apply PNat.eq
    have hR := congrArg PNat.val hr
    change (r : ℕ) = (i : ℕ) + 1 at hR
    change (i : ℕ) < (w r : ℕ) at hAbove
    change (w r : ℕ) ≤ (r : ℕ) at hBound
    omega
  · intro hFixed
    have hSmall := (hw.fixed_last_iff r).mpr hFixed
    have hPred : (r : ℕ) - 1 = (i : ℕ) := by
      rw [hr]
      change (i : ℕ) + 1 - 1 = (i : ℕ)
      omega
    rw [hPred] at hSmall
    exact hSmall.apply_le_iff

/-- A predecessor symbol is zero exactly when the initial factor fixes the endpoint. -/
theorem boundary_zero_iff_left_fixed (n : ℕ) (r : ℕ+) (u v : FinitaryPerm ℕ+)
    (hu : u ∈ booleanOn n (positions (r : ℕ)))
    (hv : v ∈ booleanOn n (positionInterval (r : ℕ) n)) :
    blockTag n (u * v) ((r : ℕ) - 1) = .zero ↔ u r = r := by
  have hU := (mem_booleanOn _ _ _).mp hu
  have hV := (mem_booleanOn _ _ _).mp hv
  have hSupport : IsSupported (r : ℕ) u := fun k hk =>
    hU.2 k (by rw [mem_positions]; exact not_le_of_gt hk)
  by_cases hFirst : r = 1
  · subst r
    change blockTag n (u * v) 0 = .zero ↔ u 1 = 1
    rw [blockTag_zero]
    exact iff_of_true rfl (le_antisymm ((hSupport.apply_le_iff 1).mpr le_rfl) one_le)
  · let i : ℕ+ := ⟨(r : ℕ) - 1, by
      have hp := r.pos
      have hNe : (r : ℕ) ≠ 1 := fun h => hFirst (PNat.eq h)
      omega⟩
    have hr : r = i + 1 := by
      apply PNat.eq
      change (r : ℕ) = (r : ℕ) - 1 + 1
      have hp := r.pos
      omega
    have hFix : ∀ k : ℕ+, k < r → v k = k := by
      intro k hk
      exact hV.2 k (by rw [mem_positionInterval]; exact fun h => (not_le_of_gt hk) h.2)
    have hPreserve := preservesInitial_of_fixed_below v r i hFix
      (by rw [hr]; exact Nat.lt_succ_self (i : ℕ))
    change blockTag n (u * v) (i : ℕ) = .zero ↔ u r = r
    rw [blockTag_eq_zero_iff_cut n _ (boolean_interval_product n r u v hu hv) i,
      PreservesInitial.product_right_iff u v i hPreserve]
    exact hSupport.preserves_prev_iff r i hr

end FinitaryPerm
