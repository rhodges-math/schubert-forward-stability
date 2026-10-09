import SchubertForwardStability.Permutations.Classes.Intervals.BooleanIntervals

/-! # Endpoint conditions for interval factors

Fixing the shared endpoint is equivalent to restricting either factor to
its smaller interval. A supported permutation has a record at its final
position precisely when that endpoint is fixed.
-/

namespace FinitaryPerm

/-- Removing the last supported position is equivalent to fixing that position. -/
theorem IsSupported.fixed_last_iff {w : FinitaryPerm ℕ+} (r : ℕ+)
    (hw : IsSupported (r : ℕ) w) : IsSupported ((r : ℕ) - 1) w ↔ w r = r := by
  constructor
  · intro h
    exact h r (Nat.sub_lt r.pos (by decide : 0 < 1))
  · intro hr k hk
    by_cases hkr : k = r
    · simpa only [hkr] using hr
    · apply hw k
      have hNe : (k : ℕ) ≠ (r : ℕ) := fun he => hkr (PNat.eq he)
      have hp := r.pos
      omega

/-- A record at the last supported position is equivalent to fixing that endpoint. -/
theorem IsSupported.isRecord_last_iff {w : FinitaryPerm ℕ+} (r : ℕ+)
    (hw : IsSupported (r : ℕ) w) : IsRecord w r ↔ w r = r := by
  constructor
  · intro hr
    by_contra hNe
    have hImage : w r ≤ r := (hw.apply_le_iff r).mpr le_rfl
    have hInv : w⁻¹ r ≤ r := (hw.apply_le_iff (w⁻¹ r)).mp (by
      rw [apply_inv_apply])
    have hInvNe : w⁻¹ r ≠ r := fun he => hNe (by
      have h := congrArg (fun k : ℕ+ => w k) he
      simpa only [apply_inv_apply] using h.symm)
    have hc := hr (w⁻¹ r) (lt_of_le_of_ne hInv hInvNe)
    rw [apply_inv_apply] at hc
    exact (not_lt_of_ge hImage) hc
  · intro hr k hk
    rw [hr]
    have hImage : w k ≤ r := (hw.apply_le_iff k).mpr hk.le
    exact lt_of_le_of_ne hImage (fun he => (ne_of_lt hk) (w.injective (he.trans hr.symm)))

/-- An initial Boolean factor lies in the preceding interval exactly when its endpoint is fixed. -/
theorem mem_booleanOn_initial_pred_iff (n : ℕ) (r : ℕ+) (w : FinitaryPerm ℕ+)
    (hw : w ∈ booleanOn n (positions (r : ℕ))) :
    w ∈ booleanOn n (positions ((r : ℕ) - 1)) ↔ w r = r := by
  have h := (mem_booleanOn _ _ _).mp hw
  have hs : IsSupported (r : ℕ) w := fun k hk =>
    h.2 k (by rw [mem_positions]; exact not_le_of_gt hk)
  constructor
  · intro hSmall
    exact ((mem_booleanOn _ _ _).mp hSmall).2 r (by
      rw [mem_positions]
      exact not_le_of_gt (Nat.sub_lt r.pos (by decide : 0 < 1)))
  · intro hFixed
    have hSmall := (hs.fixed_last_iff r).mpr hFixed
    exact (mem_booleanOn _ _ _).mpr ⟨h.1, fun k hk => hSmall k
      (lt_of_not_ge (by simpa only [mem_positions] using hk))⟩

/-- A final Boolean factor lies in the next interval exactly when its endpoint is fixed. -/
theorem mem_booleanOn_interval_next_iff (n : ℕ) (r : ℕ+) (w : FinitaryPerm ℕ+)
    (hw : w ∈ booleanOn n (positionInterval (r : ℕ) n)) :
    w ∈ booleanOn n (positionInterval ((r : ℕ) + 1) n) ↔ w r = r := by
  have h := (mem_booleanOn _ _ _).mp hw
  constructor
  · intro hSmall
    exact ((mem_booleanOn _ _ _).mp hSmall).2 r (by
      rw [mem_positionInterval]
      exact fun h => (Nat.not_succ_le_self (r : ℕ)) h.2)
  · intro hr
    apply (mem_booleanOn _ _ _).mpr
    refine ⟨h.1, ?_⟩
    intro k hk
    by_cases hkr : k = r
    · simpa only [hkr] using hr
    · apply h.2 k
      intro hOld
      apply hk
      rw [mem_positionInterval] at hOld ⊢
      have hNe : (k : ℕ) ≠ (r : ℕ) := fun he => hkr (PNat.eq he)
      exact ⟨hOld.1, by omega⟩

end FinitaryPerm
