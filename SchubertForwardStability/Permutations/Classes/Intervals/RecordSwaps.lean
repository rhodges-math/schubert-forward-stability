import SchubertForwardStability.Permutations.Classes.ReducedWords
import SchubertForwardStability.Permutations.Statistics.Records

/-! # Records under endpoint-adjacent transpositions

Right multiplication exchanges positions while left multiplication exchanges
values. At a support endpoint these operations have explicit record effects.
-/

namespace FinitaryPerm

private theorem pnat_lt_succ (i : ℕ+) : i < i + 1 := by
  change (i : ℕ) < (i : ℕ) + 1
  omega

/-- An adjacent transposition fixes every strictly smaller positive index. -/
theorem simpleTransposition_apply_below (i j : ℕ+) (hj : j < i) :
    simpleTransposition i j = j := by
  apply swap_apply_of_ne (ne_of_lt hj)
  exact ne_of_lt (hj.trans (pnat_lt_succ i))

/-- Exchanging the top value with its successor preserves order below the top value. -/
theorem simpleTransposition_lt_below (i a b : ℕ+) (ha : a ≤ i) (hb : b ≤ i) :
    simpleTransposition i a < simpleTransposition i b ↔ a < b := by
  by_cases hai : a = i
  · subst a
    rw [simpleTransposition_apply_left]
    by_cases hbi : b = i
    · subst b
      simp
    · have hbl : b < i := lt_of_le_of_ne hb hbi
      rw [simpleTransposition_apply_below i b hbl]
      exact iff_of_false (not_lt_of_ge (hbl.le.trans (pnat_lt_succ i).le))
        (not_lt_of_ge hb)
  · have hal : a < i := lt_of_le_of_ne ha hai
    rw [simpleTransposition_apply_below i a hal]
    by_cases hbi : b = i
    · subst b
      rw [simpleTransposition_apply_left]
      exact iff_of_true (hal.trans (pnat_lt_succ i)) hal
    · rw [simpleTransposition_apply_below i b (lt_of_le_of_ne hb hbi)]

/-- Swapping values above a support endpoint preserves records inside that endpoint. -/
theorem IsSupported.isRecord_simple_left {i : ℕ+} {w : FinitaryPerm ℕ+}
    (hw : IsSupported (i : ℕ) w) (j : ℕ+) (hj : j ≤ i) :
    IsRecord (simpleTransposition i * w) j ↔ IsRecord w j := by
  have hValues (k : ℕ+) (hk : k ≤ i) : w k ≤ i := (hw.apply_le_iff k).mpr hk
  constructor
  · intro hr k hk
    exact (simpleTransposition_lt_below i (w k) (w j)
      (hValues k (hk.le.trans hj)) (hValues j hj)).mp (hr k hk)
  · intro hr k hk
    exact (simpleTransposition_lt_below i (w k) (w j)
      (hValues k (hk.le.trans hj)) (hValues j hj)).mpr (hr k hk)

/-- Swapping positions at an endpoint leaves all earlier record tests unchanged. -/
theorem isRecord_simple_right_below (w : FinitaryPerm ℕ+) (i j : ℕ+) (hj : j < i) :
    IsRecord (w * simpleTransposition i) j ↔ IsRecord w j := by
  constructor
  · intro hr k hk
    simpa only [mul_apply, simpleTransposition_apply_below i k (hk.trans hj),
      simpleTransposition_apply_below i j hj] using hr k hk
  · intro hr k hk
    simpa only [mul_apply, simpleTransposition_apply_below i k (hk.trans hj),
      simpleTransposition_apply_below i j hj] using hr k hk

/-- A right swap puts the new maximum at the previous support endpoint. -/
theorem IsSupported.isRecord_simple_right {i : ℕ+} {w : FinitaryPerm ℕ+}
    (hw : IsSupported (i : ℕ) w) : IsRecord (w * simpleTransposition i) i := by
  intro k hk
  rw [mul_apply, mul_apply, simpleTransposition_apply_below i k hk,
    simpleTransposition_apply_left, hw (i + 1) (by change (i : ℕ) < (i : ℕ) + 1; omega)]
  have hVal : w k ≤ i := (hw.apply_le_iff k).mpr hk.le
  exact hVal.trans_lt (pnat_lt_succ i)

/-- The final position after a right endpoint swap is not a record. -/
theorem IsSupported.not_record_right_last {i : ℕ+} {w : FinitaryPerm ℕ+}
    (hw : IsSupported (i : ℕ) w) : ¬IsRecord (w * simpleTransposition i) (i + 1) := by
  intro hr
  have hc := hr i (pnat_lt_succ i)
  rw [mul_apply, mul_apply, simpleTransposition_apply_left,
    simpleTransposition_apply_right,
    hw (i + 1) (by change (i : ℕ) < (i : ℕ) + 1; omega)] at hc
  exact (not_lt_of_ge ((hw.apply_le_iff i).mpr le_rfl |>.trans (pnat_lt_succ i).le)) hc

/-- The final position after a left endpoint swap is not a record. -/
theorem IsSupported.not_record_left_last {i : ℕ+} {w : FinitaryPerm ℕ+}
    (hw : IsSupported (i : ℕ) w) : ¬IsRecord (simpleTransposition i * w) (i + 1) := by
  intro hr
  have hk : w⁻¹ i ≤ i := (hw.inv.apply_le_iff i).mpr le_rfl
  have hc := hr (w⁻¹ i) (hk.trans_lt (pnat_lt_succ i))
  rw [mul_apply, mul_apply, apply_inv_apply, simpleTransposition_apply_left,
    hw (i + 1) (by change (i : ℕ) < (i : ℕ) + 1; omega),
    simpleTransposition_apply_right] at hc
  exact (not_lt_of_ge (pnat_lt_succ i).le) hc

end FinitaryPerm
