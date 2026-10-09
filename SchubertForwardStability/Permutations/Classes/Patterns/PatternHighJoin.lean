import SchubertForwardStability.Permutations.Classes.Patterns.PatternJoin
import SchubertForwardStability.Permutations.Classes.Patterns.PatternReversal

/-! # A higher-left maximum join

`joinHigh a b u v` places `u`, with its values raised above those of `v`, on the first `a`
positions, the new maximum `a+b+1` at position `a+1`, and `v` on the last `b` positions.
This file gives its support and its values.
-/

namespace PermutationPattern

open FinitaryPerm

/-- Join higher left values and lower right values around a new maximum. -/
noncomputable def joinHigh (a b : ℕ) (u v : FinitaryPerm ℕ+) : FinitaryPerm ℕ+ :=
  joinLow b a (v * longestElement b) (u * longestElement a) * longestElement (a + b + 1)

/-- A higher-left join stays in its combined initial interval. -/
theorem joinHigh_supported (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) :
    IsSupported (a + b + 1) (joinHigh a b u v) := by
  have h := joinLow_supported b a (v * longestElement b) (u * longestElement a)
    (hv.mul (isSupported_longestElement b)) (hu.mul (isSupported_longestElement a))
  have hSize : b + a + 1 = a + b + 1 := by omega
  rw [hSize] at h
  exact h.mul (isSupported_longestElement (a + b + 1))

/-- A higher-left join shifts each left value above the right value interval. -/
theorem joinHigh_apply_left (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hv : IsSupported b v) (i : ℕ+) (hi : (i : ℕ) ≤ a) :
    joinHigh a b u v i = shiftPosition b (u i) := by
  let t := longestElement a i
  have ht : (t : ℕ) ≤ a := ((isSupported_longestElement a).apply_le_iff i).mpr hi
  have hIndex : longestElement (a + b + 1) i = shiftPosition (b + 1) t := by
    apply PNat.eq
    rw [longestElement_apply_val _ _ (by omega)]
    change a + b + 1 + 1 - (i : ℕ) = b + 1 + (longestElement a i : ℕ)
    rw [longestElement_apply_val a i hi]
    have := i.pos
    omega
  rw [joinHigh, mul_apply, hIndex,
    joinLow_apply_right b a (v * longestElement b) (u * longestElement a)
      (hv.mul (isSupported_longestElement b)) t ht]
  simp only [mul_apply, t, longestElement_apply_twice]

/-- The join's central position carries the new maximum value. -/
theorem joinHigh_apply_max (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) :
    joinHigh a b u v a.succPNat = (a + b).succPNat := by
  have hIndex : longestElement (a + b + 1) a.succPNat = b.succPNat := by
    apply PNat.eq
    rw [longestElement_apply_val _ _ (by change a + 1 ≤ a + b + 1; omega)]
    change a + b + 1 + 1 - (a + 1) = b + 1
    omega
  rw [joinHigh, mul_apply, hIndex,
    joinLow_apply_max b a (v * longestElement b) (u * longestElement a)
      (hv.mul (isSupported_longestElement b)) (hu.mul (isSupported_longestElement a))]
  apply PNat.eq
  change b + a + 1 = a + b + 1
  omega

/-- A higher-left join has the unchanged right factor values after its maximum. -/
theorem joinHigh_apply_right (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (t : ℕ+) (ht : (t : ℕ) ≤ b) :
    joinHigh a b u v (shiftPosition (a + 1) t) = v t := by
  have hIndex : longestElement (a + b + 1) (shiftPosition (a + 1) t) =
      longestElement b t := by
    apply PNat.eq
    rw [longestElement_apply_val _ _ (by change a + 1 + (t : ℕ) ≤ a + b + 1; omega),
      longestElement_apply_val b t ht]
    change a + b + 1 + 1 - (a + 1 + (t : ℕ)) = b + 1 - (t : ℕ)
    omega
  have hBound := ((isSupported_longestElement b).apply_le_iff t).mpr ht
  rw [joinHigh, mul_apply, hIndex,
    joinLow_apply_left b a (v * longestElement b) (u * longestElement a) _ hBound]
  simp only [mul_apply, longestElement_apply_twice]

end PermutationPattern
