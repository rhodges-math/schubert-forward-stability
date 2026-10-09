import SchubertForwardStability.Permutations.Finitary.ShiftBounds
import SchubertForwardStability.Permutations.Classes.CycleWord
import SchubertForwardStability.Permutations.Classes.PatternFamilies
import Mathlib.Tactic

/-! # Joining two initial permutations around a new maximum

The left values retain their alphabet, the right values shift by the left size,
and the new largest value occupies the position between the two blocks.
-/

namespace PermutationPattern

open FinitaryPerm

/-- Join left and shifted right permutations with a new maximum between them. -/
noncomputable def joinLow (a b : ℕ) (u v : FinitaryPerm ℕ+) : FinitaryPerm ℕ+ :=
  u * shiftPermHom a v * shiftPermHom a (wordProduct (initialDescendingWord b))

/-- Joining bounded blocks is supported in their total size plus one. -/
theorem joinLow_supported (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) :
    IsSupported (a + b + 1) (joinLow a b u v) := by
  have hc : IsSupported (b + 1) (wordProduct (initialDescendingWord b)) :=
    fun j hj => initialDescendingWord_apply_above b j hj
  exact ((hu.mono (by omega)).mul
    ((shiftPermHom_supported a b v hv).mono (by omega))).mul
    ((shiftPermHom_supported a (b + 1) _ hc).mono (by omega))

/-- The joined permutation acts as its left factor on the initial block. -/
theorem joinLow_apply_left (a b : ℕ) (u v : FinitaryPerm ℕ+) (i : ℕ+)
    (hi : (i : ℕ) ≤ a) : joinLow a b u v i = u i := by
  rw [joinLow, mul_apply, mul_apply, shiftPermHom_fixed a _ i hi,
    shiftPermHom_fixed a v i hi]

/-- The new maximum of the joined permutation is at the block boundary. -/
theorem joinLow_apply_max (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) :
    joinLow a b u v a.succPNat = (a + b).succPNat := by
  have hIndex : a.succPNat = shiftPosition a 1 := by
    apply PNat.eq
    rfl
  rw [hIndex, joinLow, mul_apply, mul_apply, shiftPermHom_apply,
    initialDescendingWord_apply_one, shiftPermHom_apply,
    hv b.succPNat (by change b < b + 1; omega),
    hu _ (by change a < a + (b + 1); omega)]
  apply PNat.eq
  change a + (b + 1) = a + b + 1
  omega

/-- Each right-block position carries its shifted right-factor value. -/
theorem joinLow_apply_right (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (t : ℕ+) (ht : (t : ℕ) ≤ b) :
    joinLow a b u v (shiftPosition (a + 1) t) = shiftPosition a (v t) := by
  have hIndex : shiftPosition (a + 1) t = shiftPosition a (t + 1) := by
    apply PNat.eq
    change (a + 1) + (t : ℕ) = a + ((t : ℕ) + 1)
    omega
  have hCycle : wordProduct (initialDescendingWord b) (t + 1) = t := by
    apply PNat.eq
    rw [initialDescendingWord_apply_inside b (t + 1)
      (by change 1 < (t : ℕ) + 1; have := t.pos; omega)
      (by change (t : ℕ) + 1 ≤ b + 1; omega)]
    change (t : ℕ) + 1 - 1 = (t : ℕ)
    omega
  rw [hIndex, joinLow, mul_apply, mul_apply, shiftPermHom_apply, hCycle,
    shiftPermHom_apply, hu _ (by change a < a + (v t : ℕ); have := (v t).pos; omega)]

end PermutationPattern
