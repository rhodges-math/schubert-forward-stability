import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorBlocks
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rounded finite Cantor length schedules

Each split deletes the ceiling of a prescribed fraction of the current length and
then retains two equally sized integer children. The integer-rounding losses are
explicit, including their accumulation over the binary tree and a half-retention
criterion for the resulting finite set of coordinates.
-/

namespace StrongMixing

/-- Length of either retained child after deleting the ceiling of `δ * n`
coordinates from a parent of integer length `n` and dividing the remainder by two. -/
noncomputable def cantorNext (δ : ℝ) (n : ℕ) : ℕ := (n - ⌈δ * n⌉₊) / 2

/-- The rounded Cantor length schedule starting at integer length `n`, with
constant deletion fraction `δ` at every split. -/
noncomputable def cantorLength (δ : ℝ) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | j + 1 => cantorNext δ (cantorLength δ n j)

/-- Two retained child lengths always fit in their parent, even for deletion
fractions outside the unit interval. Natural subtraction makes oversized deletions
produce zero child lengths. -/
theorem cantorNext_fit (δ : ℝ) (n : ℕ) : 2 * cantorNext δ n ≤ n := by
  dsimp [cantorNext]
  omega

/-- Every adjacent pair of levels in the rounded schedule satisfies the child-fit
condition required by the finite Cantor block construction. -/
theorem cantorLength_fit (δ : ℝ) (n : ℕ) (j : ℕ) :
    2 * cantorLength δ n (j + 1) ≤ cantorLength δ n j :=
  cantorNext_fit δ (cantorLength δ n j)

/-- For a deletion fraction between zero and one, a split loses at most `δ * n + 2`
coordinates: one possible ceiling error and one possible parity error. -/
theorem cantorNext_loss {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (n : ℕ) :
    (n : ℝ) - 2 * cantorNext δ n ≤ δ * n + 2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : ⌈δ * n⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hr : n ≤ 2 * cantorNext δ n + ⌈δ * n⌉₊ + 1 := by
    dsimp [cantorNext]
    omega
  have hr' : (n : ℝ) ≤ 2 * cantorNext δ n + (⌈δ * n⌉₊ : ℝ) + 1 := by
    exact_mod_cast hr
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hδ0 hn)
  linarith

/-- The number of coordinates deleted by a rounded split is at least the prescribed
real fraction `δ * n`, whenever `δ <= 1`. Negative fractions are allowed. -/
theorem cantorNext_gap {δ : ℝ} (hδ1 : δ ≤ 1) (n : ℕ) :
    δ * n ≤ ((n - 2 * cantorNext δ n : ℕ) : ℝ) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : ⌈δ * n⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hr : ⌈δ * n⌉₊ ≤ n - 2 * cantorNext δ n := by
    dsimp [cantorNext]
    omega
  exact (Nat.le_ceil (δ * n)).trans (by exact_mod_cast hr)

/-- After `d` rounded binary splits, at least
`(1 - d * δ) * n - 2 * (2 ^ d - 1)` coordinates remain. The rounding loss is
explicit and the assertion includes zero lengths and arbitrarily deep splits. -/
theorem cantorLength_retained {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (n d : ℕ) :
    (1 - (d : ℝ) * δ) * n - 2 * ((2 : ℝ) ^ d - 1) ≤
      (2 : ℝ) ^ d * cantorLength δ n d := by
  induction d with
  | zero => simp [cantorLength]
  | succ d ih =>
    have hloss := cantorNext_loss hδ0 hδ1 (cantorLength δ n d)
    have hstep : (1 - δ) * (cantorLength δ n d : ℝ) - 2 ≤
        2 * (cantorLength δ n (d + 1) : ℝ) := by
      simpa only [cantorLength] using (by linarith :
        (1 - δ) * (cantorLength δ n d : ℝ) - 2 ≤
          2 * (cantorNext δ (cantorLength δ n d) : ℝ))
    have hp : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hscale := mul_le_mul_of_nonneg_left hstep
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d)
    have hprev := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hδ1)
    have hbonus : 0 ≤ (d : ℝ) * δ ^ 2 * n + 2 * δ * ((2 : ℝ) ^ d - 1) := by
      exact add_nonneg (by positivity) (mul_nonneg (mul_nonneg (by norm_num) hδ0)
        (sub_nonneg.mpr hp))
    push_cast
    rw [pow_succ]
    nlinarith

/-- If `d * δ <= 1/4` and `2 ^ d <= n/8`, the rounded retained Cantor block has
at least half of the original `n` coordinates. The criterion is independent of
translation. -/
theorem cantorBlock_half {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (n d : ℕ) (a : ℤ)
    (hfrac : (d : ℝ) * δ ≤ 1 / 4) (hround : (2 : ℝ) ^ d ≤ (n : ℝ) / 8) :
    (n : ℝ) / 2 ≤ (cantorBlock (cantorLength δ n) 0 a d).card := by
  have hr := cantorLength_retained hδ0 hδ1 n d
  have hfracn := mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  rw [cantorBlock_card _ (cantorLength_fit δ n)]
  simp only [Nat.zero_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

end StrongMixing
