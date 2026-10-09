import SchubertForwardStability.Paper.Boolean.Drift
import SchubertForwardStability.Permutations.Classes.Boolean.BooleanRestrictions
import SchubertForwardStability.Permutations.Statistics.RecordSums
import Mathlib.Analysis.Asymptotics.Defs

/-! # Terminal maximum of the mean Boolean record walk

The last record fiber is the preceding Boolean family. Positive drift before
the final supported position and the terminal walk value locate the finite
mean maximum there and bound its deviation from the ambient size.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Lemma 5.29.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Classical

private theorem fib_odd_pos (k : ℤ) : (0 : ℝ) < (Int.fib (2 * k - 1) : ℝ) := by
  have h := Int.fib_two_mul_add_one_pos (n := k - 1)
  rw [show 2 * (k - 1) + 1 = 2 * k - 1 by ring] at h
  exact_mod_cast h

/-- At the terminal ambient position the Boolean mean record walk equals ambient size. -/
theorem booleanMeanWalk_terminal (n : ℕ) : booleanMeanWalk n n.succPNat = n := by
  unfold booleanMeanWalk
  calc
    _ = ∫ _p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+, (n : ℝ) ∂pairLaw (boolean n) := by
      apply integral_uniform_finset_congr
      intro p hp
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
      rw [recordWalk, ((mem_boolean n p.1).mp hu).1.nonRecordsFrom_eq_zero
        n.succPNat (by change n < n + 1; omega),
        ((mem_boolean n p.2).mp hv).1.nonRecordsFrom_eq_zero
          n.succPNat (by change n < n + 1; omega)]
      simp only [Nat.cast_zero, zero_add, Int.cast_sub, Int.cast_natCast, Int.cast_one]
      change ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ)
      push_cast
      ring
    _ = _ := by simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- The mean walk at its last supported position has the adjacent-family Fibonacci expression. -/
theorem booleanMeanWalk_last (r : ℕ+) : booleanMeanWalk (r : ℕ) r =
    (r : ℝ) + 1 - 2 * (Int.fib (2 * (r : ℤ) - 3) : ℝ) /
      (Int.fib (2 * (r : ℤ) - 1) : ℝ) := by
  have h := booleanMeanWalk_step (r : ℕ) r
  have hNext : r + 1 = (r : ℕ).succPNat := by apply PNat.eq; rfl
  rw [hNext, booleanMeanWalk_terminal, integral_boolean_step] at h
  have hCount : (booleanRecordCount (r : ℕ) r : ℝ) =
      (Int.fib (2 * (r : ℤ) - 3) : ℝ) := by
    exact_mod_cast booleanRecordCount_last_fib r
  rw [hCount] at h
  linear_combination -h

/-- From size two, the last supported Boolean mean walk lies between size and size plus one. -/
theorem booleanMeanWalk_last_bound (r : ℕ+) (hr : 2 ≤ (r : ℕ)) :
    (r : ℝ) ≤ booleanMeanWalk (r : ℕ) r ∧
      booleanMeanWalk (r : ℕ) r ≤ (r : ℝ) + 1 := by
  have hGrowth := Int.fib_odd_stride_le (r : ℕ) 1 (by omega)
  simp only [pow_one] at hGrowth
  rw [show 2 * ((r : ℤ) - (1 : ℕ)) - 1 = 2 * (r : ℤ) - 3 by push_cast; ring] at hGrowth
  have hCast : 2 * (Int.fib (2 * (r : ℤ) - 3) : ℝ) ≤
      (Int.fib (2 * (r : ℤ) - 1) : ℝ) := by exact_mod_cast hGrowth
  have hDen := fib_odd_pos (r : ℤ)
  have hNum : (0 : ℝ) ≤ (Int.fib (2 * (r : ℤ) - 3) : ℝ) := by
    have h := fib_odd_pos ((r : ℤ) - 1)
    rw [show 2 * ((r : ℤ) - 1) - 1 = 2 * (r : ℤ) - 3 by ring] at h
    exact h.le
  have hUpper : (Int.fib (2 * (r : ℤ) - 3) : ℝ) /
      (Int.fib (2 * (r : ℤ) - 1) : ℝ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hDen).mpr
    linarith
  have hLower := div_nonneg hNum hDen.le
  rw [booleanMeanWalk_last]
  constructor
  · linear_combination 2 * hUpper
  · linear_combination 2 * hLower

private theorem mean_mono_nat (n k l : ℕ) (hn : 3 ≤ n) (hkl : k ≤ l)
    (hl : l + 1 ≤ n) : booleanMeanWalk n k.succPNat ≤ booleanMeanWalk n l.succPNat := by
  revert hl
  induction hkl with
  | refl => intro _; exact le_refl _
  | @step l hkl ih =>
    intro hl
    have hOld := ih (by omega)
    have hDrift := boolean_uniform_drift n hn l.succPNat (by change l + 1 ≤ n - 1; omega)
    have hStep := booleanMeanWalk_step n l.succPNat
    have hNext : l.succPNat + 1 = (l + 1).succPNat := by apply PNat.eq; rfl
    rw [hNext] at hStep
    linarith

/-- Before the final supported position every Boolean mean walk is bounded by its last mean. -/
theorem booleanMeanWalk_le_last (n : ℕ) (hn : 3 ≤ n) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    booleanMeanWalk n i ≤ booleanMeanWalk n ⟨n, by omega⟩ := by
  have hp := i.pos
  have h := mean_mono_nat n ((i : ℕ) - 1) (n - 1) hn (by omega) (by omega)
  have hI : ((i : ℕ) - 1).succPNat = i := by apply PNat.eq; change (i : ℕ) - 1 + 1 = _; omega
  have hN : (n - 1).succPNat = (⟨n, by omega⟩ : ℕ+) := by
    apply PNat.eq
    change n - 1 + 1 = n
    omega
  simpa only [hI, hN] using h

/-- The maximum of the Boolean walk means occurs at the last supported position from size three. -/
theorem booleanMeanMax_eq_last (n : ℕ) (hn : 3 ≤ n) :
    booleanMeanMax n = booleanMeanWalk n ⟨n, by omega⟩ := by
  apply le_antisymm
  · unfold booleanMeanMax
    apply (Finset.sup'_le_iff _ _).mpr
    intro i hi
    have hBound := (mem_positions (n + 1) i).mp hi
    by_cases hBefore : (i : ℕ) ≤ n
    · exact booleanMeanWalk_le_last n hn i hBefore
    · have hI : i = n.succPNat := by apply PNat.eq; change (i : ℕ) = n + 1; omega
      rw [hI, booleanMeanWalk_terminal]
      exact (booleanMeanWalk_last_bound ⟨n, by omega⟩ (by change 2 ≤ n; omega)).1
  · unfold booleanMeanMax
    exact Finset.le_sup' (booleanMeanWalk n)
      ((mem_positions (n + 1) ⟨n, by omega⟩).mpr (by change n ≤ n + 1; omega))

/-- The Boolean maximum mean differs from ambient size by a uniformly bounded eventual term. -/
theorem booleanMeanMax_sub_bigO :
    IsBigO atTop (fun n : ℕ => booleanMeanMax n - (n : ℝ)) (fun _ => (1 : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [booleanMeanMax_eq_last n hn]
  have h := booleanMeanWalk_last_bound ⟨n, by omega⟩ (by change 2 ≤ n; omega)
  change (n : ℝ) ≤ booleanMeanWalk n _ ∧ booleanMeanWalk n _ ≤ (n : ℝ) + 1 at h
  rw [Real.norm_eq_abs, abs_of_nonneg (by change 0 ≤ booleanMeanWalk n _ - (n : ℝ); linarith)]
  norm_num
  linarith

end RecordStability
