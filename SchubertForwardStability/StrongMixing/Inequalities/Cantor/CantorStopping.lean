import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorDecay
import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorFixed
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Find

/-!
# Finite stopping levels for rounded Cantor sets

The retained set has a fixed terminal depth. The first level below a numerical
threshold gives a partial-depth proof of its log-Laplace bound, without changing
that set as the Laplace parameter varies.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

/-- The fixed Cantor depth is the base-two natural logarithm of `n/8`.
This is a total natural-valued definition, including `n = 0`. -/
def fixedCantorDepth (n : ℕ) : ℕ := Nat.log 2 (n / 8)

/-- For `n >= 8`, the multiplicity at the fixed Cantor depth is at most `n/8`.
The division in this statement is natural-number division. -/
theorem fixedCantorDepth_pow_le (n : ℕ) (hn : 8 ≤ n) :
    2 ^ fixedCantorDepth n ≤ n / 8 := by
  exact Nat.pow_log_le_self 2 (by omega)

/-- At every rounded Cantor level, the terminal multiplicity times the terminal
interval length is at most the original length. This statement requires no sign
or size restriction on the rounding parameter. -/
theorem cantor_length_pow_le (δ : ℝ) (n d : ℕ) :
    2 ^ d * cantorLength δ n d ≤ n := by
  have h := cantorBlock_card_le (cantorLength δ n) (cantorLength_fit δ n) 0 0 d
  rw [cantorBlock_card (cantorLength δ n) (cantorLength_fit δ n) 0 0 d] at h
  simpa only [Nat.zero_add, cantorLength] using h

/-- The rounded terminal interval at the fixed depth has length at most sixteen,
uniformly in the original length and the real rounding parameter. -/
theorem fixedCantorLength_le (δ : ℝ) (n : ℕ) :
    cantorLength δ n (fixedCantorDepth n) ≤ 16 := by
  by_cases hn : n < 8
  · have hd : fixedCantorDepth n = 0 := by
      simp only [fixedCantorDepth, Nat.div_eq_of_lt hn, Nat.log_zero_right]
    rw [hd, cantorLength]
    omega
  · have hp := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (n / 8)
    change n / 8 < 2 ^ (fixedCantorDepth n + 1) at hp
    rw [pow_succ] at hp
    have hn' : n < 16 * 2 ^ fixedCantorDepth n := by omega
    have h := (cantor_length_pow_le δ n (fixedCantorDepth n)).trans_lt hn'
    have hpow : 0 < 2 ^ fixedCantorDepth n := by positivity
    nlinarith

/-- The fixed-depth Cantor block retains at least half of the coordinates when
`n >= 8`, the deletion fraction lies in `[0,1]`, and the depth times that fraction
is at most `1/4`. The cardinality assertion is independent of translation. -/
theorem fixedCantorBlock_half {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (hn : 8 ≤ n) (a : ℤ)
    (hfrac : (fixedCantorDepth n : ℝ) * δ ≤ 1 / 4) :
    (n : ℝ) / 2 ≤ (cantorBlock (cantorLength δ n) 0 a (fixedCantorDepth n)).card := by
  apply cantorBlock_half hδ0 hδ1 n (fixedCantorDepth n) a hfrac
  have hp : 8 * 2 ^ fixedCantorDepth n ≤ n := by
    have h := fixedCantorDepth_pow_le n hn
    omega
  have hpR : 8 * (2 : ℝ) ^ fixedCantorDepth n ≤ n := by exact_mod_cast hp
  linarith

/-- If the last length is at most a threshold, there is a first level at or below
the threshold. All strictly earlier lengths are strictly greater than it. No
monotonicity assumption is needed, and the first level may be zero. -/
theorem exists_first_length_le (L : ℕ → ℕ) (N : ℕ) (B : ℝ)
    (hLast : (L N : ℝ) ≤ B) :
    ∃ d ≤ N, (L d : ℝ) ≤ B ∧ ∀ k < d, B < (L k : ℝ) := by
  classical
  let he : ∃ k, (L k : ℝ) ≤ B := ⟨N, hLast⟩
  refine ⟨Nat.find he, Nat.find_min' he hLast, Nat.find_spec he, ?_⟩
  intro k hk
  exact lt_of_not_ge (Nat.find_min he hk)

end StrongMixing
