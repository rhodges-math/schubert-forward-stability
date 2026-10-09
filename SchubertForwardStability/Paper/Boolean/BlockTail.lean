import SchubertForwardStability.Paper.Boolean.BlockDrift
import SchubertForwardStability.Paper.Boolean.BlockRows
import SchubertForwardStability.Paper.Boolean.LogTail
import SchubertForwardStability.Paper.Boolean.MaximumExcess

/-! # One-sided tails of backwards Boolean record-walk blocks

The concrete centered row and positive drift put every backwards endpoint event
inside the MPR lower-tail event. Its bounded positive part therefore has a
summable weighted logarithmic-exponential upper bound.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory StrongMixing
open scoped Classical BigOperators

/-- A preterminal backwards Boolean endpoint event has the fixed logarithmic-exponential tail. -/
theorem boolean_backtrack_tail (N a k : ℕ) (hk : 4 ≤ k) (ha : a + k ≤ N) :
    (pairLaw (boolean (N + 1))).real {p |
      (recordWalk p.1 p.2 (a + k).succPNat : ℝ) ≤ recordWalk p.1 p.2 a.succPNat} ≤
      Real.exp (-(positiveDriftTailRate (mprTailConstant (Real.log 6 / 12)) (1 / 27) * k /
        (Real.log k * Real.log (Real.log k)))) := by
  let S := (Finset.range k).image (fun t : ℕ => ((a + t : ℕ) : ℤ))
  have hCard : S.card = k := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ (by
      intro t s h
      change ((a + t : ℕ) : ℤ) = ((a + s : ℕ) : ℤ) at h
      have hNat : a + t = a + s := by exact_mod_cast h
      omega), Finset.card_range]
  have hInclusion : {p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ |
      (recordWalk p.1 p.2 (a + k).succPNat : ℝ) ≤ recordWalk p.1 p.2 a.succPNat} ⊆
      {p | (∑ i ∈ S, booleanCenteredRow N i p) ≤ -((1 / 27 : ℝ) * k)} := by
    intro p hp
    change (∑ i ∈ (Finset.range k).image (fun t : ℕ => ((a + t : ℕ) : ℤ)),
      booleanCenteredRow N i p) ≤ -((1 / 27 : ℝ) * k)
    rw [booleanCenteredRow_sum N a k ha p]
    exact boolean_backtrack_centered_le (N + 1) a k (by omega) (by omega) p hp
  have hMPR := booleanCenteredRow_lower_tail N S (by rwa [hCard])
    (x := (1 / 27 : ℝ) * k) (by positivity)
  rw [hCard] at hMPR
  have hDen : (k : ℝ) * 2 ^ 2 + 2 * ((1 / 27 : ℝ) * k) * Real.log k *
      Real.log (Real.log k) =
      4 * k + 2 * ((1 / 27 : ℝ) * k) * Real.log k * Real.log (Real.log k) := by ring
  rw [hDen] at hMPR
  have hRate : 0 < mprTailConstant (Real.log 6 / 12) :=
    mprTailConstant_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num))
  calc
    _ ≤ (pairLaw (boolean (N + 1))).real
        {p | (∑ i ∈ S, booleanCenteredRow N i p) ≤ -((1 / 27 : ℝ) * k)} :=
      measureReal_mono hInclusion (measure_ne_top _ _)
    _ ≤ _ := hMPR.trans (positive_drift_exponential_le
      (eta := (1 / 27 : ℝ)) hRate (by norm_num) k hk)

/-- The mean positive backwards displacement has its weighted logarithmic tail bound. -/
theorem integral_boolean_backtrack_le (N a k : ℕ) (hk : 4 ≤ k) (ha : a + k ≤ N) :
    (∫ p, max ((recordWalk p.1 p.2 a.succPNat : ℝ) -
        recordWalk p.1 p.2 (a + k).succPNat) 0 ∂pairLaw (boolean (N + 1))) ≤
      (k : ℝ) * Real.exp
        (-(positiveDriftTailRate (mprTailConstant (Real.log 6 / 12)) (1 / 27) * k /
          (Real.log k * Real.log (Real.log k)))) := by
  apply (integral_boolean_positive_excess_le (N + 1) a.succPNat (a + k).succPNat
    (K := (k : ℝ)) (Nat.cast_nonneg k) ?_).trans
    (mul_le_mul_of_nonneg_left (boolean_backtrack_tail N a k hk ha) (Nat.cast_nonneg k))
  intro p _
  have h := (abs_le.mp (abs_recordWalk_sub_le_real p.1 p.2 a k)).1
  linarith

end RecordStability
