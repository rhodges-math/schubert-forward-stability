import SchubertForwardStability.StrongMixing.Inequalities.PeelingDepth
import SchubertForwardStability.LimitTheorems.Asymptotics.LogDecay

/-! # Positive-drift logarithmic tail comparison

A fixed lower bound for the log-log product absorbs the constant part of the
Bernstein denominator. The weighted resulting tail is summable.
-/

namespace RecordStability

open StrongMixing

/-- The fixed decay rate obtained from a positive drift and a Bernstein coefficient. -/
noncomputable def positiveDriftTailRate (C eta : ℝ) : ℝ :=
  C * eta ^ 2 / (4 / (Real.log 4 * Real.log (Real.log 4)) + 2 * eta)

/-- Positive drift and a positive Bernstein coefficient give a strictly positive decay rate. -/
theorem positiveDriftTailRate_pos {C eta : ℝ} (hC : 0 < C) (hEta : 0 < eta) :
    0 < positiveDriftTailRate C eta := by
  have hp := peeling_logs_pos 4 (by omega)
  norm_num only [Nat.cast_ofNat] at hp
  have hLog : 0 < Real.log (4 : ℝ) := by linarith [hp.1]
  have hLogLog : 0 < Real.log (Real.log (4 : ℝ)) := hp.2
  unfold positiveDriftTailRate
  positivity

/-- The positive-drift Bernstein exponential is bounded by a fixed logarithmic decay. -/
theorem positive_drift_exponential_le {C eta : ℝ} (hC : 0 < C) (hEta : 0 < eta)
    (k : ℕ) (hk : 4 ≤ k) :
    Real.exp (-C * (eta * k) ^ 2 /
      (4 * k + 2 * (eta * k) * Real.log k * Real.log (Real.log k))) ≤
    Real.exp (-(positiveDriftTailRate C eta * k /
      (Real.log k * Real.log (Real.log k)))) := by
  let d := Real.log (4 : ℝ) * Real.log (Real.log (4 : ℝ))
  let L := Real.log (k : ℝ) * Real.log (Real.log (k : ℝ))
  let A := 4 / d + 2 * eta
  have hp4 := peeling_logs_pos 4 (by omega)
  norm_num only [Nat.cast_ofNat] at hp4
  have hpk := peeling_logs_pos k hk
  have h4 : 0 < Real.log (4 : ℝ) := by linarith [hp4.1]
  have hkLog : 0 < Real.log (k : ℝ) := by linarith [hpk.1]
  have hd : 0 < d := mul_pos h4 hp4.2
  have hL : 0 < L := mul_pos hkLog hpk.2
  have hA : 0 < A := by dsimp [A]; positivity
  have hCast : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLogLe : Real.log (4 : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  have hLogLogLe : Real.log (Real.log (4 : ℝ)) ≤ Real.log (Real.log (k : ℝ)) :=
    Real.log_le_log h4 hLogLe
  have hdL : d ≤ L := mul_le_mul hLogLe hLogLogLe hp4.2.le hkLog.le
  have hFour : (4 : ℝ) ≤ (4 / d) * L := by
    have h := mul_le_mul_of_nonneg_left hdL
      (show 0 ≤ (4 : ℝ) / d from div_nonneg (by norm_num) hd.le)
    rwa [div_mul_cancel₀ _ hd.ne'] at h
  have hDen : 4 * (k : ℝ) + 2 * (eta * k) * L ≤ A * k * L := by
    have h := mul_le_mul_of_nonneg_right hFour hCast.le
    dsimp [A]
    nlinarith only [h]
  have hSmall : 0 < 4 * (k : ℝ) + 2 * (eta * k) * L := by positivity
  have hFraction := div_le_div_of_nonneg_left
    (show 0 ≤ C * (eta * (k : ℝ)) ^ 2 by positivity) hSmall hDen
  apply Real.exp_le_exp.mpr
  have hDenRewrite : 4 * (k : ℝ) + 2 * (eta * k) * Real.log k * Real.log (Real.log k) =
      4 * (k : ℝ) + 2 * (eta * k) * L := by dsimp [L]; ring
  rw [hDenRewrite]
  change -C * (eta * (k : ℝ)) ^ 2 / (4 * k + 2 * (eta * k) * L) ≤ _
  calc
    _ ≤ -(C * (eta * (k : ℝ)) ^ 2 / (A * k * L)) := by
      simpa only [neg_mul, neg_div] using neg_le_neg hFraction
    _ = _ := by
      change -(C * (eta * (k : ℝ)) ^ 2 / (A * k * L)) = -((C * eta ^ 2 / A) * k / L)
      field_simp [hA.ne', hCast.ne', hL.ne']

/-- The weighted positive-drift logarithmic decay has a finite sum. -/
theorem summable_positiveDriftTail {C eta : ℝ} (hC : 0 < C) (hEta : 0 < eta) :
    Summable (fun k : ℕ => (k : ℝ) * Real.exp
      (-(positiveDriftTailRate C eta * k / (Real.log k * Real.log (Real.log k))))) :=
  LimitTheorems.summable_nat_logDecay (positiveDriftTailRate_pos hC hEta)

end RecordStability
