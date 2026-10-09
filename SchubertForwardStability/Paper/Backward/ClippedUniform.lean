import SchubertForwardStability.Paper.Backward.Clipping
import SchubertForwardStability.Paper.Uniform.Expectation
import SchubertForwardStability.Paper.Uniform.ProductGaussian

/-! # Clipped product forward stability for uniform permutations

## Main results

* `integral_uniform_deficit_le`: for `n ≥ 1`, the mean deficit `max 0 (n - F)` is at
  most `1 / n`.
* `uniform_clipped_expectation`: `max n F` has the same expectation asymptotic as `F`,
  with the same additive constant.
* `uniform_clipped_gaussian`: `max n F` has the same Gaussian limit as `F`.

## Implementation notes

Here `F` is product forward stability of two independent uniform permutations of size `n`.
Since `F` dominates the larger individual forward stability, the deficit can be positive
only when both permutations fix `n`, an event of probability `1 / n ^ 2`.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The deficit is at most the size times the indicator that both permutations fix
their last position. -/
theorem deficit_le_last_upward {n : ℕ} (hn : 1 ≤ n) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported n u) (hv : IsSupported n v) :
    max 0 ((n : ℝ) - productForwardStability u v) ≤
      (n : ℝ) * (upwardIndicator u v (n.toPNat hn) : ℝ) := by
  have huf := (u.forwardStability_le_iff hn).mpr hu
  have hvf := (v.forwardStability_le_iff hn).mpr hv
  have hm := max_forwardStability_le_product u v
  by_cases hN : max u.forwardStability v.forwardStability = n
  · have hF : (n : ℝ) ≤ (productForwardStability u v : ℝ) := by exact_mod_cast hN ▸ hm
    rw [max_eq_left (by linarith)]
    exact mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast upwardIndicator_nonneg _ _ _)
  · have hlt : max u.forwardStability v.forwardStability < n := by omega
    have hur : IsRecord u (n.toPNat hn) := u.isRecord_above (by change _ < n; omega)
    have hvr : IsRecord v (n.toPNat hn) := v.isRecord_above (by change _ < n; omega)
    rw [upwardIndicator_eq_records, ite_eq_left ⟨hur, hvr⟩, Int.cast_one, mul_one]
    apply max_le (Nat.cast_nonneg _)
    have hF : (0 : ℝ) ≤ (productForwardStability u v : ℝ) := Nat.cast_nonneg _
    linarith

/-- For positive size, the uniform mean deficit is at most the reciprocal size. -/
theorem integral_uniform_deficit_le {n : ℕ} (hn : 1 ≤ n) :
    (∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2)
      ∂pairLaw (symmetricGroup n)) ≤ 1 / n := by
  calc
    _ ≤ ∫ p, (n : ℝ) * (upwardIndicator p.1 p.2 (n.toPNat hn) : ℝ)
        ∂pairLaw (symmetricGroup n) := by
      apply integral_uniform_finset_mono
      intro p hp
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
      exact deficit_le_last_upward hn p.1 p.2
        ((mem_symmetricGroup _ _).mp hu) ((mem_symmetricGroup _ _).mp hv)
    _ = 1 / n := by
      rw [integral_const_mul, integral_uniform_upward n (n.toPNat hn) (by rfl)]
      have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      change (n : ℝ) * (1 / (n : ℝ) ^ 2) = 1 / (n : ℝ)
      field_simp

/-- The uniform mean deficit tends to zero. -/
theorem tendsto_integral_uniform_deficit :
    Tendsto (fun n : ℕ => ∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2)
      ∂pairLaw (symmetricGroup n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => integral_deficit_nonneg n _) ?_
    tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact integral_uniform_deficit_le hn

/-- Every additive constant in the uniform forward expectation asymptotic is also an
additive constant for the clipped statistic. -/
theorem uniform_clipped_expectation_of {c : ℝ}
    (h : Tendsto (fun n : ℕ =>
      (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (symmetricGroup n)) -
        (2 * n - 2 * Real.log n - 2 * Real.eulerMascheroniConstant + c)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∫ p, max (n : ℝ) (productForwardStability p.1 p.2 : ℝ)
        ∂pairLaw (symmetricGroup n)) -
        (2 * n - 2 * Real.log n - 2 * Real.eulerMascheroniConstant + c)) atTop (𝓝 0) :=
  tendsto_clipped_integral h tendsto_integral_uniform_deficit

/-- One constant between one and the Basel sum gives the expectation asymptotic of both
uniform forward stability and its clipping at the ambient size. -/
theorem uniform_clipped_expectation :
    ∃ c ∈ Set.Icc (1 : ℝ) (Real.pi ^ 2 / 6),
      Tendsto (fun n : ℕ =>
        (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (symmetricGroup n)) -
          (2 * n - 2 * Real.log n - 2 * Real.eulerMascheroniConstant + c)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        (∫ p, max (n : ℝ) (productForwardStability p.1 p.2 : ℝ)
          ∂pairLaw (symmetricGroup n)) -
          (2 * n - 2 * Real.log n - 2 * Real.eulerMascheroniConstant + c)) atTop (𝓝 0) := by
  obtain ⟨c, hc, h⟩ := uniform_product_expectation
  exact ⟨c, hc, h, uniform_clipped_expectation_of h⟩

/-- Uniform forward stability clipped at the ambient size, with logarithmic centering,
tends to the standard Gaussian. -/
theorem uniform_clipped_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        (max (n : ℝ) (productForwardStability p.1 p.2 : ℝ) - (2 * n - 2 * Real.log n)) /
          Real.sqrt (2 * Real.log n))
      atTop id (fun n => pairLaw (symmetricGroup n)) (gaussianReal 0 1) := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt (2 * Real.log n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Tendsto.const_mul_atTop (by norm_num)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  exact tendstoInDistribution_clipped (a := fun n => 2 * n - 2 * Real.log n)
    (b := fun n => Real.sqrt (2 * Real.log n)) (fun _ => Real.sqrt_nonneg _)
    uniform_product_gaussian (tendsto_integral_uniform_deficit.div_atTop hs)

end RecordStability
