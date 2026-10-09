import SchubertForwardStability.StrongMixing.Inequalities.CoordinateCovariance
import SchubertForwardStability.StrongMixing.Inequalities.GeometricSums
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.SeparatedLaplace
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.BoundedLaplace

/-!
# Second moments of geometrically mixing interval sums

The covariance inequality and the finite geometric tail give a linear bound in
the interval length for the second moment of a centered, bounded sequence sum.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A centered prefix paired with its next coordinate is bounded by the finite
reverse geometric covariance tail. -/
private theorem interval_prefix_cross_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M r : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ω, |X i ω| ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ r ^ h)
    (hXX : ∀ i j, Integrable (fun ω => X i ω * X j ω) μ) (a : ℤ) (m : ℕ) :
    (∫ ω, (∑ k ∈ Finset.range m, X (a + k) ω) * X (a + m) ω ∂μ) ≤
      4 * M ^ 2 * (r / (1 - r)) := by
  have hid : (fun ω => (∑ k ∈ Finset.range m, X (a + k) ω) * X (a + m) ω) =
      (fun ω => ∑ k ∈ Finset.range m, X (a + k) ω * X (a + m) ω) := by
    funext ω
    exact Finset.sum_mul _ _ _
  rw [hid, integral_finsetSum (Finset.range m)
    (f := fun k ω => X (a + k) ω * X (a + m) ω)
    (fun k _ => hXX (a + k) (a + m))]
  calc
    _ ≤ ∑ k ∈ Finset.range m, 4 * M ^ 2 * r ^ (m - k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm := Finset.mem_range.mp hk
      have hlag : 1 ≤ m - k := by omega
      have hpos : a + (k : ℤ) + ((m - k : ℕ) : ℤ) = a + (m : ℤ) := by omega
      have hc := centered_coordinate_product_le μ X hX hcenter hM hbound
        (a + k) (m - k)
      rw [hpos] at hc
      exact (le_abs_self _).trans (hc.trans
        (mul_le_mul_of_nonneg_left (hmix (m - k) hlag) (by positivity)))
    _ = 4 * M ^ 2 * ∑ k ∈ Finset.range m, r ^ (m - k) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * M ^ 2 * (r / (1 - r)) :=
      mul_le_mul_of_nonneg_left (geometric_reverse_sum_le hr0 hr1 m) (by positivity)

/-- For centered real coordinates bounded by `M`, a mixing bound `alpha(h) <= r^h`
at positive lags, with `0 <= r < 1`, gives an interval second moment at most
`n * M^2 * (1 + 8 * r / (1 - r))`. Empty intervals and the zero bound are allowed.
No stationarity is required. -/
theorem interval_second_moment_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M r : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ω, |X i ω| ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ r ^ h) (a : ℤ) (n : ℕ) :
    (∫ ω, (∑ k ∈ Finset.range n, X (a + k) ω) ^ 2 ∂μ) ≤
      n * M ^ 2 * (1 + 8 * r / (1 - r)) := by
  let P (m : ℕ) (ω : Ω) := ∑ k ∈ Finset.range m, X (a + k) ω
  have hX2 (i : ℤ) : MemLp (X i) 2 μ :=
    MemLp.of_bound (hX i).aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun ω => by simpa using hbound i ω))
  have hP2 (m : ℕ) : MemLp (P m) 2 μ := by
    apply MemLp.of_bound
      (Finset.measurable_sum (Finset.range m) (fun k _ => hX (a + k))).aestronglyMeasurable
      (m * M)
    apply Filter.Eventually.of_forall
    intro ω
    simpa only [Real.norm_eq_abs, Finset.card_range] using
      abs_sum_le_card_mul (fun k : ℕ => X (a + k)) (Finset.range m)
        (fun k _ => hbound (a + k)) ω
  have hPsq (m : ℕ) : Integrable (fun ω => (P m ω) ^ 2) μ := by
    exact (memLp_two_iff_integrable_sq (hP2 m).aestronglyMeasurable).mp (hP2 m)
  have hXX (i j : ℤ) : Integrable (fun ω => X i ω * X j ω) μ :=
    (hX2 i).integrable_mul (hX2 j)
  have hdiag (i : ℤ) : (∫ ω, (X i ω) ^ 2 ∂μ) ≤ M ^ 2 := by
    have hi : Integrable (fun ω => (X i ω) ^ 2) μ := by
      simpa only [pow_two] using hXX i i
    have hm := integral_mono hi (integrable_const (M ^ 2)) (fun ω => ?_)
    · simpa using hm
    · have hb := abs_le.mp (hbound i ω)
      have hp := mul_nonneg (sub_nonneg.mpr hb.2) (by linarith : 0 ≤ M + X i ω)
      nlinarith
  have hcross (m : ℕ) :
      (∫ ω, P m ω * X (a + m) ω ∂μ) ≤ 4 * M ^ 2 * (r / (1 - r)) :=
    interval_prefix_cross_le μ X hX hcenter hM hbound hr0 hr1 hmix hXX a m
  change (∫ ω, (P n ω) ^ 2 ∂μ) ≤ _
  induction n with
  | zero => simp [P]
  | succ n ih =>
    have hprod : Integrable (fun ω => P n ω * X (a + n) ω) μ :=
      (hP2 n).integrable_mul (hX2 (a + n))
    have hlast : Integrable (fun ω => (X (a + n) ω) ^ 2) μ := by
      simpa only [pow_two] using hXX (a + n) (a + n)
    have hexp : (∫ ω, (P (n + 1) ω) ^ 2 ∂μ) =
        (∫ ω, (P n ω) ^ 2 ∂μ) + 2 * (∫ ω, P n ω * X (a + n) ω ∂μ) +
          (∫ ω, (X (a + n) ω) ^ 2 ∂μ) := by
      calc
        _ = ∫ ω, (P n ω) ^ 2 + 2 * (P n ω * X (a + n) ω) +
            (X (a + n) ω) ^ 2 ∂μ := by
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro ω
          simp only [P, Finset.sum_range_succ]
          ring
        _ = _ := by
          rw [integral_add
            (f := fun ω => (P n ω) ^ 2 + 2 * (P n ω * X (a + n) ω))
            (g := fun ω => (X (a + n) ω) ^ 2)
            ((hPsq n).add (hprod.const_mul 2)) hlast,
            integral_add (f := fun ω => (P n ω) ^ 2)
              (g := fun ω => 2 * (P n ω * X (a + n) ω))
              (hPsq n) (hprod.const_mul 2), integral_const_mul]
    rw [hexp]
    calc
      _ ≤ n * M ^ 2 * (1 + 8 * r / (1 - r)) +
          2 * (4 * M ^ 2 * (r / (1 - r))) + M ^ 2 :=
        add_le_add (add_le_add ih
          (mul_le_mul_of_nonneg_left (hcross n) (by norm_num))) (hdiag (a + n))
      _ = (n + 1 : ℕ) * M ^ 2 * (1 + 8 * r / (1 - r)) := by
        push_cast
        ring

end StrongMixing
