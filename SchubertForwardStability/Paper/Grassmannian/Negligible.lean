import SchubertForwardStability.Paper.Grassmannian.Expectation
import SchubertForwardStability.LimitTheorems.Convergence.FirstMoment

/-! # Negligible maximum and residual terms in Grassmannian stability

Under the subset model, `(FS(u,v) - 3n/2)/sqrt(n)` differs from
`-(max(|V|, |W|) - n/2)/sqrt(n)` by a term whose first moment tends to zero, so the
difference tends to zero in probability.
-/

open MeasureTheory ProbabilityTheory Filter Asymptotics FinitaryPerm SchubertPolynomial
open scoped Topology

namespace RecordStability

private theorem integrable_subset_pair (n : ℕ) (f : Finset ℕ+ × Finset ℕ+ → ℝ) :
    Integrable f ((subsetLaw n).prod (subsetLaw n)) := by
  rw [subsetLaw, ← uniformOn_finset_prod]
  exact integrable_uniform_finset _ f

/-- The mean absolute deficit of the selected maximum is `1-2^(-n)`. -/
theorem integral_subset_max_gap (n : ℕ) :
    (∫ V, |(n : ℝ) - ((V.sup PNat.val : ℕ) : ℝ)| ∂subsetLaw n) =
      1 - ((2 : ℝ) ^ n)⁻¹ := by
  calc
    _ = ∫ V, (n : ℝ) - ((V.sup PNat.val : ℕ) : ℝ) ∂subsetLaw n := by
      apply integral_uniform_finset_congr
      intro V hV
      apply abs_of_nonneg
      have hb := subset_maximum_le n V (Finset.mem_powerset.mp hV)
      exact sub_nonneg.mpr (by exact_mod_cast hb)
    _ = _ := by
      rw [integral_sub (integrable_subsetLaw n _) (integrable_subsetLaw n _),
        integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul,
        subsetLaw_maximum_mean]
      ring

private theorem integral_pair_gap_fst (n : ℕ) :
    (∫ p, |(n : ℝ) - ((p.1.sup PNat.val : ℕ) : ℝ)|
      ∂(subsetLaw n).prod (subsetLaw n)) = 1 - ((2 : ℝ) ^ n)⁻¹ := by
  rw [integral_prod _ (integrable_subset_pair n _)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  exact integral_subset_max_gap n

private theorem integral_pair_gap_snd (n : ℕ) :
    (∫ p, |(n : ℝ) - ((p.2.sup PNat.val : ℕ) : ℝ)|
      ∂(subsetLaw n).prod (subsetLaw n)) = 1 - ((2 : ℝ) ^ n)⁻¹ := by
  rw [integral_prod _ (integrable_subset_pair n _)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  exact integral_subset_max_gap n

/-- The difference from the centered size maximum has a vanishing first-moment bound. -/
theorem integral_subset_scaled_error_le (n : ℕ) :
    (∫ p, ‖((productForwardStability (subsetPermutation n p.1)
      (subsetPermutation n p.2) : ℝ) - (3 : ℝ) / 2 * n) / Real.sqrt n +
        ((max p.1.card p.2.card : ℝ) - (n : ℝ) / 2) / Real.sqrt n‖
          ∂(subsetLaw n).prod (subsetLaw n)) ≤
      (2 + ∫ p, |(grassmannianResidual n p.1 p.2 : ℝ)|
        ∂(subsetLaw n).prod (subsetLaw n)) / Real.sqrt n := by
  have h (p : Finset ℕ+ × Finset ℕ+) :
      ((productForwardStability (subsetPermutation n p.1)
        (subsetPermutation n p.2) : ℝ) - (3 : ℝ) / 2 * n) / Real.sqrt n +
          ((max p.1.card p.2.card : ℝ) - (n : ℝ) / 2) / Real.sqrt n =
        (-(n - ((p.1.sup PNat.val : ℕ) : ℝ)) -
          (n - ((p.2.sup PNat.val : ℕ) : ℝ)) +
            (grassmannianResidual n p.1 p.2 : ℝ)) / Real.sqrt n := by
    dsimp only [grassmannianResidual]
    push_cast
    ring
  calc
    _ ≤ ∫ p, (|(n : ℝ) - ((p.1.sup PNat.val : ℕ) : ℝ)| +
        |(n : ℝ) - ((p.2.sup PNat.val : ℕ) : ℝ)| +
          |(grassmannianResidual n p.1 p.2 : ℝ)|) / Real.sqrt n
            ∂(subsetLaw n).prod (subsetLaw n) := by
      apply integral_mono (integrable_subset_pair n _) (integrable_subset_pair n _)
      intro p
      dsimp only
      rw [h p, Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have ha := abs_add_le (-(n - ((p.1.sup PNat.val : ℕ) : ℝ)) -
        (n - ((p.2.sup PNat.val : ℕ) : ℝ))) (grassmannianResidual n p.1 p.2 : ℝ)
      have hb := abs_sub (-(n - ((p.1.sup PNat.val : ℕ) : ℝ)))
        (n - ((p.2.sup PNat.val : ℕ) : ℝ))
      simp only [abs_neg] at ha hb
      linarith
    _ = (2 * (1 - ((2 : ℝ) ^ n)⁻¹) + ∫ p,
        |(grassmannianResidual n p.1 p.2 : ℝ)|
          ∂(subsetLaw n).prod (subsetLaw n)) / Real.sqrt n := by
      rw [integral_div, integral_add (integrable_subset_pair n _)
        (integrable_subset_pair n _), integral_add (integrable_subset_pair n _)
        (integrable_subset_pair n _), integral_pair_gap_fst, integral_pair_gap_snd]
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have hp : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
      linarith

/-- The normalized maximum and residual correction vanishes in probability. -/
theorem grassmannian_scaled_error_zero :
    LimitTheorems.TendstoInProbability
      (fun (n : ℕ) (p : Finset ℕ+ × Finset ℕ+) =>
        ((productForwardStability (subsetPermutation n p.1)
          (subsetPermutation n p.2) : ℝ) - (3 : ℝ) / 2 * n) / Real.sqrt n +
            ((max p.1.card p.2.card : ℝ) - (n : ℝ) / 2) / Real.sqrt n)
      atTop (0 : ℝ) (fun n => (subsetLaw n).prod (subsetLaw n)) := by
  apply LimitTheorems.tendstoInProbability_of_integral_norm
  · intro n
    exact integrable_subset_pair n _
  · obtain ⟨_, _, _, d, hd, h⟩ := grassmannian_residual_bounds
    have he : Tendsto (fun n : ℕ => Real.exp (-d * n)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hd)
    have hr := h.trans_tendsto he
    have hnum := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).add hr
    have ht := hnum.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
      integral_subset_scaled_error_le
    simpa only [Function.comp_def] using ht

end RecordStability
