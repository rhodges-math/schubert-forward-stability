import SchubertForwardStability.Paper.Grassmannian.CardMean
import SchubertForwardStability.Paper.Grassmannian.ResidualMeans
import SchubertForwardStability.Paper.Grassmannian.Transfer
import SchubertForwardStability.Permutations.ForMathlib.UniformIntegrable
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Integral.Prod

/-! # Mean asymptotic under subset-encoded Grassmannian sampling

For independent uniform Grassmannian permutations `u, v` of size `n`, the mean of
`FS(u,v)` is `3n/2 - sqrt(n)/(2*sqrt(pi)) - 2 + o(1)`. Under the subset model the mean
splits into two support maxima, the maximum of two subset sizes and a residual with
vanishing mean; the asymptotic is then transferred to the uniform law.

## Main results

* `RecordStability.grassmannian_encoded_expectation`: the asymptotic under the subset model.
* `RecordStability.grassmannian_expectation`: the asymptotic for the uniform law.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Theorem 1.4 and Proposition 4.11.
-/

open Filter Asymptotics MeasureTheory ProbabilityTheory FinitaryPerm SchubertPolynomial
open scoped Topology

namespace RecordStability

private theorem integrable_subset_pair (n : ℕ) (f : Finset ℕ+ × Finset ℕ+ → ℝ) :
    Integrable f ((subsetLaw n).prod (subsetLaw n)) := by
  rw [subsetLaw, ← uniformOn_finset_prod]
  exact integrable_uniform_finset _ f

private theorem integral_subset_max_fst (n : ℕ) :
    (∫ p, ((p.1.sup PNat.val : ℕ) : ℝ) ∂(subsetLaw n).prod (subsetLaw n)) =
      (n : ℝ) - 1 + ((2 : ℝ) ^ n)⁻¹ := by
  rw [integral_prod _ (integrable_subset_pair n _)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  exact subsetLaw_maximum_mean n

private theorem integral_subset_max_snd (n : ℕ) :
    (∫ p, ((p.2.sup PNat.val : ℕ) : ℝ) ∂(subsetLaw n).prod (subsetLaw n)) =
      (n : ℝ) - 1 + ((2 : ℝ) ^ n)⁻¹ := by
  rw [integral_prod _ (integrable_subset_pair n _)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  exact subsetLaw_maximum_mean n

/-- The encoded product mean splits into two maxima, a size maximum and the residual mean. -/
theorem subset_product_mean_decomposition (n : ℕ) :
    (∫ p, (productForwardStability (subsetPermutation n p.1)
      (subsetPermutation n p.2) : ℝ) ∂(subsetLaw n).prod (subsetLaw n)) =
      2 * ((n : ℝ) - 1 + ((2 : ℝ) ^ n)⁻¹) -
        (∫ p, (max p.1.card p.2.card : ℝ) ∂(subsetLaw n).prod (subsetLaw n)) +
        (∫ p, (grassmannianResidual n p.1 p.2 : ℝ) ∂(subsetLaw n).prod (subsetLaw n)) := by
  have h (p : Finset ℕ+ × Finset ℕ+) :
      (productForwardStability (subsetPermutation n p.1) (subsetPermutation n p.2) : ℝ) =
        (((p.1.sup PNat.val : ℕ) : ℝ) + ((p.2.sup PNat.val : ℕ) : ℝ) -
          (max p.1.card p.2.card : ℝ)) + (grassmannianResidual n p.1 p.2 : ℝ) := by
    dsimp only [grassmannianResidual]
    push_cast
    ring
  simp_rw [h]
  rw [integral_add (integrable_subset_pair n _) (integrable_subset_pair n _),
    integral_sub (integrable_subset_pair n _) (integrable_subset_pair n _),
    integral_add (integrable_subset_pair n _) (integrable_subset_pair n _),
    integral_subset_max_fst, integral_subset_max_snd]
  ring

/-- The signed residual mean tends to zero under independent subset sampling. -/
theorem grassmannian_residual_mean_zero :
    Tendsto (fun n : ℕ =>
      ∫ p, (grassmannianResidual n p.1 p.2 : ℝ) ∂(subsetLaw n).prod (subsetLaw n))
        atTop (𝓝 0) := by
  obtain ⟨_, _, _, d, hd, h⟩ := grassmannian_residual_bounds
  have he : Tendsto (fun n : ℕ => Real.exp (-d * n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hd)
  have hr := h.trans_tendsto he
  apply squeeze_zero_norm (fun n => ?_) hr
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
    (fun p : Finset ℕ+ × Finset ℕ+ => (grassmannianResidual n p.1 p.2 : ℝ))

/-- Subset-encoded stability has the stated three-halves mean and square-root correction. -/
theorem grassmannian_encoded_expectation :
    Tendsto (fun n : ℕ =>
      (∫ p, (productForwardStability p.1 p.2 : ℝ)
        ∂(grassmannianLaw n).prod (grassmannianLaw n)) -
          ((3 : ℝ) / 2 * n - Real.sqrt n / (2 * Real.sqrt Real.pi) - 2)) atTop (𝓝 0) := by
  have hcard := grassmannian_card_maximum_mean.trans_tendsto
    ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop)
  have hpow : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have ht := ((hpow.const_mul 2).sub hcard).add grassmannian_residual_mean_zero
  convert ht using 1
  · funext n
    rw [grassmannianLaw, Measure.map_prod_map _ _
      (measurable_subsetPermutation n) (measurable_subsetPermutation n),
      integral_map (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable]
    change (∫ p, (productForwardStability (subsetPermutation n p.1)
      (subsetPermutation n p.2) : ℝ) ∂(subsetLaw n).prod (subsetLaw n)) - _ = _
    rw [subset_product_mean_decomposition]
    ring
  · norm_num

/-- Uniform Grassmannian stability has the same centered mean asymptotic. -/
theorem grassmannian_expectation :
    Tendsto (fun n : ℕ =>
      (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (grassmannian n)) -
        ((3 : ℝ) / 2 * n - Real.sqrt n / (2 * Real.sqrt Real.pi) - 2)) atTop (𝓝 0) := by
  have h := grassmannian_encoded_expectation.sub tendsto_grass_expectation_diff
  convert h using 1
  · funext n
    ring
  · norm_num

end RecordStability
