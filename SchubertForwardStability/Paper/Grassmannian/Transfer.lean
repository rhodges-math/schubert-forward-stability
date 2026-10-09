import SchubertForwardStability.LimitTheorems.TotalVariation.Comparison
import SchubertForwardStability.Paper.Grassmannian.TotalVariation
import SchubertForwardStability.Paper.Grassmannian.Bounds
import SchubertForwardStability.LimitTheorems.TotalVariation.Support
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Comparison of Grassmannian forward-stability laws

## Main results

The independent modified and uniform pair laws have exponentially small total
variation. The forward-stability observable has range at most twice positive
ambient size, giving a vanishing expectation difference. Its normalized laws
also have vanishing total variation.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Section 4.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial MeasureTheory ProbabilityTheory LimitTheorems Filter
open scoped Classical Topology

private noncomputable def finiteModel (n : ℕ) : Measure (grassmannian n) :=
  finiteRestriction (grassmannian n) (grassmannianLaw n)

private noncomputable def finiteUniform (n : ℕ) : Measure (grassmannian n) :=
  finiteRestriction (grassmannian n) (unif (grassmannian n))

private instance finiteModel_probability (n : ℕ) : IsProbabilityMeasure (finiteModel n) :=
  isProbabilityMeasure_finiteRestriction _ _ (ae_mem_grassmannianLaw n)

private instance finiteUniform_probability (n : ℕ) :
    IsProbabilityMeasure (finiteUniform n) :=
  isProbabilityMeasure_finiteRestriction _ _ (ae_mem_unif _ ⟨1, one_mem_grassmannian n⟩)

private def pairMap (n : ℕ) : (grassmannian n) × (grassmannian n) →
    FinitaryPerm ℕ+ × FinitaryPerm ℕ+ := Prod.map Subtype.val Subtype.val

private theorem pairMap_measurable (n : ℕ) : Measurable (pairMap n) :=
  measurable_subtype_coe.prodMap measurable_subtype_coe

private theorem pairMap_injective (n : ℕ) : Function.Injective (pairMap n) := by
  intro p q he
  exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))

private theorem finiteModel_pair (n : ℕ) :
    ((finiteModel n).prod (finiteModel n)).map (pairMap n) =
      (grassmannianLaw n).prod (grassmannianLaw n) := by
  rw [pairMap, ← Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe,
    finiteModel, map_finiteRestriction _ _ (ae_mem_grassmannianLaw n)]

private theorem finiteUniform_pair (n : ℕ) :
    ((finiteUniform n).prod (finiteUniform n)).map (pairMap n) =
      pairLaw (grassmannian n) := by
  rw [pairLaw_eq_prod, pairMap,
    ← Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe,
    finiteUniform, map_finiteRestriction _ _ (ae_mem_unif _ ⟨1, one_mem_grassmannian n⟩)]

private theorem finitePair_tv (n : ℕ) :
    totalVariation ((grassmannianLaw n).prod (grassmannianLaw n))
        (pairLaw (grassmannian n)) =
      totalVariation ((finiteModel n).prod (finiteModel n))
        ((finiteUniform n).prod (finiteUniform n)) := by
  have h := totalVariation_map_injective ((finiteModel n).prod (finiteModel n))
    ((finiteUniform n).prod (finiteUniform n)) (pairMap_measurable n) (pairMap_injective n)
  rwa [finiteModel_pair, finiteUniform_pair] at h

/-- Independent Grassmannian pair-law distance is at most twice the marginal distance. -/
theorem grass_pair_totalVariation_le (n : ℕ) :
    totalVariation ((grassmannianLaw n).prod (grassmannianLaw n))
      (pairLaw (grassmannian n)) ≤
        2 * totalVariation (grassmannianLaw n) (unif (grassmannian n)) := by
  rw [finitePair_tv]
  have h := totalVariation_prod_le (finiteModel n) (finiteUniform n)
    (finiteModel n) (finiteUniform n)
  simp only [finiteModel, finiteUniform, totalVariation_finiteRestriction _ _ _
    (ae_mem_grassmannianLaw n) (ae_mem_unif _ ⟨1, one_mem_grassmannian n⟩)] at h
  dsimp only [finiteModel, finiteUniform]
  linarith

/-- Independent Grassmannian pair-law distance is bounded by `2*n/2^n`. -/
theorem grass_pair_totalVariation_pow_le (n : ℕ) :
    totalVariation ((grassmannianLaw n).prod (grassmannianLaw n))
      (pairLaw (grassmannian n)) ≤ 2 * (n : ℝ) / (2 : ℝ) ^ n := by
  exact (grass_pair_totalVariation_le n).trans (by
    have h := mul_le_mul_of_nonneg_left (grassmannian_totalVariation_le n)
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [mul_div_assoc] using h)

/-- A positive-ambient Grassmannian product has forward stability at most twice its size. -/
theorem grassmannian_product_bound (n : ℕ) (hn : 1 ≤ n)
    (u v : FinitaryPerm ℕ+) (hu : u ∈ grassmannian n) (hv : v ∈ grassmannian n) :
    productForwardStability u v ≤ 2 * n := by
  by_cases he : u = 1
  · subst u
    rw [productForwardStability_one_left]
    have h := (v.forwardStability_le_iff hn).mpr ((mem_grassmannian n v).mp hv).1
    omega
  by_cases hf : v = 1
  · subst v
    rw [productForwardStability_one_right]
    have h := (u.forwardStability_le_iff hn).mpr ((mem_grassmannian n u).mp hu).1
    omega
  obtain ⟨V, hV, hU⟩ := exists_grassmannianOfSubset hu
  obtain ⟨W, hW, hT⟩ := exists_grassmannianOfSubset hv
  have h₁ : subsetPermutation n V = u := (subsetPermutation_eq n V hV).trans hU.symm
  have h₂ : subsetPermutation n W = v := (subsetPermutation_eq n W hW).trans hT.symm
  have hx := subset_productForwardStability_general n V W hV hW
    (h₁.symm ▸ he) (h₂.symm ▸ hf)
  rw [h₁, h₂] at hx
  rw [hx]
  have hMV := subset_maximum_le n V hV
  have hMW := subset_maximum_le n W hW
  omega

/-- The forward-stability expectation discrepancy is bounded by its range times pair distance. -/
theorem grass_expectation_diff_tv (n : ℕ) (hn : 1 ≤ n) :
    |(∫ p, (productForwardStability p.1 p.2 : ℝ)
      ∂(grassmannianLaw n).prod (grassmannianLaw n)) -
        ∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (grassmannian n)| ≤
      (2 * (n : ℝ)) * totalVariation
        ((grassmannianLaw n).prod (grassmannianLaw n)) (pairLaw (grassmannian n)) := by
  let f (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) : ℝ := productForwardStability p.1 p.2
  have hm : (∫ p, f p ∂(grassmannianLaw n).prod (grassmannianLaw n)) =
      ∫ p, f (pairMap n p) ∂(finiteModel n).prod (finiteModel n) := by
    rw [← finiteModel_pair n]
    exact integral_map (pairMap_measurable n).aemeasurable
      (measurable_of_countable f).aestronglyMeasurable
  have hu : (∫ p, f p ∂pairLaw (grassmannian n)) =
      ∫ p, f (pairMap n p) ∂(finiteUniform n).prod (finiteUniform n) := by
    rw [← finiteUniform_pair n]
    exact integral_map (pairMap_measurable n).aemeasurable
      (measurable_of_countable f).aestronglyMeasurable
  change |(∫ p, f p ∂_) - ∫ p, f p ∂_| ≤ _
  rw [hm, hu, finitePair_tv]
  apply abs_integral_sub_le_tv_range
  intro p
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have hb := grassmannian_product_bound n hn p.1 p.2 p.1.property p.2.property
  change (productForwardStability p.1 p.2 : ℝ) ≤ 2 * (n : ℝ)
  exact_mod_cast hb

/-- The forward-stability expectation discrepancy is bounded by `4*n^2/2^n`. -/
theorem grass_expectation_diff_bound (n : ℕ) (hn : 1 ≤ n) :
    |(∫ p, (productForwardStability p.1 p.2 : ℝ)
      ∂(grassmannianLaw n).prod (grassmannianLaw n)) -
        ∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (grassmannian n)| ≤
      4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ n := by
  refine (grass_expectation_diff_tv n hn).trans ?_
  calc
    _ ≤ (2 * (n : ℝ)) * (2 * (n : ℝ) / (2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left (grass_pair_totalVariation_pow_le n) (by positivity)
    _ = _ := by ring

/-- Modified and uniform Grassmannian forward-stability means have vanishing difference. -/
theorem tendsto_grass_expectation_diff :
    Tendsto (fun n : ℕ =>
      (∫ p, (productForwardStability p.1 p.2 : ℝ)
        ∂(grassmannianLaw n).prod (grassmannianLaw n)) -
          ∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (grassmannian n))
      atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => 4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)).const_mul 4
  have hlo : Tendsto (fun n : ℕ => -(4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ n))
      atTop (𝓝 0) := by simpa only [neg_zero] using hb.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hb
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (abs_le.mp (grass_expectation_diff_bound n hn)).1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (abs_le.mp (grass_expectation_diff_bound n hn)).2

/-- Normalized forward-stability pushforward laws have the same exponential distance bound. -/
theorem grass_normalized_tv_le (n : ℕ) :
    totalVariation
      (((grassmannianLaw n).prod (grassmannianLaw n)).map fun p =>
        ((productForwardStability p.1 p.2 : ℝ) - (3 : ℝ) / 2 * n) / Real.sqrt n)
      ((pairLaw (grassmannian n)).map fun p =>
        ((productForwardStability p.1 p.2 : ℝ) - (3 : ℝ) / 2 * n) / Real.sqrt n) ≤
      2 * (n : ℝ) / (2 : ℝ) ^ n := by
  let N (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) : ℝ :=
    ((productForwardStability p.1 p.2 : ℝ) - (3 : ℝ) / 2 * n) / Real.sqrt n
  have hN : Measurable N := measurable_of_countable _
  have h := totalVariation_map_le_finite ((finiteModel n).prod (finiteModel n))
    ((finiteUniform n).prod (finiteUniform n)) (N ∘ pairMap n)
  rw [← Measure.map_map hN (pairMap_measurable n),
    ← Measure.map_map hN (pairMap_measurable n), finiteModel_pair,
    finiteUniform_pair, ← finitePair_tv] at h
  exact h.trans (grass_pair_totalVariation_pow_le n)

/-- The normalized modified and uniform forward-stability laws have distance tending to zero. -/
theorem tendsto_grass_normalized_tv :
    Tendsto (fun n : ℕ => totalVariation
      (((grassmannianLaw n).prod (grassmannianLaw n)).map fun p =>
        ((productForwardStability p.1 p.2 : ℝ) - (3 : ℝ) / 2 * n) / Real.sqrt n)
      ((pairLaw (grassmannian n)).map fun p =>
        ((productForwardStability p.1 p.2 : ℝ) - (3 : ℝ) / 2 * n) / Real.sqrt n))
      atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => 2 * (n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero, mul_div_assoc] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)).const_mul 2
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ =>
    Real.iSup_nonneg fun _ => abs_nonneg _) (Filter.Eventually.of_forall grass_normalized_tv_le) hb

end RecordStability
