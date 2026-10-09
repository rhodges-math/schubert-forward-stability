import SchubertForwardStability.Paper.Grassmannian.CardGaussian
import SchubertForwardStability.Paper.Grassmannian.Negligible
import SchubertForwardStability.Paper.Grassmannian.LimitTransfer
import SchubertForwardStability.LimitTheorems.Convergence.Slutsky

/-! # Gaussian maximum limit of encoded Grassmannian product stability

For independent uniform Grassmannian permutations `u, v` of size `n`,
`(FS(u,v) - 3n/2)/sqrt(n)` converges in distribution to `-max(Z_1, Z_2)/2`, where `Z_1`
and `Z_2` are independent standard Gaussians. The limit is obtained under the subset model
and then transferred to the uniform law.

## Main results

* `RecordStability.grassmannian_encoded_gaussian`: the limit under the subset model.
* `RecordStability.grassmannian_gaussian`: the limit for the uniform law.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Theorem 1.4 and Proposition 4.12.
-/

open FinitaryPerm RecordStability SchubertPolynomial MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace RecordStability

/-- The subset product statistic tends to minus half the maximum of two Gaussians. -/
theorem subset_product_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : Finset ℕ+ × Finset ℕ+) =>
        ((productForwardStability (subsetPermutation n p.1)
          (subsetPermutation n p.2) : ℝ) - (3 : ℝ) / 2 * n) / Real.sqrt n)
      atTop (fun p : ℝ × ℝ => -(1 / 2 : ℝ) * max p.1 p.2)
      (fun n => (subsetLaw n).prod (subsetLaw n))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  apply LimitTheorems.tendstoInDistribution_of_sub subset_card_maximum_gaussian
  · simpa only [neg_div, sub_neg_eq_add] using grassmannian_scaled_error_zero
  · intro n
    exact (measurable_of_countable _).aemeasurable

/-- Encoded Grassmannian product stability has the Gaussian maximum limit. -/
theorem grassmannian_encoded_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        ((productForwardStability p.1 p.2 : ℝ) - (3 : ℝ) / 2 * n) / Real.sqrt n)
      atTop (fun p : ℝ × ℝ => -(1 / 2 : ℝ) * max p.1 p.2)
      (fun n => (grassmannianLaw n).prod (grassmannianLaw n))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  apply LimitTheorems.tendstoInDistribution_law_congr subset_product_gaussian
  · intro n
    exact (measurable_of_countable _).aemeasurable
  · have hm : Measurable (fun p : ℝ × ℝ => -(1 / 2 : ℝ) * max p.1 p.2) := by
      fun_prop
    exact hm.aemeasurable
  · intro n
    rw [grassmannianLaw, Measure.map_prod_map _ _
      (measurable_subsetPermutation n) (measurable_subsetPermutation n),
      Measure.map_map (measurable_of_countable _)
        ((measurable_subsetPermutation n).prodMap (measurable_subsetPermutation n))]
    rfl
  · rfl

/-- Uniform Grassmannian product stability has the Gaussian maximum limit. -/
theorem grassmannian_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        ((productForwardStability p.1 p.2 : ℝ) - (3 : ℝ) / 2 * n) / Real.sqrt n)
      atTop (fun p : ℝ × ℝ => -(1 / 2 : ℝ) * max p.1 p.2)
      (fun n => pairLaw (grassmannian n)) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  exact LimitTheorems.tendstoInDistribution_finite_tv
    (fun n => (grassmannian n).product (grassmannian n))
    ae_grass_pair_model ae_grass_pair_uniform tendsto_grass_pair_tv
    grassmannian_encoded_gaussian

end RecordStability
