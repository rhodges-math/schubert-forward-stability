import SchubertForwardStability.LimitTheorems.Convergence.FiniteLawChange
import SchubertForwardStability.Paper.Grassmannian.Transfer

/-! # Finite supports for Grassmannian law transfer

Both Grassmannian pair laws are supported on the same finite permutation family,
and their total-variation distance tends to zero.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Section 4.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory LimitTheorems Filter
open scoped Classical Topology

/-- The encoded Grassmannian pair law is supported on the ambient Grassmannian square. -/
theorem ae_grass_pair_model (n : ℕ) :
    ∀ᵐ p ∂(grassmannianLaw n).prod (grassmannianLaw n),
      p ∈ (grassmannian n).product (grassmannian n) := by
  apply (Measure.ae_prod_iff_ae_ae .of_discrete).mpr
  filter_upwards [ae_mem_grassmannianLaw n] with u hu
  filter_upwards [ae_mem_grassmannianLaw n] with v hv
  exact Finset.mem_product.mpr ⟨hu, hv⟩

/-- The uniform Grassmannian pair law is supported on the same ambient square. -/
theorem ae_grass_pair_uniform (n : ℕ) :
    ∀ᵐ p ∂pairLaw (grassmannian n),
      p ∈ (grassmannian n).product (grassmannian n) := by
  rw [pairLaw_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae .of_discrete).mpr
  filter_upwards [ae_mem_unif _ ⟨1, one_mem_grassmannian n⟩] with u hu
  filter_upwards [ae_mem_unif _ ⟨1, one_mem_grassmannian n⟩] with v hv
  exact Finset.mem_product.mpr ⟨hu, hv⟩

/-- The encoded and uniform Grassmannian pair-law distance tends to zero. -/
theorem tendsto_grass_pair_tv :
    Tendsto (fun n : ℕ => totalVariation
      ((grassmannianLaw n).prod (grassmannianLaw n)) (pairLaw (grassmannian n)))
      atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => 2 * (n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero, mul_div_assoc] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)).const_mul 2
  apply squeeze_zero (fun _ => Real.iSup_nonneg fun _ => abs_nonneg _)
    grass_pair_totalVariation_pow_le hb

end RecordStability
