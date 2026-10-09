import SchubertForwardStability.Paper.Uniform.PairGaussian
import SchubertForwardStability.Paper.Walk.Tails
import SchubertForwardStability.Permutations.Statistics.RecordSums
import SchubertForwardStability.Permutations.Random.PointMasses

/-! # The Gaussian limit of the second uniform record-walk value

For independent uniform `u, v` in `S_n`, the second value `Y_2 = Λ_2(u) + Λ_2(v) + 1` of
the record walk satisfies `(Y_2 - (2n - 2*log(n)))/sqrt(2*log(n)) → N(0, 1)` in
distribution.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Lemma 3.8.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

/-- The reciprocal second-walk Gaussian scale tends to zero. -/
theorem tendsto_inv_secondRecordScale :
    Tendsto (fun n : ℕ => (1 : ℝ) / Real.sqrt (2 * Real.log n)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => Real.sqrt (2 * Real.log n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Tendsto.const_mul_atTop (by norm_num) hlog)
  exact tendsto_const_nhds.div_atTop hs

/-- The normalized second walk value under the uniform independent-pair law tends to Gaussian. -/
theorem uniform_second_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        ((recordWalk p.1 p.2 2 : ℝ) - (2 * n - 2 * Real.log n)) /
          Real.sqrt (2 * Real.log n))
      atTop id (fun n => pairLaw (symmetricGroup n)) (gaussianReal 0 1) := by
  have hadd := LimitTheorems.slutsky_add uniform_record_pair_gaussian
    (LimitTheorems.tendstoInProbability_of_tendsto
      (μ := fun n => pairLaw (symmetricGroup n)) tendsto_inv_secondRecordScale)
    (fun _ => measurable_const.aemeasurable)
  apply hadd.congr (T := id)
  · intro n
    have hp : ∀ᵐ p ∂pairLaw (symmetricGroup n),
        p ∈ (symmetricGroup n).product (symmetricGroup n) := by
      exact ae_mem_uniformOn_finset _
        ⟨(1, 1), Finset.mem_product.mpr
          ⟨one_mem_symmetricGroup n, one_mem_symmetricGroup n⟩⟩
    filter_upwards [hp] with p hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
    have hr := recordWalk_second p.1 p.2
      ((mem_symmetricGroup n p.1).mp hu) ((mem_symmetricGroup n p.2).mp hv)
    rw [hr]
    push_cast
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    by_cases hl : Real.sqrt (Real.log n) = 0
    · simp [hl]
    · have htwo : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      field_simp
      ring
  · exact Filter.Eventually.of_forall (fun x : ℝ => by simp)

end RecordStability
