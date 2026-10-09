import SchubertForwardStability.Paper.Uniform.LogScale
import SchubertForwardStability.Permutations.Random.FamilyInstances
import SchubertForwardStability.LimitTheorems.Convergence.LawChange
import SchubertForwardStability.LimitTheorems.Convergence.Independent
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Gaussian limits for independent uniform record counts

For independent uniform `u, v` in `S_n`, the record counts, centered at `log(n)` and divided
by `sqrt(log(n))`, have independent standard Gaussian limits. Hence minus their normalized
sum, divided by `sqrt(2)`, tends to a standard Gaussian.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology NNReal

/-- The two logarithmically normalized record counts have independent Gaussian limits. -/
theorem uniform_record_joint_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        (((recordCount n p.1 : ℝ) - Real.log n) / Real.sqrt (Real.log n),
          ((recordCount n p.2 : ℝ) - Real.log n) / Real.sqrt (Real.log n)))
      atTop id (fun n => pairLaw (symmetricGroup n))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let X (n : ℕ) (w : FinitaryPerm ℕ+) :=
    ((recordCount n w : ℝ) - Real.log n) / Real.sqrt (Real.log n)
  have hX (n : ℕ) : Measurable (X n) := measurable_of_countable _
  have hf : TendstoInDistribution (fun (n : ℕ) p => X n p.1) atTop
      (Prod.fst : ℝ × ℝ → ℝ) (fun n => pairLaw (symmetricGroup n))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    apply LimitTheorems.tendstoInDistribution_law_congr uniform_record_gaussian
    · intro n
      exact ((hX n).comp measurable_fst).aemeasurable
    · exact measurable_fst.aemeasurable
    · intro n
      change Measure.map (X n ∘ Prod.fst) _ = _
      rw [pairLaw_eq_prod, ← Measure.map_map (hX n) measurable_fst]
      simp [X]
    · simp
  have hs : TendstoInDistribution (fun (n : ℕ) p => X n p.2) atTop
      (Prod.snd : ℝ × ℝ → ℝ) (fun n => pairLaw (symmetricGroup n))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    apply LimitTheorems.tendstoInDistribution_law_congr uniform_record_gaussian
    · intro n
      exact ((hX n).comp measurable_snd).aemeasurable
    · exact measurable_snd.aemeasurable
    · intro n
      change Measure.map (X n ∘ Prod.snd) _ = _
      rw [pairLaw_eq_prod, ← Measure.map_map (hX n) measurable_snd]
      simp [X]
    · simp
  apply LimitTheorems.tendstoInDistribution_indep hf hs
  · intro n
    rw [pairLaw_eq_prod]
    exact indepFun_prod (hX n) (hX n)
  · exact indepFun_prod measurable_id measurable_id

/-- The negative sum of two independent standard Gaussians, divided by sqrt two, is standard. -/
theorem gaussian_normalized_negative_sum_law :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => -(p.1 + p.2) / Real.sqrt 2) = gaussianReal 0 1 := by
  have hadd : ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => p.1 + p.2) = gaussianReal 0 2 := by
    have h := gaussianReal_add_gaussianReal_of_indepFun
      (X := (Prod.fst : ℝ × ℝ → ℝ)) (Y := (Prod.snd : ℝ × ℝ → ℝ))
      (indepFun_prod measurable_id measurable_id)
      (measurePreserving_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)).hasLaw
      (measurePreserving_snd (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)).hasLaw
    have he : (Prod.fst : ℝ × ℝ → ℝ) + Prod.snd =
        (fun p : ℝ × ℝ => p.1 + p.2) := by
      funext p
      rfl
    rw [he] at h
    norm_num at h
    exact h
  change Measure.map ((fun x : ℝ => -x / Real.sqrt 2) ∘
    (fun p : ℝ × ℝ => p.1 + p.2)) _ = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), hadd]
  change Measure.map ((fun x : ℝ => x / Real.sqrt 2) ∘ Neg.neg) _ = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_neg,
    gaussianReal_map_div_const]
  have hv : NNReal.mk ((Real.sqrt 2) ^ 2) (sq_nonneg _) = 2 := by
    apply NNReal.eq
    change (Real.sqrt (2 : ℝ)) ^ 2 = (2 : ℝ)
    exact Real.sq_sqrt (by norm_num)
  rw [hv]
  norm_num

/-- The negative sum of two centered uniform record counts has a standard Gaussian limit. -/
theorem uniform_record_pair_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        -(((recordCount n p.1 : ℝ) - Real.log n) / Real.sqrt (Real.log n) +
          ((recordCount n p.2 : ℝ) - Real.log n) / Real.sqrt (Real.log n)) /
            Real.sqrt 2)
      atTop id (fun n => pairLaw (symmetricGroup n)) (gaussianReal 0 1) := by
  have h := uniform_record_joint_gaussian.continuous_comp
    (g := fun p : ℝ × ℝ => -(p.1 + p.2) / Real.sqrt 2) (by fun_prop)
  apply LimitTheorems.tendstoInDistribution_law_congr h
  · exact h.forall_aemeasurable
  · exact measurable_id.aemeasurable
  · intro n
    rfl
  · simpa using gaussian_normalized_negative_sum_law.symm

end RecordStability
