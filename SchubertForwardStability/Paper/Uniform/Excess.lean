import SchubertForwardStability.Paper.Uniform.SecondGaussian
import SchubertForwardStability.Paper.Uniform.Overshoot
import SchubertForwardStability.Paper.Uniform.Variance
import SchubertForwardStability.LimitTheorems.Convergence.FirstMoment
import SchubertForwardStability.Permutations.ForMathlib.UniformIntegrable

/-! # Vanishing normalized uniform record-walk excess

## Main results

The intrinsic excess is bounded in mean by two under the finite uniform pair law.
Dividing by the logarithmic standard deviation makes it vanish in probability.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory Filter
open scoped Classical BigOperators Topology

/-- The intrinsic maximum lies below the ambient tail maximum starting at two. -/
theorem recordWalkMax_le_maxFrom_second {n : ℕ} (u v : FinitaryPerm ℕ+)
    (hu : u.forwardStability ≤ n) (hv : v.forwardStability ≤ n) :
    recordWalkMax u v ≤ recordWalkMaxFrom n 2 u v := by
  obtain ⟨j, hj, he⟩ := exists_recordWalk_eq_maxAt
    (max u.forwardStability v.forwardStability) u v
  change recordWalk u v j = recordWalkMax u v at he
  rw [← he]
  by_cases hij : (2 : ℕ+) ≤ j
  · exact recordWalk_le_maxFrom 2 u v hij (hj.trans (Nat.add_le_add_right (max_le hu hv) 1))
  · have hj1 : j = 1 := by
      apply PNat.eq
      change (j : ℕ) = 1
      have hp := PNat.pos j
      change ¬(2 : ℕ) ≤ (j : ℕ) at hij
      omega
    subst j
    have hs := recordWalkStep_eq u v 1
    rw [nonRecordIndicator_eq_zero (isRecord_first u),
      nonRecordIndicator_eq_zero (isRecord_first v)] at hs
    change recordWalk u v 2 - recordWalk u v 1 = 1 - 0 - 0 at hs
    have hn := u.one_le_forwardStability.trans hu
    calc
      _ ≤ recordWalk u v 2 := by omega
      _ ≤ _ := recordWalk_le_maxFrom 2 u v le_rfl (by change 2 ≤ n + 1; omega)

/-- Reciprocal-square sums over a positive initial interval equal the finite variance correction. -/
theorem sum_Icc_reciprocalSquares (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, 1 / ((j : ℝ) ^ 2)) = reciprocalSquares n := by
  unfold reciprocalSquares
  apply Finset.sum_bij (fun j hj =>
    (⟨j - 1, by have h := Finset.mem_Icc.mp hj; omega⟩ : Fin n))
  · intro j hj
    exact Finset.mem_univ _
  · intro a ha b hb he
    have h := congrArg Fin.val he
    have hpa := Finset.mem_Icc.mp ha
    have hpb := Finset.mem_Icc.mp hb
    dsimp at h
    omega
  · intro k _
    refine ⟨k.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    apply Fin.ext
    simp
  · intro j hj
    have hp := (Finset.mem_Icc.mp hj).1
    have hc : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hp
    dsimp
    rw [hc]
    simp [one_div, inv_pow]

/-- Uniform intrinsic excess has a fixed first-moment bound at sizes at least two. -/
theorem integral_uniform_excess_le_two (n : ℕ) (hn : 2 ≤ n) :
    (∫ p, (recordWalkExcess p.1 p.2 : ℝ) ∂pairLaw (symmetricGroup n)) ≤ 2 := by
  calc
    _ ≤ ∫ p, ((recordWalkMaxFrom n 2 p.1 p.2 - recordWalk p.1 p.2 2 : ℤ) : ℝ)
        ∂pairLaw (symmetricGroup n) := by
      apply integral_uniform_finset_mono
      intro p hp
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
      have hfu := (p.1.forwardStability_le_iff (by omega : 1 ≤ n)).mpr
        ((mem_symmetricGroup n p.1).mp hu)
      have hfv := (p.2.forwardStability_le_iff (by omega : 1 ≤ n)).mpr
        ((mem_symmetricGroup n p.2).mp hv)
      have hb := recordWalkMax_le_maxFrom_second p.1 p.2 hfu hfv
      unfold recordWalkExcess
      exact_mod_cast sub_le_sub_right hb (recordWalk p.1 p.2 2)
    _ ≤ ∑ j ∈ Finset.Icc 2 n, 1 / ((j : ℝ) ^ 2) :=
      integral_uniform_overshoot n 2 hn
    _ ≤ ∑ j ∈ Finset.Icc 1 n, 1 / ((j : ℝ) ^ 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        have h := Finset.mem_Icc.mp hj
        exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
      · intro j _ _
        positivity
    _ = reciprocalSquares n := sum_Icc_reciprocalSquares n
    _ ≤ 2 := reciprocalSquares_le_two n

/-- The normalized excess above the second uniform walk value vanishes in probability. -/
theorem uniform_excess_vanishes :
    LimitTheorems.TendstoInProbability
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        (recordWalkExcess p.1 p.2 : ℝ) / Real.sqrt (2 * Real.log n))
      atTop (0 : ℝ) (fun n => pairLaw (symmetricGroup n)) := by
  apply LimitTheorems.tendstoInProbability_of_integral_norm
  · intro n
    exact integrable_uniform_finset _ _
  · have he (n : ℕ) :
        (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
          ‖(recordWalkExcess p.1 p.2 : ℝ) / Real.sqrt (2 * Real.log n)‖) =
        (fun p => (recordWalkExcess p.1 p.2 : ℝ) / Real.sqrt (2 * Real.log n)) := by
      funext p
      apply Real.norm_of_nonneg
      exact div_nonneg (by exact_mod_cast recordWalkExcess_nonneg p.1 p.2)
        (Real.sqrt_nonneg _)
    have hlim : Tendsto (fun n : ℕ => (2 : ℝ) / Real.sqrt (2 * Real.log n))
        atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
          tendsto_inv_secondRecordScale
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ => integral_nonneg (fun _ => norm_nonneg _))
      _ hlim
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [he n, integral_div]
    exact div_le_div_of_nonneg_right (integral_uniform_excess_le_two n hn) (Real.sqrt_nonneg _)

end RecordStability
