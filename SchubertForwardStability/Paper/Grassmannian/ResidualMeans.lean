import SchubertForwardStability.Paper.Grassmannian.ResidualEvents
import SchubertForwardStability.Permutations.ForMathlib.UniformIntegrals
import Mathlib.Analysis.Asymptotics.Defs

/-! # Exponentially small residual means

## Main results

The absolute residual is bounded by the ambient size times its nonzero-event
indicator. An elementary exponential inequality absorbs this factor into half
the probability decay rate.
-/

open FinitaryPerm MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Classical Topology

namespace RecordStability

/-- The absolute residual mean is at most the ambient bound times its exception probability. -/
theorem integral_subset_residual_abs_le (n : ℕ) :
    (∫ p, |(grassmannianResidual n p.1 p.2 : ℝ)|
      ∂(subsetLaw n).prod (subsetLaw n)) ≤
      (max 1 n : ℕ) * ((subsetLaw n).prod (subsetLaw n)).real
        {p | grassmannianResidual n p.1 p.2 ≠ 0} := by
  let E := {p : Finset ℕ+ × Finset ℕ+ | grassmannianResidual n p.1 p.2 ≠ 0}
  calc
    _ ≤ ∫ p, E.indicator (fun _ => ((max 1 n : ℕ) : ℝ)) p
        ∂(subsetLaw n).prod (subsetLaw n) := by
      rw [subsetLaw, ←uniformOn_finset_prod]
      apply integral_uniform_finset_mono
      intro p hp
      obtain ⟨hV, hW⟩ := Finset.mem_product.mp hp
      by_cases h : grassmannianResidual n p.1 p.2 = 0
      · simp [E, h]
      · rw [Set.indicator_of_mem (show p ∈ E from h)]
        exact_mod_cast subset_residual_abs_le n p.1 p.2
          (Finset.mem_powerset.mp hV) (Finset.mem_powerset.mp hW)
    _ = _ := by
      rw [integral_indicator_const _ (.of_discrete), smul_eq_mul]
      exact mul_comm _ _

private theorem max_mul_exp_le (c : ℝ) (hc : 0 < c) (n : ℕ) :
    ((max 1 n : ℕ) : ℝ) * Real.exp (-c * n) ≤
      (1 + 2 / c) * Real.exp (-(c / 2) * n) := by
  let E := Real.exp ((c / 2) * n)
  have he : 1 ≤ E := Real.one_le_exp (by positivity)
  have hx : (c / 2) * (n : ℝ) ≤ E := by
    have h := Real.add_one_le_exp ((c / 2) * n)
    dsimp [E]
    linarith
  have hn : (n : ℝ) ≤ (2 / c) * E := by
    have h : (n : ℝ) ≤ E / (c / 2) :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < c / 2)).mpr (by nlinarith [hx])
    have hd : E / (c / 2) = (2 / c) * E := by
      rw [div_div_eq_mul_div]
      ring
    rwa [hd] at h
  have hm : ((max 1 n : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast (by omega : max 1 n ≤ n + 1)
  have hb : ((max 1 n : ℕ) : ℝ) ≤ (1 + 2 / c) * E := by
    nlinarith
  calc
    _ ≤ (1 + 2 / c) * E * Real.exp (-c * n) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
    _ = _ := by
      dsimp [E]
      rw [mul_assoc, ←Real.exp_add]
      rw [show (c / 2) * (n : ℝ) + -c * n = -(c / 2) * n by ring]

/-- Residual probability and absolute mean each have a strictly positive exponential rate. -/
theorem grassmannian_residual_bounds :
    ∃ c : ℝ, 0 < c ∧
      (fun n : ℕ => ((subsetLaw n).prod (subsetLaw n)).real
        {p | grassmannianResidual n p.1 p.2 ≠ 0}) =O[atTop]
          (fun n : ℕ => Real.exp (-c * n)) ∧
      ∃ d : ℝ, 0 < d ∧
        (fun n : ℕ => ∫ p, |(grassmannianResidual n p.1 p.2 : ℝ)|
          ∂(subsetLaw n).prod (subsetLaw n)) =O[atTop]
            (fun n : ℕ => Real.exp (-d * n)) := by
  obtain ⟨c, hc, h⟩ := subset_residual_probability_tail
  refine ⟨c, hc, ?_, c / 2, by positivity, ?_⟩
  · apply IsBigO.of_bound 4
    filter_upwards [] with n
    rw [Real.norm_of_nonneg measureReal_nonneg, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact h n
  · apply IsBigO.of_bound (4 * (1 + 2 / c))
    filter_upwards [] with n
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => abs_nonneg _),
      Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ (max 1 n : ℕ) * ((subsetLaw n).prod (subsetLaw n)).real
          {p | grassmannianResidual n p.1 p.2 ≠ 0} := integral_subset_residual_abs_le n
      _ ≤ ((max 1 n : ℕ) : ℝ) * (4 * Real.exp (-c * n)) :=
        mul_le_mul_of_nonneg_left (h n) (Nat.cast_nonneg _)
      _ = 4 * (((max 1 n : ℕ) : ℝ) * Real.exp (-c * n)) := by ring
      _ ≤ 4 * ((1 + 2 / c) * Real.exp (-(c / 2) * n)) :=
        mul_le_mul_of_nonneg_left (max_mul_exp_le c hc n) (by norm_num)
      _ = _ := by ring

end RecordStability
