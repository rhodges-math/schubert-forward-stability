import SchubertForwardStability.Permutations.ForMathlib.UniformIntegrals
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Finite tail sums for natural-valued statistics

This file contains general results that extend Mathlib. A bounded natural value is the sum
of its positive threshold indicators, and finite uniform integration gives the tail-sum
formula for its mean.
-/

namespace Nat

open scoped Classical BigOperators

/-- A bounded natural value equals the finite sum of its positive threshold indicators. -/
theorem cast_eq_sum_thresholds (k N : ℕ) (hk : k ≤ N) :
    (k : ℝ) = ∑ t ∈ Finset.Icc 1 N, if t ≤ k then (1 : ℝ) else 0 := by
  have hFilter : (Finset.Icc 1 N).filter (fun t => t ≤ k) = Finset.Icc 1 k := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [Finset.sum_ite]
  simp [hFilter]

end Nat

namespace ProbabilityTheory

open MeasureTheory
open scoped Classical BigOperators

/-- The mean of a bounded natural statistic under a finite uniform law is the sum of its
tail probabilities. -/
theorem integral_uniform_nat_tails {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] (W : Finset α) (X : α → ℕ)
    (N : ℕ) (hX : ∀ x ∈ W, X x ≤ N) :
    (∫ x, (X x : ℝ) ∂uniformOn (W : Set α)) =
      ∑ t ∈ Finset.Icc 1 N, (uniformOn (W : Set α)).real {x | t ≤ X x} := by
  calc
    _ = ∫ x, ∑ t ∈ Finset.Icc 1 N, if t ≤ X x then (1 : ℝ) else 0
        ∂uniformOn (W : Set α) := by
      apply integral_uniform_finset_congr
      intro x hx
      exact Nat.cast_eq_sum_thresholds (X x) N (hX x hx)
    _ = _ := by
      rw [integral_uniform_finsetSum]
      apply Finset.sum_congr rfl
      intro t _
      have hF : (fun x : α => if t ≤ X x then (1 : ℝ) else 0) =
          {x : α | t ≤ X x}.indicator (fun _ => (1 : ℝ)) := by
        funext x
        simp [Set.indicator]
      rw [hF, integral_indicator_const (1 : ℝ) (Set.to_countable _).measurableSet,
        smul_eq_mul, mul_one]

end ProbabilityTheory
