import SchubertForwardStability.Paper.Backward.Clipping
import SchubertForwardStability.Paper.Boolean.Expectation

/-! # Clipped product forward stability for Boolean permutations

## Main results

* `integral_boolean_deficit_le`: at every size `n`, the mean deficit `max 0 (n - F)` is
  at most one third.
* `boolean_clipped_expectation`: the mean of `max n F` is `n` plus a bounded error.

## Implementation notes

Here `F` is product forward stability of two independent uniform Boolean permutations of
size `n`. The deficit is dominated by the deficit of the larger individual forward
stability, whose mean is at most one third by its factor-four tails. A lower bound on the
mean of `F` alone would not bound the mean positive deficit.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial MeasureTheory ProbabilityTheory Filter Asymptotics

/-- At every size, the Boolean mean deficit below the ambient size is at most one third. -/
theorem integral_boolean_deficit_le (n : ℕ) :
    (∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2) ∂pairLaw (boolean n)) ≤
      1 / 3 := by
  have hmono : (∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2)
      ∂pairLaw (boolean n)) ≤
      ∫ p, ((n - max p.1.forwardStability p.2.forwardStability : ℕ) : ℝ)
        ∂pairLaw (boolean n) :=
    integral_uniform_finset_mono _ _ _ fun p _ => deficit_le_forward_deficit n p.1 p.2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine hmono.trans (le_of_eq_of_le ?_ (by norm_num : (0 : ℝ) ≤ 1 / 3))
    simp only [Nat.zero_sub, Nat.cast_zero, integral_zero]
  · exact hmono.trans (integral_boolean_pair_deficit_le n hn)

/-- The Boolean clipped mean lies between the ambient size and the forward mean plus
one third. -/
theorem integral_boolean_clipped_bounds (n : ℕ) :
    (n : ℝ) ≤ ∫ p, max (n : ℝ) (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (boolean n) ∧
      (∫ p, max (n : ℝ) (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (boolean n)) ≤
        (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (boolean n)) + 1 / 3 := by
  refine ⟨?_, ?_⟩
  · have h := integral_mono_of_nonneg (μ := pairLaw (boolean n))
      (f := fun _ => (n : ℝ))
      (g := fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
        max (n : ℝ) (productForwardStability p.1 p.2 : ℝ))
      (Eventually.of_forall fun _ => Nat.cast_nonneg n)
      (integrable_uniform_finset _ _) (Eventually.of_forall fun _ => le_max_left _ _)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h
  · rw [integral_clipped_eq]
    linarith [integral_boolean_deficit_le n]

/-- The mean Boolean forward stability clipped at the ambient size is the ambient size
plus a bounded error. -/
theorem boolean_clipped_expectation :
    IsBigO atTop (fun n : ℕ =>
      (∫ p, max (n : ℝ) (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (boolean n)) - n)
      (fun _ => (1 : ℝ)) := by
  have hD : IsBigO atTop (fun n : ℕ =>
      ∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2) ∂pairLaw (boolean n))
      (fun _ => (1 : ℝ)) := by
    apply IsBigO.of_bound (1 / 3)
    filter_upwards [] with n
    rw [Real.norm_of_nonneg (integral_deficit_nonneg n _), norm_one, mul_one]
    exact integral_boolean_deficit_le n
  refine (boolean_product_expectation.add hD).congr_left fun n => ?_
  rw [integral_clipped_eq]
  ring

end RecordStability
