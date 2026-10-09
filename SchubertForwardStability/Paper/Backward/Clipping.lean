import SchubertForwardStability.SchubertPolynomials.Products.RecordBound
import SchubertForwardStability.Permutations.Random.Uniform
import SchubertForwardStability.Permutations.ForMathlib.UniformIntegrals
import SchubertForwardStability.Permutations.ForMathlib.UniformIntegrable
import SchubertForwardStability.LimitTheorems.Convergence.Slutsky
import SchubertForwardStability.LimitTheorems.Convergence.FirstMoment

/-! # Product forward stability clipped at the ambient size

## Main results

* `max_forwardStability_le_product`: product forward stability dominates both
  individual forward stabilities.
* `integral_clipped_eq`: under a finite uniform pair law, the mean of `max n F` is the
  mean of `F` plus the mean deficit `max 0 (n - F)`.
* `tendsto_clipped_integral`, `tendstoInDistribution_clipped`: a vanishing mean deficit
  carries centered mean limits and normalized distributional limits from `F` to `max n F`.

## Implementation notes

Here `F` is `productForwardStability p.1 p.2` for a sampled pair `p`. The clipped
statistic and the deficit are real-valued, so the deficit is an ordinary maximum with zero.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- Product forward stability dominates the larger of the two individual stabilities. -/
theorem max_forwardStability_le_product (u v : FinitaryPerm ℕ+) :
    max u.forwardStability v.forwardStability ≤ productForwardStability u v := by
  rw [productForwardStability_eq_suffixBound]
  exact max_forward_le_pairSuffixBound u v

/-- The clipped statistic exceeds the statistic by its deficit below the clipping level. -/
theorem max_sub_eq_deficit (x y : ℝ) : max x y - y = max 0 (x - y) := by
  rw [← max_sub_sub_right, sub_self, max_comm]

/-- The deficit below the ambient size is at most the deficit of the larger
individual forward stability. -/
theorem deficit_le_forward_deficit (n : ℕ) (u v : FinitaryPerm ℕ+) :
    max 0 ((n : ℝ) - productForwardStability u v) ≤
      ((n - max u.forwardStability v.forwardStability : ℕ) : ℝ) := by
  have hm := max_forwardStability_le_product u v
  apply max_le (Nat.cast_nonneg _)
  rcases le_total (max u.forwardStability v.forwardStability) n with h | h
  · rw [Nat.cast_sub h]
    have hc : ((max u.forwardStability v.forwardStability : ℕ) : ℝ) ≤
        (productForwardStability u v : ℝ) := by exact_mod_cast hm
    linarith
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, sub_nonpos]
    exact_mod_cast h.trans hm

/-- Under a finite uniform pair law, the clipped mean is the forward mean plus the
mean deficit. -/
theorem integral_clipped_eq (n : ℕ) (W : Finset (FinitaryPerm ℕ+)) :
    (∫ p, max (n : ℝ) (productForwardStability p.1 p.2 : ℝ) ∂pairLaw W) =
      (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw W) +
        ∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2) ∂pairLaw W := by
  have he : (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
      max (n : ℝ) (productForwardStability p.1 p.2 : ℝ)) =
      fun p => (productForwardStability p.1 p.2 : ℝ) +
        max 0 ((n : ℝ) - productForwardStability p.1 p.2) := by
    funext p
    rw [← max_sub_eq_deficit]
    ring
  rw [he]
  exact integral_uniform_finset_add _ _ _

/-- The mean deficit below the ambient size is nonnegative. -/
theorem integral_deficit_nonneg (n : ℕ) (W : Finset (FinitaryPerm ℕ+)) :
    0 ≤ ∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2) ∂pairLaw W :=
  integral_nonneg fun _ => le_max_left _ _

/-- A centered limit of forward means passes to the clipped means when the mean
deficit vanishes. -/
theorem tendsto_clipped_integral {W : ℕ → Finset (FinitaryPerm ℕ+)} {a : ℕ → ℝ} {c : ℝ}
    (hF : Tendsto (fun n : ℕ =>
      (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (W n)) - a n) atTop (𝓝 c))
    (hD : Tendsto (fun n : ℕ =>
      ∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2) ∂pairLaw (W n))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∫ p, max (n : ℝ) (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (W n)) - a n)
      atTop (𝓝 c) := by
  have h := hF.add hD
  rw [add_zero] at h
  refine h.congr fun n => ?_
  rw [integral_clipped_eq]
  ring

/-- A normalized distributional limit passes to the clipped statistic when the mean
deficit divided by the nonnegative scale vanishes. -/
theorem tendstoInDistribution_clipped {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {W : ℕ → Finset (FinitaryPerm ℕ+)}
    [∀ n, IsProbabilityMeasure (pairLaw (W n))] {a b : ℕ → ℝ} {Z : Ω' → ℝ}
    (hb : ∀ n, 0 ≤ b n)
    (hF : TendstoInDistribution (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
      ((productForwardStability p.1 p.2 : ℝ) - a n) / b n) atTop Z
      (fun n => pairLaw (W n)) μ')
    (hD : Tendsto (fun n : ℕ =>
      (∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2) ∂pairLaw (W n)) / b n)
      atTop (𝓝 0)) :
    TendstoInDistribution (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
      (max (n : ℝ) (productForwardStability p.1 p.2 : ℝ) - a n) / b n) atTop Z
      (fun n => pairLaw (W n)) μ' := by
  have he (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) :
      (max (n : ℝ) (productForwardStability p.1 p.2 : ℝ) - a n) / b n -
        ((productForwardStability p.1 p.2 : ℝ) - a n) / b n =
      max 0 ((n : ℝ) - productForwardStability p.1 p.2) / b n := by
    rw [← sub_div, ← max_sub_eq_deficit]
    ring_nf
  apply LimitTheorems.tendstoInDistribution_of_sub hF
  · apply LimitTheorems.tendstoInProbability_of_integral_norm
    · intro n
      exact integrable_uniform_finset _ _
    · refine hD.congr fun n => ?_
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [] with p
      rw [he, Real.norm_of_nonneg (div_nonneg (le_max_left _ _) (hb n))]
  · intro n
    exact (measurable_of_countable _).aemeasurable

end RecordStability
