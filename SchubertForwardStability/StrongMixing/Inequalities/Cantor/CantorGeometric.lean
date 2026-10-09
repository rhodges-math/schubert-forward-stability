import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorLaplace
import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorLengths

/-!
# Geometric-mixing errors for rounded Cantor blocks

The natural gaps in the rounded construction dominate the prescribed fractional
deletion. Under an exponential coefficient bound, the dyadic Laplace errors
are bounded by an explicit geometrically weighted exponential sum.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Under `alpha(h) <= exp(-2 * c * h)` and `t * M <= c * δ`, the rounded
Cantor block log-Laplace transform is bounded by its terminal transforms plus
`sum (2 ^ k * exp(-c * δ * L k))`, using the natural gaps of the rounded construction.
Zero deletion fraction and zero Laplace parameter are allowed. -/
theorem cantor_geometric_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c δ : ℝ}
    (hM : 0 ≤ M) (hc : 0 ≤ c) (hδ1 : δ ≤ 1)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (n d : ℕ) (a : ℤ) {t : ℝ} (ht : 0 ≤ t) (htM : t * M ≤ c * δ) :
    Real.log (∫ ω, Real.exp (t *
      ∑ i ∈ cantorBlock (cantorLength δ n) 0 a d, X i ω) ∂μ) ≤
      cantorLeafLog μ X (cantorLength δ n) 0 a t d +
        ∑ k ∈ Finset.range d, (2 : ℝ) ^ k *
          Real.exp (-c * δ * cantorLength δ n k) := by
  have hb := cantor_log_laplace_le μ X hX hcenter hM hbound
    (cantorLength δ n) (cantorLength_fit δ n) 0 a t d
  simp only [Nat.zero_add] at hb
  refine hb.trans (add_le_add le_rfl (Finset.sum_le_sum (fun k _ => ?_)))
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)
  let gap := cantorLength δ n k - 2 * cantorLength δ n (k + 1) + 1
  have hgap1 : 1 ≤ gap := by dsimp [gap]; omega
  have hg0 := cantorNext_gap hδ1 (cantorLength δ n k)
  change δ * (cantorLength δ n k : ℝ) ≤
    ((cantorLength δ n k - 2 * cantorLength δ n (k + 1) : ℕ) : ℝ) at hg0
  have hg : δ * (cantorLength δ n k : ℝ) ≤ (gap : ℝ) := by
    dsimp [gap]
    push_cast
    linarith
  have hfit : 2 * (cantorLength δ n (k + 1) : ℝ) ≤ cantorLength δ n k := by
    exact_mod_cast cantorLength_fit δ n k
  have hchild := mul_le_mul_of_nonneg_left hfit (mul_nonneg ht hM)
  have hgap := mul_le_mul_of_nonneg_left hg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc)
  have hlevel := mul_le_mul_of_nonneg_right htM
    (Nat.cast_nonneg (cantorLength δ n k) : 0 ≤ (cantorLength δ n k : ℝ))
  calc
    _ ≤ Real.exp (2 * |t| * M * cantorLength δ n (k + 1)) *
        Real.exp (-2 * c * gap) :=
      mul_le_mul_of_nonneg_left (hmix gap hgap1) (Real.exp_nonneg _)
    _ = Real.exp (2 * t * M * cantorLength δ n (k + 1) - 2 * c * gap) := by
      rw [abs_of_nonneg ht, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-c * δ * cantorLength δ n k) := by
      apply Real.exp_le_exp.mpr
      nlinarith

end StrongMixing
