import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorGeometric

/-!
# Explicit geometric Cantor error bounds

The rounded gaps yield a levelwise exponential decay bound. A common
lower bound on all lengths above the stopping depth then controls the accumulated
dyadic error by a closed finite geometric-power sum.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- At a rounded Cantor level, the exponential covariance error is at most
`exp(-c*delta*L k)` when `t*M <= c*delta`, `t,M,c >= 0`, and `delta <= 1`.
The mixing hypothesis is the lag coefficient bound at every positive lag, and the
natural gap is computed from the rounded lengths. -/
theorem rounded_cantor_error_le (μ : Measure Ω)
    (X : ℤ → Ω → ℝ) {M c δ t : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hδ1 : δ ≤ 1)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (n k : ℕ) (ht : 0 ≤ t) (htM : t * M ≤ c * δ) :
    Real.exp (2 * |t| * M * cantorLength δ n (k + 1)) *
        mixingCoeff μ X
          (cantorLength δ n k - 2 * cantorLength δ n (k + 1) + 1) ≤
      Real.exp (-c * δ * cantorLength δ n k) := by
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

/-- The finite sum of powers of two from exponent zero through `d-1` is
`2^d-1`, as an identity of real numbers. The empty-range boundary is included. -/
theorem sum_two_pow_eq (d : ℕ) : (∑ k ∈ Finset.range d, (2 : ℝ) ^ k) = 2 ^ d - 1 := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- If every length above the stopping depth is at least `B`, the full rounded
Cantor dyadic covariance error is at most `(2^d-1)*exp(-c*delta*B)` under the
exponential coefficient bound. The bound applies to any finite stopping
depth, including zero, and retains the exact multiplicity factor. -/
theorem cantor_error_sum_le (μ : Measure Ω)
    (X : ℤ → Ω → ℝ) {M c δ t B : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (n d : ℕ) (ht : 0 ≤ t) (htM : t * M ≤ c * δ)
    (hlevels : ∀ k : ℕ, k < d → B ≤ cantorLength δ n k) :
    (∑ k ∈ Finset.range d, (2 : ℝ) ^ k *
        (Real.exp (2 * |t| * M * cantorLength δ n (k + 1)) *
          mixingCoeff μ X
            (cantorLength δ n k - 2 * cantorLength δ n (k + 1) + 1))) ≤
      (2 ^ d - 1) * Real.exp (-c * δ * B) := by
  calc
    _ ≤ ∑ k ∈ Finset.range d, (2 : ℝ) ^ k * Real.exp (-c * δ * B) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)
      refine (rounded_cantor_error_le μ X hM hc hδ1 hmix n k ht htM).trans ?_
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (hlevels k (Finset.mem_range.mp hk))
        (mul_nonneg hc hδ0)
      nlinarith only [h]
    _ = _ := by rw [← Finset.sum_mul, sum_two_pow_eq]

end StrongMixing
