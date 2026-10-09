import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorStopped
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.InverseExponential

/-!
# Quadratic Laplace bounds on retained Cantor sets

The inverse-exponential estimate absorbs the stopping error
into a constant depending only on the geometric mixing rate.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A prescribed-depth retained Cantor set has log-Laplace transform at most
`n*(t*M)^2*(6*K_c+384/c^2)` under the geometric-mixing hypotheses,
`0<t*M<=1/8`, `t*M<=c*delta/3`, terminal interval smallness, and `2^N<=n`.
The quadratic coefficient depends only on the positive mixing rate `c`. -/
theorem cantor_stopped_quadratic_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c δ t : ℝ}
    (hM : 0 < M) (hc : 0 < c) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (n N : ℕ) (a : ℤ) (ht : 0 < t) (hsmall : t * M ≤ 1 / 8)
    (hfinal : (t * M) ^ 2 * cantorLength δ n N ≤ c / 24)
    (hpow : (2 : ℝ) ^ N ≤ n) (hsep : t * M ≤ c * δ / 3) :
    Real.log (∫ ω, Real.exp
        (t * ∑ i ∈ cantorBlock (cantorLength δ n) 0 a N, X i ω) ∂μ) ≤
      n * (t * M) ^ 2 *
        (6 * (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) + 384 / c ^ 2) := by
  have h := cantor_stopped_depth_le μ X hX hcenter hM hc hδ0 hδ1 hbound hmix
    n N a ht hsmall hfinal hpow hsep
  have he := exp_inverse_sq_le (show 0 < c / 8 by positivity) (mul_pos ht hM)
  have hn : 0 ≤ (3 : ℝ) * n := by positivity
  have hs : 2 * (t * M) ^ 2 / (c / 8) ^ 2 = 128 * (t * M) ^ 2 / c ^ 2 := by
    field_simp
    ring
  rw [hs] at he
  have he' : Real.exp (-c / (8 * t * M)) ≤ 128 * (t * M) ^ 2 / c ^ 2 := by
    convert he using 1
    field_simp
  refine h.trans ((add_le_add le_rfl (mul_le_mul_of_nonneg_left he' hn)).trans_eq ?_)
  ring

/-- The fixed-depth Cantor set has a pure quadratic log-Laplace estimate with
coefficient `6*K_c+384/c^2` when `n >= 8`, `0<t*M<=1/8`, `(t*M)^2<=c/384`,
and `t*M<=c*delta/3`. Its definition is independent of `t`; half-retention is
available under the separate depth-times-deletion-fraction condition. -/
theorem cantor_fixed_quadratic_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c δ t : ℝ}
    (hM : 0 < M) (hc : 0 < c) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (n : ℕ) (hn : 8 ≤ n) (a : ℤ) (ht : 0 < t) (hsmall : t * M ≤ 1 / 8)
    (hsquare : (t * M) ^ 2 ≤ c / 384) (hsep : t * M ≤ c * δ / 3) :
    Real.log (∫ ω, Real.exp
        (t * ∑ i ∈ cantorBlock (cantorLength δ n) 0 a (fixedCantorDepth n), X i ω) ∂μ) ≤
      n * (t * M) ^ 2 *
        (6 * (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) + 384 / c ^ 2) := by
  apply cantor_stopped_quadratic_le μ X hX hcenter hM hc hδ0 hδ1 hbound hmix n
    (fixedCantorDepth n) a ht hsmall _ _ hsep
  · have hl : (cantorLength δ n (fixedCantorDepth n) : ℝ) ≤ 16 := by
      exact_mod_cast fixedCantorLength_le δ n
    have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg (t * M))
    nlinarith
  · have h := (fixedCantorDepth_pow_le n hn).trans (Nat.div_le_self n 8)
    exact_mod_cast h

end StrongMixing
