import SchubertForwardStability.StrongMixing.Inequalities.TerminalSubset
import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorPartial

/-!
# Terminal subset estimates inside a fixed Cantor set

Partial-depth decoupling keeps the retained set fixed. The arbitrary-subset
terminal estimate controls its terminal transforms at interval scale
`1/(t*M)^2`, with an explicit exponentially small term.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- After `outer` splits of a fixed Cantor set with residual depth `inner`, its
terminal log-Laplace sum is bounded by the common terminal interval length times
the quadratic and exponentially small coefficients. The terminal size
condition is `(t*M)^2*L(j+outer) <= c/24`. -/
theorem cantor_partial_terminal_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (L : ℕ → ℕ) (hL : ∀ j, 2 * L (j + 1) ≤ L j) (j : ℕ) (a : ℤ)
    (outer inner : ℕ) (ht : 0 < t) (hsmall : t * M ≤ 1 / 8)
    (hsize : (t * M) ^ 2 * L (j + outer) ≤ c / 24) :
    cantorPartialLog μ X L j a t inner outer ≤
      (2 : ℝ) ^ outer * L (j + outer) *
        (6 * (t * M) ^ 2 * (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
          16 * t * M * Real.exp (-c / (8 * t * M))) := by
  induction outer generalizing j a with
  | zero =>
    have h := terminal_subset_laplace_le μ X hX hcenter hM hc hbound hmix
      (cantorBlock L j a inner) a (L j) (cantorBlock_subset L hL j a inner) ht hsmall
      (by simpa only [Nat.add_zero] using hsize)
    simp only [cantorPartialLog, Nat.add_zero, pow_zero, one_mul]
    exact h.trans_eq (by ring)
  | succ d ih =>
    have hid : j + 1 + d = j + (d + 1) := by omega
    have hs : (t * M) ^ 2 * L (j + 1 + d) ≤ c / 24 := by
      simpa only [hid] using hsize
    rw [cantorPartialLog]
    have hA := ih (j + 1) a hs
    have hB := ih (j + 1) (a + L j - L (j + 1)) hs
    refine (add_le_add hA hB).trans_eq ?_
    rw [hid, pow_succ]
    ring

/-- A fixed Cantor block of depth `outer+inner` has a log-Laplace bound using the
full ambient length and the explicit outer-level mixing-error series. Its retained
set does not depend on the stopping parameter, and the size condition is needed only
at the chosen outer level. -/
theorem cantor_fixed_terminal_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (L : ℕ → ℕ) (hL : ∀ j, 2 * L (j + 1) ≤ L j) (j : ℕ) (a : ℤ)
    (outer inner : ℕ) (ht : 0 < t) (hsmall : t * M ≤ 1 / 8)
    (hsize : (t * M) ^ 2 * L (j + outer) ≤ c / 24) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ cantorBlock L j a (outer + inner), X i ω) ∂μ) ≤
      L j * (6 * (t * M) ^ 2 *
          (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
            16 * t * M * Real.exp (-c / (8 * t * M))) +
        ∑ k ∈ Finset.range outer, (2 : ℝ) ^ k *
          (Real.exp (2 * |t| * M * L (j + k + 1)) *
            mixingCoeff μ X (L (j + k) - 2 * L (j + k + 1) + 1)) := by
  have h := cantor_partial_laplace_le μ X hX hcenter hM.le hbound L hL j a t outer inner
  have hb := cantor_partial_terminal_le μ X hX hcenter hM hc hbound hmix L hL j a
    outer inner ht hsmall hsize
  have hcard := cantorBlock_card_le L hL j a outer
  rw [cantorBlock_card L hL j a outer] at hcard
  have hcR : (2 : ℝ) ^ outer * L (j + outer) ≤ L j := by exact_mod_cast hcard
  have hr1 : Real.exp (-2 * c) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hcoef : 0 ≤ 6 * (t * M) ^ 2 *
      (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
        16 * t * M * Real.exp (-c / (8 * t * M)) := by positivity
  exact h.trans (add_le_add (hb.trans
    (mul_le_mul_of_nonneg_right hcR hcoef)) le_rfl)

end StrongMixing
