import SchubertForwardStability.StrongMixing.Inequalities.IntervalLaplace
import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorGeometric

/-!
# Quadratic terminal bounds for Cantor log-Laplace transforms

Every terminal interval has the same scheduled length. The short-interval
bound controls the terminal-transform sum by the retained cardinality, and is
combined with the explicit dyadic geometric-mixing errors.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For a centered sequence with exponential mixing and `c > 0`, the
terminal log-Laplace sum at depth `d` is bounded by the quadratic interval constant
times `2^d * L (j+d)`. Only the terminal interval needs the small-parameter bound;
the schedule may have zero lengths and need not satisfy the child-fit condition. -/
theorem cantor_leaf_quadratic_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (L : ℕ → ℕ) (j : ℕ) (a : ℤ) (t : ℝ) (d : ℕ)
    (hsmall : |t| * L (j + d) * M ≤ 1) :
    cantorLeafLog μ X L j a t d ≤
      (2 : ℝ) ^ d * t ^ 2 * L (j + d) * M ^ 2 *
        (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) := by
  induction d generalizing j a with
  | zero =>
    simpa only [cantorLeafLog, Nat.add_zero, pow_zero, one_mul] using
      geometric_interval_laplace_le μ X hX hcenter hM hc hbound hmix a (L j) t
        (by simpa only [Nat.add_zero] using hsmall)
  | succ d ih =>
    have hid : j + 1 + d = j + (d + 1) := by omega
    have hs : |t| * L (j + 1 + d) * M ≤ 1 := by simpa only [hid] using hsmall
    rw [cantorLeafLog]
    calc
      _ ≤ (2 : ℝ) ^ d * t ^ 2 * L (j + 1 + d) * M ^ 2 *
            (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
          (2 : ℝ) ^ d * t ^ 2 * L (j + 1 + d) * M ^ 2 *
            (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) :=
        add_le_add (ih (j + 1) a hs) (ih (j + 1) (a + L j - L (j + 1)) hs)
      _ = _ := by rw [hid, pow_succ]; ring

/-- A rounded finite Cantor block has log-Laplace transform at most the full-length
quadratic bound plus its explicit dyadic geometric-mixing errors. The hypotheses
are the exponential lag bound, a sufficiently small terminal parameter,
and `t*M <= c*delta`. -/
theorem cantor_quadratic_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c δ : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hδ1 : δ ≤ 1)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (n d : ℕ) (a : ℤ) {t : ℝ} (ht : 0 ≤ t) (htM : t * M ≤ c * δ)
    (hsmall : t * cantorLength δ n d * M ≤ 1) :
    Real.log (∫ ω, Real.exp (t *
      ∑ i ∈ cantorBlock (cantorLength δ n) 0 a d, X i ω) ∂μ) ≤
      t ^ 2 * n * M ^ 2 *
          (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
        ∑ k ∈ Finset.range d, (2 : ℝ) ^ k *
          Real.exp (-c * δ * cantorLength δ n k) := by
  have hbase := cantor_geometric_laplace_le μ X hX hcenter hM hc.le hδ1 hbound
    hmix n d a ht htM
  have hterminal := cantor_leaf_quadratic_le μ X hX hcenter hM hc hbound hmix
    (cantorLength δ n) 0 a t d
    (by simpa only [Nat.zero_add, abs_of_nonneg ht] using hsmall)
  simp only [Nat.zero_add] at hterminal
  have hcard := cantorBlock_card_le (cantorLength δ n) (cantorLength_fit δ n) 0 a d
  rw [cantorBlock_card (cantorLength δ n) (cantorLength_fit δ n)] at hcard
  simp only [Nat.zero_add, cantorLength] at hcard
  have hcardR : (2 : ℝ) ^ d * cantorLength δ n d ≤ (n : ℝ) := by
    exact_mod_cast hcard
  have hratio : 0 ≤ 1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c)) := by
    have he : Real.exp (-2 * c) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    positivity
  have hterm : cantorLeafLog μ X (cantorLength δ n) 0 a t d ≤
      t ^ 2 * n * M ^ 2 *
        (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) := by
    refine hterminal.trans ?_
    have hs := mul_le_mul_of_nonneg_right hcardR
      (mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg M)) hratio)
    nlinarith only [hs]
  exact hbase.trans (add_le_add hterm le_rfl)

end StrongMixing
