import SchubertForwardStability.StrongMixing.Inequalities.Laplace.DyadicLaplace

/-!
# Finite-depth dyadic log-Laplace decoupling

This version only requires the binary decomposition and child bounds at the levels
strictly below the chosen depth. Centering is needed only at levels through that depth.
No infinitely continued decomposition is imposed on terminal finite blocks.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A centered binary block decomposition through a specified finite depth satisfies
the sum-of-terminal-log-Laplace estimate with the sum of every internal-node mixing
error. Bounds, measurability and split equalities are needed only at the levels of
the finite decomposition. -/
theorem finite_dyadic_log_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (depth : ℕ) (Z : ℕ → ℕ → Ω → ℝ) (F G : ℕ → ℕ → MeasurableSpace Ω)
    (hF : ∀ j i, j < depth → F j i ≤ mΩ)
    (hG : ∀ j i, j < depth → G j i ≤ mΩ)
    (hleft : ∀ j i, j < depth →
      @Measurable Ω ℝ (F j i) _ (Z (j + 1) (2 * i)))
    (hright : ∀ j i, j < depth →
      @Measurable Ω ℝ (G j i) _ (Z (j + 1) (2 * i + 1)))
    (M N : ℕ → ℕ → ℝ)
    (hbLeft : ∀ j i, j < depth → ∀ ω, |Z (j + 1) (2 * i) ω| ≤ M j i)
    (hbRight : ∀ j i, j < depth → ∀ ω, |Z (j + 1) (2 * i + 1) ω| ≤ N j i)
    (hcenter : ∀ j i, j ≤ depth → ∫ ω, Z j i ω ∂μ = 0)
    (hsplit : ∀ j i, j < depth → ∀ ω,
      Z j i ω = Z (j + 1) (2 * i) ω + Z (j + 1) (2 * i + 1) ω) (t : ℝ) :
    Real.log (∫ ω, Real.exp (t * Z 0 0 ω) ∂μ) ≤
      (∑ i ∈ Finset.range (2 ^ depth),
        Real.log (∫ ω, Real.exp (t * Z depth i ω) ∂μ)) +
      ∑ j ∈ Finset.range depth, ∑ i ∈ Finset.range (2 ^ j),
        Real.exp (|t| * (M j i + N j i)) *
          strongMixingCoeff (mΩ := mΩ) μ (F j i) (G j i) := by
  let L : ℕ → ℕ → ℝ := fun j i => Real.log (∫ ω, Real.exp (t * Z j i ω) ∂μ)
  let E : ℕ → ℕ → ℝ := fun j i =>
    Real.exp (|t| * (M j i + N j i)) *
      strongMixingCoeff (mΩ := mΩ) μ (F j i) (G j i)
  let S : ℕ → ℝ := fun j => ∑ i ∈ Finset.range (2 ^ j), L j i
  let T : ℕ → ℝ := fun j => ∑ i ∈ Finset.range (2 ^ j), E j i
  have hlocal : ∀ j i, j < depth →
      L j i ≤ L (j + 1) (2 * i) + L (j + 1) (2 * i + 1) + E j i := by
    intro j i hj
    have heq : Z j i = fun ω => Z (j + 1) (2 * i) ω + Z (j + 1) (2 * i + 1) ω :=
      funext (hsplit j i hj)
    simpa only [L, E, heq] using log_laplace_product_error_le μ (F j i) (G j i)
      (hF j i hj) (hG j i hj) (Z (j + 1) (2 * i)) (Z (j + 1) (2 * i + 1))
      (hleft j i hj) (hright j i hj) (hbLeft j i hj) (hbRight j i hj)
      (hcenter (j + 1) (2 * i) (by omega))
      (hcenter (j + 1) (2 * i + 1) (by omega)) t
  have hsum : ∀ j, j < depth → S j ≤ S (j + 1) + T j := by
    intro j hj
    have hs := Finset.sum_le_sum (s := Finset.range (2 ^ j))
      (fun i _ => hlocal j i hj)
    rw [Finset.sum_add_distrib, sum_range_pairs] at hs
    simpa only [S, T, pow_succ, Nat.mul_comm] using hs
  have hiter : ∀ d, d ≤ depth → L 0 0 ≤ S d + ∑ j ∈ Finset.range d, T j := by
    intro d
    induction d with
    | zero => intro _; simp [S]
    | succ d ih =>
      intro hd
      refine (ih (by omega)).trans ((add_le_add (hsum d (by omega)) le_rfl).trans_eq ?_)
      rw [Finset.sum_range_succ]
      ring
  exact hiter depth le_rfl

end StrongMixing
