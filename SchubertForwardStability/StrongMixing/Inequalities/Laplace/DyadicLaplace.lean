import SchubertForwardStability.StrongMixing.Inequalities.Laplace.LaplaceLogs

/-!
# Dyadic log-Laplace decoupling

For a binary decomposition of centered block random variables, this module
iterates the two-field logarithmic covariance bound through every level.
The final error is the explicit sum of the mixing errors at all internal nodes.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

/-- Summing paired consecutive indices over `range n` gives the same real sum as
summing all `2 * n` indices. This is the dyadic level-reindexing identity. -/
theorem sum_range_pairs (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1))) =
      ∑ i ∈ Finset.range (2 * n), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [Finset.sum_range_succ, ih, hid, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A binary tree of centered bounded block random variables satisfies an
iterated log-Laplace bound. At each node the two child blocks are measurable in
their sigma fields, and the error at each node is controlled by the strong-mixing
coefficient of those fields. The only decomposition hypothesis is that each node is the
sum of its children. -/
theorem dyadic_log_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → ℕ → Ω → ℝ) (F G : ℕ → ℕ → MeasurableSpace Ω)
    (hF : ∀ j i, F j i ≤ mΩ) (hG : ∀ j i, G j i ≤ mΩ)
    (hleft : ∀ j i, @Measurable Ω ℝ (F j i) _ (Z (j + 1) (2 * i)))
    (hright : ∀ j i, @Measurable Ω ℝ (G j i) _ (Z (j + 1) (2 * i + 1)))
    (M N : ℕ → ℕ → ℝ)
    (hbLeft : ∀ j i ω, |Z (j + 1) (2 * i) ω| ≤ M j i)
    (hbRight : ∀ j i ω, |Z (j + 1) (2 * i + 1) ω| ≤ N j i)
    (hcenter : ∀ j i, ∫ ω, Z j i ω ∂μ = 0)
    (hsplit : ∀ j i ω, Z j i ω = Z (j + 1) (2 * i) ω + Z (j + 1) (2 * i + 1) ω)
    (t : ℝ) (depth : ℕ) :
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
  have hlocal : ∀ j i, L j i ≤ L (j + 1) (2 * i) + L (j + 1) (2 * i + 1) + E j i := by
    intro j i
    have heq : Z j i = fun ω => Z (j + 1) (2 * i) ω + Z (j + 1) (2 * i + 1) ω :=
      funext (hsplit j i)
    simpa only [L, E, heq] using log_laplace_product_error_le μ (F j i) (G j i)
      (hF j i) (hG j i) (Z (j + 1) (2 * i)) (Z (j + 1) (2 * i + 1))
      (hleft j i) (hright j i) (hbLeft j i) (hbRight j i)
      (hcenter (j + 1) (2 * i)) (hcenter (j + 1) (2 * i + 1)) t
  have hsum : ∀ j, S j ≤ S (j + 1) + T j := by
    intro j
    have hs := Finset.sum_le_sum (s := Finset.range (2 ^ j)) (fun i _ => hlocal j i)
    rw [Finset.sum_add_distrib, sum_range_pairs] at hs
    simpa only [S, T, pow_succ, Nat.mul_comm] using hs
  have hiter : ∀ d, L 0 0 ≤ S d + ∑ j ∈ Finset.range d, T j := by
    intro d
    induction d with
    | zero => simp [S]
    | succ d ih =>
      refine ih.trans ((add_le_add (hsum d) le_rfl).trans_eq ?_)
      rw [Finset.sum_range_succ]
      ring
  exact hiter depth

end StrongMixing
