import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Two-state contraction against future events

Normalized two-state rows act on a unit-valued future-event probability function.
Their difference is controlled by the difference of a single coordinate. Finite
convex mixtures remain within the oscillation of their summands.
-/

open scoped BigOperators

namespace StrongMixing

/-- The difference of expectations under normalized two-state rows factors into
the first-coordinate row difference and the test-function difference. -/
theorem binary_expectation_difference (p q f : Bool → ℝ)
    (hp : ∑ b, p b = 1) (hq : ∑ b, q b = 1) :
    (∑ b, p b * f b) - (∑ b, q b * f b) =
      (p false - q false) * (f false - f true) := by
  have hp' : p true = 1 - p false := by
    simp only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
      Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton] at hp
    linarith
  have hq' : q true = 1 - q false := by
    simp only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
      Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton] at hq
    linarith
  simp only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton, hp', hq']
  ring

/-- A future-event probability taking values in the unit interval cannot increase
the distance between normalized two-state rows. -/
theorem binary_expectation_contract (p q f : Bool → ℝ)
    (hp : ∑ b, p b = 1) (hq : ∑ b, q b = 1)
    (hf : ∀ b, 0 ≤ f b ∧ f b ≤ 1) :
    |(∑ b, p b * f b) - (∑ b, q b * f b)| ≤ |p false - q false| := by
  rw [binary_expectation_difference p q f hp hq, abs_mul]
  have hd : |f false - f true| ≤ 1 := by
    exact abs_le.mpr ⟨by linarith [(hf false).1, (hf true).2],
      by linarith [(hf true).1, (hf false).2]⟩
  simpa using mul_le_mul_of_nonneg_left hd (abs_nonneg (p false - q false))

/-- A finite probability mixture differs from any one summand by at most a uniform
pairwise oscillation bound for the summands. -/
theorem probability_mean_oscillation {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (L : ℝ)
    (hf : ∀ i j, |f i - f j| ≤ L) (i : ι) :
    |f i - ∑ j, p j * f j| ≤ L := by
  have he : f i - ∑ j, p j * f j = ∑ j, p j * (f i - f j) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
  rw [he]
  calc
    _ ≤ ∑ j, |p j * (f i - f j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, p j * L := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hp j)]
      exact mul_le_mul_of_nonneg_left (hf i j) (hp j)
    _ = L := by rw [← Finset.sum_mul, hs, one_mul]

end StrongMixing
