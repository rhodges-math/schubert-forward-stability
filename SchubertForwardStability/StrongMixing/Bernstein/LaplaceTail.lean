import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Optimization of a quadratic log-Laplace bound

## Main results

* `measure_ge_of_log_laplace`: a quadratic log-Laplace bound gives a one-sided Bernstein tail.

The hypothesis is a quadratic bound on the log-Laplace transform of a single random
variable.
-/

open MeasureTheory ProbabilityTheory

namespace StrongMixing

/-- A log-Laplace bound `A t² / (1 - B t)` gives the one-sided tail
`exp(-x² / (4 A + 2 B x))` for every nonnegative threshold. -/
theorem measure_ge_of_log_laplace {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hLaplace : ∀ t : ℝ, 0 ≤ t → B * t < 1 →
      Integrable (fun ω ↦ Real.exp (t * X ω)) μ ∧
        Real.log (∫ ω, Real.exp (t * X ω) ∂μ) ≤ A * t ^ 2 / (1 - B * t))
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | x ≤ X ω} ≤ Real.exp (-x ^ 2 / (4 * A + 2 * B * x)) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  let D := 2 * A + B * x
  have hD : 0 < D := by dsimp [D]; positivity
  let t := x / D
  have ht : 0 < t := div_pos hx hD
  have hBt : B * t < 1 := by
    dsimp [t]
    rw [← mul_div_assoc, div_lt_one hD]
    dsimp [D]
    linarith
  obtain ⟨hint, hbound⟩ := hLaplace t ht.le hBt
  have hfrac : 1 - B * t = 2 * A / D := by
    dsimp [t]
    field_simp [hD.ne']
    dsimp [D]
    ring
  have hfinal : 0 < 4 * A + 2 * B * x := by positivity
  have heq : -t * x + A * t ^ 2 / (1 - B * t) = -x ^ 2 / (4 * A + 2 * B * x) := by
    rw [hfrac]
    dsimp [t]
    field_simp [hD.ne', hA.ne', hfinal.ne']
    dsimp [D]
    ring
  calc
    μ.real {ω | x ≤ X ω} ≤ Real.exp (-t * x + cgf X μ t) :=
      measure_ge_le_exp_cgf x ht.le hint
    _ ≤ Real.exp (-t * x + A * t ^ 2 / (1 - B * t)) := by
      apply Real.exp_le_exp.mpr
      simp only [cgf, mgf]
      linarith
    _ = Real.exp (-x ^ 2 / (4 * A + 2 * B * x)) := congrArg Real.exp heq

end StrongMixing
