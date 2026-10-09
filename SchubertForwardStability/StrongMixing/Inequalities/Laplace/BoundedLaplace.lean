import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-! # Elementary bounded-variable Laplace estimates

## Main results

* `integrable_exp_of_abs_le`: bounded random variables have integrable Laplace transforms.
* `integral_exp_centered_le`: the centered small-parameter transform has a quadratic bound.
* `log_integral_exp_centered_le`: its logarithm is bounded by the second moment.

These estimates are used in the proof of the strong-mixing Bernstein inequality.
-/

open MeasureTheory

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A real variable bounded in absolute value almost surely has an integrable exponential
at every real parameter under a finite measure. -/
theorem integrable_exp_of_abs_le [IsFiniteMeasure μ] {X : Ω → ℝ} {M : ℝ}
    (hX : AEMeasurable X μ) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ M) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) μ := by
  refine Integrable.of_bound (by fun_prop) (Real.exp (|t| * M)) ?_
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * X ω ≤ |t * X ω| := le_abs_self _
    _ = |t| * |X ω| := abs_mul _ _
    _ ≤ |t| * M := mul_le_mul_of_nonneg_left hω (abs_nonneg _)

/-- For a centered square-integrable variable and `|t X| ≤ 1` almost surely, the Laplace
transform is at most one plus `t²` times the second moment. -/
theorem integral_exp_centered_le [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hint : MemLp X 2 μ) (hmean : (∫ ω, X ω ∂μ) = 0) {t : ℝ}
    (hsmall : ∀ᵐ ω ∂μ, |t * X ω| ≤ 1) :
    (∫ ω, Real.exp (t * X ω) ∂μ) ≤ 1 + t ^ 2 * (∫ ω, (X ω) ^ 2 ∂μ) := by
  have hfirst := hint.integrable (by norm_num)
  have hsecond := (memLp_two_iff_integrable_sq hint.aestronglyMeasurable).mp hint
  have hexp : Integrable (fun ω ↦ Real.exp (t * X ω)) μ := by
    simpa using integrable_exp_of_abs_le (hint.aemeasurable.const_mul t) hsmall 1
  have hlin : Integrable (fun ω ↦ t * X ω) μ := hfirst.const_mul t
  have hsq : Integrable (fun ω ↦ t ^ 2 * (X ω) ^ 2) μ := hsecond.const_mul (t ^ 2)
  calc
    (∫ ω, Real.exp (t * X ω) ∂μ)
        ≤ ∫ ω, 1 + t * X ω + t ^ 2 * (X ω) ^ 2 ∂μ := by
      apply integral_mono_ae hexp (((integrable_const 1).add hlin).add hsq)
      filter_upwards [hsmall] with ω hω
      change Real.exp (t * X ω) ≤ 1 + t * X ω + t ^ 2 * (X ω) ^ 2
      have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hω)).2
      nlinarith
    _ = 1 + t ^ 2 * (∫ ω, (X ω) ^ 2 ∂μ) := by
      rw [integral_add (f := fun ω ↦ 1 + t * X ω) (g := fun ω ↦ t ^ 2 * (X ω) ^ 2)
          ((integrable_const 1).add hlin) hsq,
        integral_add (f := fun _ ↦ 1) (g := fun ω ↦ t * X ω)
          (integrable_const 1) hlin, integral_const,
        integral_const_mul, integral_const_mul, hmean]
      simp

/-- Under the centered small-parameter hypotheses, the log Laplace transform is at most
`t²` times the second moment. -/
theorem log_integral_exp_centered_le [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hint : MemLp X 2 μ) (hmean : (∫ ω, X ω ∂μ) = 0) {t : ℝ}
    (hsmall : ∀ᵐ ω ∂μ, |t * X ω| ≤ 1) :
    Real.log (∫ ω, Real.exp (t * X ω) ∂μ) ≤ t ^ 2 * (∫ ω, (X ω) ^ 2 ∂μ) := by
  have hexp : Integrable (fun ω ↦ Real.exp (t * X ω)) μ := by
    simpa using integrable_exp_of_abs_le (hint.aemeasurable.const_mul t) hsmall 1
  have hlog := Real.log_le_sub_one_of_pos (integral_exp_pos hexp)
  have hupper := integral_exp_centered_le hint hmean hsmall
  linarith

end StrongMixing
