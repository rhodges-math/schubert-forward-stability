import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Convergence in probability on varying spaces

## Main definitions

* `TendstoInProbability`: convergence in probability to a constant for varying source spaces.

## Implementation notes

The event threshold is strict. Positive weak thresholds give the same convergence
by bounding each weak-threshold event with a smaller strict-threshold event.
-/

open MeasureTheory Filter
open scoped Topology

namespace LimitTheorems

variable {ι E : Type*} {Ω : ι → Type*} [SeminormedAddCommGroup E]
  [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
  {X : (i : ι) → Ω i → E} {l : Filter ι} {c : E}

/-- Convergence in probability to a constant, allowing a different source space at each index. -/
def TendstoInProbability (X : (i : ι) → Ω i → E) (l : Filter ι) (c : E)
    (μ : (i : ι) → Measure (Ω i)) : Prop :=
  ∀ ε > 0, Tendsto (fun i ↦ (μ i).real {ω | ε < ‖X i ω - c‖}) l (𝓝 0)

/-- Positive weak-threshold events vanish under convergence in probability. -/
theorem TendstoInProbability.measure_ge [∀ i, IsFiniteMeasure (μ i)]
    (h : TendstoInProbability X l c μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun i ↦ (μ i).real {ω | ε ≤ ‖X i ω - c‖}) l (𝓝 0) := by
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun i ↦ ?_) (h (ε / 2) (by positivity))
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  exact (half_lt_self hε).trans_le hω

/-- Strict and weak positive event thresholds define the same convergence. -/
theorem tendstoInProbability_iff_ge [∀ i, IsFiniteMeasure (μ i)] :
    TendstoInProbability X l c μ ↔
      ∀ ε > 0, Tendsto (fun i ↦ (μ i).real {ω | ε ≤ ‖X i ω - c‖}) l (𝓝 0) := by
  constructor
  · exact fun h ε hε ↦ h.measure_ge hε
  · intro h ε hε
    refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun i ↦ ?_) (h ε hε)
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    exact (show ε < ‖X i ω - c‖ from hω).le

/-- Constant random variables converge in probability to their value. -/
theorem tendstoInProbability_const :
    TendstoInProbability (fun i (_ : Ω i) ↦ c) l c μ := by
  intro ε hε
  simpa [not_lt.mpr hε.le] using (tendsto_const_nhds :
    Tendsto (fun _ : ι ↦ (0 : ℝ)) l (𝓝 0))

/-- The zero constant can be removed from the deviation expression. -/
theorem tendstoInProbability_zero :
    TendstoInProbability X l 0 μ ↔
      ∀ ε > 0, Tendsto (fun i ↦ (μ i).real {ω | ε < ‖X i ω‖}) l (𝓝 0) := by
  simp only [TendstoInProbability, sub_zero]

/-- Convergence to a constant is convergence of the centered variables to zero. -/
theorem tendstoInProbability_sub_const :
    TendstoInProbability (fun i ω ↦ X i ω - c) l 0 μ ↔
      TendstoInProbability X l c μ := by
  simp only [TendstoInProbability, sub_zero]

/-- Adding a zero coordinate preserves convergence in probability to zero. -/
theorem TendstoInProbability.prod_zero {E' : Type*} [SeminormedAddCommGroup E']
    {X : (i : ι) → Ω i → E'} (h : TendstoInProbability X l 0 μ) :
    TendstoInProbability (fun i ω ↦ ((0 : E), X i ω)) l 0 μ := by
  simpa only [TendstoInProbability, sub_zero, Prod.norm_def, norm_zero,
    max_eq_right (norm_nonneg _)] using h

end LimitTheorems
