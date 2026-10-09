import SchubertForwardStability.LimitTheorems.Convergence.LawChange
import SchubertForwardStability.LimitTheorems.TotalVariation.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.Asymptotics.Defs

/-! # Transfers along equal laws and small total variation

## Main results

* `tendstoInDistribution_of_identDistrib`: row-wise equality in law transports
  convergence in distribution.
* `tendsto_integral_of_identDistrib`, `isBigO_integral_of_identDistrib`: row-wise equality
  in law transports centered expectation limits and bounds.
* The primed versions need equality in law only for all large indices.
* `abs_measureReal_sub_le_totalVariation`: total variation bounds every event
  discrepancy of two probability laws on an arbitrary measurable space.

## Implementation notes

The row carriers may vary with the index. No finiteness of the carrier is needed for the
event bound, since every event discrepancy of two probability laws is at most one.
-/

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology

namespace LimitTheorems

/-- Row-wise equality in law transports convergence in distribution to the same limit. -/
theorem tendstoInDistribution_of_identDistrib
    {ι E Ω' : Type*} {Ω Γ : ι → Type*}
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (Γ i)] [MeasurableSpace Ω']
    {μ : ∀ i, Measure (Ω i)} {ν : ∀ i, Measure (Γ i)}
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {X : ∀ i, Ω i → E} {Y : ∀ i, Γ i → E} {Z : Ω' → E} {l : Filter ι}
    (h : TendstoInDistribution X l Z μ μ')
    (hXY : ∀ i, IdentDistrib (X i) (Y i) (μ i) (ν i)) :
    TendstoInDistribution Y l Z ν μ' :=
  tendstoInDistribution_law_congr h (fun i => (hXY i).aemeasurable_snd)
    h.aemeasurable_limit (fun i => (hXY i).map_eq.symm) rfl

/-- Row-wise equality in law transports a centered limit of real expectations. -/
theorem tendsto_integral_of_identDistrib
    {ι : Type*} {Ω Γ : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (Γ i)]
    {μ : ∀ i, Measure (Ω i)} {ν : ∀ i, Measure (Γ i)}
    {X : ∀ i, Ω i → ℝ} {Y : ∀ i, Γ i → ℝ} {a : ι → ℝ} {c : ℝ} {l : Filter ι}
    (h : Tendsto (fun i => (∫ ω, X i ω ∂μ i) - a i) l (𝓝 c))
    (hXY : ∀ i, IdentDistrib (X i) (Y i) (μ i) (ν i)) :
    Tendsto (fun i => (∫ ω, Y i ω ∂ν i) - a i) l (𝓝 c) := by
  refine h.congr fun i => ?_
  rw [(hXY i).integral_eq]

/-- Row-wise equality in law transports an asymptotic bound on centered real expectations. -/
theorem isBigO_integral_of_identDistrib
    {ι F : Type*} [Norm F] {Ω Γ : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSpace (Γ i)] {μ : ∀ i, Measure (Ω i)} {ν : ∀ i, Measure (Γ i)}
    {X : ∀ i, Ω i → ℝ} {Y : ∀ i, Γ i → ℝ} {a : ι → ℝ} {g : ι → F} {l : Filter ι}
    (h : (fun i => (∫ ω, X i ω ∂μ i) - a i) =O[l] g)
    (hXY : ∀ i, IdentDistrib (X i) (Y i) (μ i) (ν i)) :
    (fun i => (∫ ω, Y i ω ∂ν i) - a i) =O[l] g := by
  refine h.congr_left fun i => ?_
  rw [(hXY i).integral_eq]

/-- Equality in law for all large indices transports convergence in distribution to the same
limit. -/
theorem tendstoInDistribution_of_identDistrib'
    {ι E Ω' : Type*} {Ω Γ : ι → Type*}
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (Γ i)] [MeasurableSpace Ω']
    {μ : ∀ i, Measure (Ω i)} {ν : ∀ i, Measure (Γ i)}
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {X : ∀ i, Ω i → E} {Y : ∀ i, Γ i → E} {Z : Ω' → E} {l : Filter ι}
    (h : TendstoInDistribution X l Z μ μ') (hY : ∀ i, AEMeasurable (Y i) (ν i))
    (hXY : ∀ᶠ i in l, IdentDistrib (X i) (Y i) (μ i) (ν i)) :
    TendstoInDistribution Y l Z ν μ' := by
  refine ⟨hY, h.aemeasurable_limit, h.tendsto.congr' ?_⟩
  filter_upwards [hXY] with i hi
  exact Subtype.ext hi.map_eq

/-- Equality in law for all large indices transports a centered limit of real expectations. -/
theorem tendsto_integral_of_identDistrib'
    {ι : Type*} {Ω Γ : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (Γ i)]
    {μ : ∀ i, Measure (Ω i)} {ν : ∀ i, Measure (Γ i)}
    {X : ∀ i, Ω i → ℝ} {Y : ∀ i, Γ i → ℝ} {a : ι → ℝ} {c : ℝ} {l : Filter ι}
    (h : Tendsto (fun i => (∫ ω, X i ω ∂μ i) - a i) l (𝓝 c))
    (hXY : ∀ᶠ i in l, IdentDistrib (X i) (Y i) (μ i) (ν i)) :
    Tendsto (fun i => (∫ ω, Y i ω ∂ν i) - a i) l (𝓝 c) := by
  refine h.congr' ?_
  filter_upwards [hXY] with i hi
  rw [hi.integral_eq]

/-- Equality in law for all large indices transports an asymptotic bound on centered real
expectations. -/
theorem isBigO_integral_of_identDistrib'
    {ι F : Type*} [Norm F] {Ω Γ : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSpace (Γ i)] {μ : ∀ i, Measure (Ω i)} {ν : ∀ i, Measure (Γ i)}
    {X : ∀ i, Ω i → ℝ} {Y : ∀ i, Γ i → ℝ} {a : ι → ℝ} {g : ι → F} {l : Filter ι}
    (h : (fun i => (∫ ω, X i ω ∂μ i) - a i) =O[l] g)
    (hXY : ∀ᶠ i in l, IdentDistrib (X i) (Y i) (μ i) (ν i)) :
    (fun i => (∫ ω, Y i ω ∂ν i) - a i) =O[l] g := by
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hXY] with i hi
  rw [hi.integral_eq]

/-- Total variation bounds each event discrepancy of two probability laws. -/
theorem abs_measureReal_sub_le_totalVariation {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (A : Set α) :
    |μ.real A - ν.real A| ≤ totalVariation μ ν := by
  have hb : BddAbove (Set.range fun B : Set α => |μ.real B - ν.real B|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨B, rfl⟩
    have hμ : μ.real B ≤ 1 := measureReal_le_one
    have hν : ν.real B ≤ 1 := measureReal_le_one
    have hμ' : 0 ≤ μ.real B := measureReal_nonneg
    have hν' : 0 ≤ ν.real B := measureReal_nonneg
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  exact le_ciSup hb A

end LimitTheorems
