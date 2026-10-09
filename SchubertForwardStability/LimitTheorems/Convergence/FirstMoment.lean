import SchubertForwardStability.LimitTheorems.Convergence.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Convergence in probability from vanishing first norm moments

By Markov's inequality, random variables on varying probability spaces whose expected norms
tend to zero converge to zero in probability.
-/

namespace LimitTheorems

open MeasureTheory Filter
open scoped Topology

/-- Vanishing integrals of norms imply convergence in probability on varying spaces. -/
theorem tendstoInProbability_of_integral_norm
    {ι E : Type*} {Ω : ι → Type*} [SeminormedAddCommGroup E]
    [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)}
    [∀ i, IsFiniteMeasure (μ i)] {X : ∀ i, Ω i → E} {l : Filter ι}
    (hX : ∀ i, Integrable (fun ω => ‖X i ω‖) (μ i))
    (hlim : Tendsto (fun i => ∫ ω, ‖X i ω‖ ∂μ i) l (𝓝 0)) :
    TendstoInProbability X l 0 μ := by
  intro ε hε
  have hbound (i : ι) : (μ i).real {ω | ε < ‖X i ω‖} ≤
      (∫ ω, ‖X i ω‖ ∂μ i) / ε := by
    have hm : (μ i).real {ω | ε < ‖X i ω‖} ≤ (μ i).real {ω | ε ≤ ‖X i ω‖} :=
      measureReal_mono (by
        intro ω h
        change ε < ‖X i ω‖ at h
        change ε ≤ ‖X i ω‖
        exact h.le) (measure_ne_top _ _)
    have hi := mul_meas_ge_le_integral_of_nonneg
      (ae_of_all (μ i) (fun ω => norm_nonneg (X i ω))) (hX i) ε
    apply (le_div_iff₀ hε).mpr
    calc
      _ = ε * (μ i).real {ω | ε < ‖X i ω‖} := mul_comm _ _
      _ ≤ ε * (μ i).real {ω | ε ≤ ‖X i ω‖} :=
        mul_le_mul_of_nonneg_left hm hε.le
      _ ≤ _ := hi
  simp only [sub_zero]
  apply squeeze_zero (fun _ => measureReal_nonneg) hbound
  simpa only [zero_div] using hlim.div_const ε

end LimitTheorems
