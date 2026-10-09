import SchubertForwardStability.LimitTheorems.Convergence.Probability

/-! # Deterministic convergence on varying probability spaces

## Main results

Every convergent deterministic sequence converges in probability on any family of
source measure spaces. No finite-measure or source measurability condition is needed.
-/

namespace LimitTheorems

open MeasureTheory Filter
open scoped Topology

/-- A convergent deterministic sequence is convergent in probability on any source spaces. -/
theorem tendstoInProbability_of_tendsto {ι E : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] [SeminormedAddCommGroup E]
    {μ : (i : ι) → Measure (Ω i)} {a : ι → E} {c : E} {l : Filter ι}
    (ha : Tendsto a l (𝓝 c)) :
    TendstoInProbability (fun i (_ : Ω i) => a i) l c μ := by
  have hnorm : Tendsto (fun i => ‖a i - c‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (ha.sub_const c).norm
  intro ε hε
  apply (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) l (𝓝 0)).congr'
  filter_upwards [hnorm.eventually_lt_const hε] with i hi
  have he : {ω : Ω i | ε < ‖a i - c‖} = ∅ := by
    simp only [not_lt.mpr hi.le, Set.ofPred_false]
  simp only [he, measureReal_empty]

end LimitTheorems
