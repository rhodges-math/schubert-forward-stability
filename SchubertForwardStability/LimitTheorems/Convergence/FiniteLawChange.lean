import SchubertForwardStability.LimitTheorems.TotalVariation.Support
import SchubertForwardStability.LimitTheorems.Convergence.Slutsky
import SchubertForwardStability.LimitTheorems.Convergence.LawChange

/-! # Weak limits under finite-supported law changes

Maximal couplings turn vanishing total variation into a perturbation that
vanishes in probability. Distributional convergence therefore transports
between probability laws on the same finite row supports.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

namespace LimitTheorems

/-- An observable difference event is bounded by the maximal-coupling mismatch. -/
theorem coupled_observable_tail_le_tv {α E : Type*}
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
    [SeminormedAddCommGroup E] (s : Finset α) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ a ∂μ, a ∈ s) (hν : ∀ᵐ a ∂ν, a ∈ s)
    (X : α → E) {ε : ℝ} (hε : 0 < ε) :
    (supportedCoupling s μ ν).real {p | ε < ‖X p.2 - X p.1‖} ≤
      totalVariation μ ν := by
  let := isProbabilityMeasure_supportedCoupling s μ ν hμ hν
  rw [←supportedCoupling_mismatch s μ ν hμ hν]
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro p hp he
  change ε < ‖X p.2 - X p.1‖ at hp
  rw [he, sub_self, norm_zero] at hp
  exact (not_lt_of_ge hε.le) hp

/-- Vanishing total variation preserves a common observable's distributional limit. -/
theorem tendstoInDistribution_finite_tv
    {ι E Ω' : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, DiscreteMeasurableSpace (Ω i)]
    [∀ i, Countable (Ω i)] [MeasurableSpace Ω']
    [MeasurableSpace E] [SeminormedAddCommGroup E]
    [SecondCountableTopology E] [BorelSpace E]
    {μ ν : ∀ i, Measure (Ω i)} {μ' : Measure Ω'}
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    [IsProbabilityMeasure μ'] {X : ∀ i, Ω i → E} {Z : Ω' → E}
    {l : Filter ι} [l.IsCountablyGenerated] (s : ∀ i, Finset (Ω i))
    (hμ : ∀ i, ∀ᵐ a ∂μ i, a ∈ s i) (hν : ∀ i, ∀ᵐ a ∂ν i, a ∈ s i)
    (hTV : Tendsto (fun i => totalVariation (μ i) (ν i)) l (𝓝 0))
    (hX : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution X l Z ν μ' := by
  let ρ (i : ι) := supportedCoupling (s i) (μ i) (ν i)
  let : ∀ i, IsProbabilityMeasure (ρ i) :=
    fun i => isProbabilityMeasure_supportedCoupling (s i) (μ i) (ν i) (hμ i) (hν i)
  have hf (i : ι) : (ρ i).map (fun p : Ω i × Ω i => X i p.1) = (μ i).map (X i) := by
    change (supportedCoupling (s i) (μ i) (ν i)).map (X i ∘ Prod.fst) = _
    rw [←Measure.map_map (by fun_prop) measurable_fst,
      supportedCoupling_fst (s i) (μ i) (ν i) (hμ i) (hν i)]
  have hs (i : ι) : (ρ i).map (fun p : Ω i × Ω i => X i p.2) = (ν i).map (X i) := by
    change (supportedCoupling (s i) (μ i) (ν i)).map (X i ∘ Prod.snd) = _
    rw [←Measure.map_map (by fun_prop) measurable_snd,
      supportedCoupling_snd (s i) (μ i) (ν i) (hμ i) (hν i)]
  have hfst := tendstoInDistribution_law_congr hX
    (Y := fun (i : ι) (p : Ω i × Ω i) => X i p.1) (ν := ρ)
    (fun _ => by fun_prop) hX.aemeasurable_limit hf rfl
  have hdiff : TendstoInProbability
      (fun (i : ι) (p : Ω i × Ω i) => X i p.2 - X i p.1) l 0 ρ := by
    intro ε hε
    simp only [sub_zero]
    apply squeeze_zero (fun _ => measureReal_nonneg)
      (fun i => coupled_observable_tail_le_tv (s i) (μ i) (ν i) (hμ i) (hν i) (X i) hε)
      hTV
  have hsnd := tendstoInDistribution_of_sub hfst hdiff
    (Y := fun (i : ι) (p : Ω i × Ω i) => X i p.2) (fun _ => by fun_prop)
  exact tendstoInDistribution_law_congr hsnd (fun _ => by fun_prop)
    hX.aemeasurable_limit (fun i => (hs i).symm) rfl

end LimitTheorems
