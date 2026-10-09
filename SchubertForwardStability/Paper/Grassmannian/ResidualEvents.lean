import SchubertForwardStability.Paper.Grassmannian.Identity
import SchubertForwardStability.Permutations.Random.ExtremeTails

/-! # Rare events for the subset-pair residual

## Main results

A nonzero residual forces a large sampled cardinality or a small selected maximum
in one coordinate. The finite product law is concentrated on admissible encodings,
so its residual probability is bounded by four coordinate tails.
-/

open FinitaryPerm MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal

namespace RecordStability

/-- For any threshold, a nonzero residual forces one of the four coordinate extremes. -/
theorem subset_residual_threshold_cases (n : ℕ) (V W : Finset ℕ+)
    (hV : V ⊆ positions n) (hW : W ⊆ positions n) (t : ℝ)
    (hne : grassmannianResidual n V W ≠ 0) :
    t ≤ (V.card : ℝ) ∨ t ≤ (W.card : ℝ) ∨
      ((V.sup PNat.val : ℕ) : ℝ) ≤ t ∨ ((W.sup PNat.val : ℕ) : ℝ) ≤ t := by
  by_contra h
  push Not at h
  obtain ⟨hVcard, hWcard, hVmax, hWmax⟩ := h
  have hu : subsetPermutation n V ≠ 1 := by
    intro hu
    have he := subset_identity_maximum n V hV hu
    rw [he] at hVmax
    linarith
  have hv : subsetPermutation n W ≠ 1 := by
    intro hv
    have he := subset_identity_maximum n W hW hv
    rw [he] at hWmax
    linarith
  have hsep : max V.card W.card ≤ min (V.sup PNat.val) (W.sup PNat.val) := by
    apply Nat.le_min.mpr
    constructor
    · apply max_le
      · exact_mod_cast (hVcard.le.trans hVmax.le)
      · exact_mod_cast (hWcard.le.trans hVmax.le)
    · apply max_le
      · exact_mod_cast (hVcard.le.trans hWmax.le)
      · exact_mod_cast (hWcard.le.trans hWmax.le)
  exact hne (subset_residual_eq_zero_of_le n V W hV hW hu hv hsep)

/-- Independent admissible-subset samples are almost surely admissible in both coordinates. -/
theorem ae_subsetPairLaw (n : ℕ) :
    ∀ᵐ p ∂(subsetLaw n).prod (subsetLaw n),
      p.1 ⊆ positions n ∧ p.2 ⊆ positions n := by
  rw [subsetLaw, ←uniformOn_finset_prod]
  have hs : ((positions n).powerset.product (positions n).powerset).Nonempty := by
    exact ⟨(∅, ∅), by simp⟩
  filter_upwards [ae_mem_uniformOn_finset _ hs] with p hp
  obtain ⟨hV, hW⟩ := Finset.mem_product.mp hp
  exact ⟨Finset.mem_powerset.mp hV, Finset.mem_powerset.mp hW⟩

private theorem pair_four_events (n : ℕ) (A B : Set (Finset ℕ+)) :
    ((subsetLaw n).prod (subsetLaw n)).real
        (((A ×ˢ Set.univ) ∪ (Set.univ ×ˢ A)) ∪ (B ×ˢ Set.univ) ∪ (Set.univ ×ˢ B)) ≤
      2 * ((subsetLaw n).real A + (subsetLaw n).real B) := by
  let μ := (subsetLaw n).prod (subsetLaw n)
  have h₁ := measureReal_union_le (μ := μ) (A ×ˢ Set.univ) (Set.univ ×ˢ A)
  have h₂ := measureReal_union_le (μ := μ)
    ((A ×ˢ Set.univ) ∪ (Set.univ ×ˢ A)) (B ×ˢ Set.univ)
  have h₃ := measureReal_union_le (μ := μ)
    (((A ×ˢ Set.univ) ∪ (Set.univ ×ˢ A)) ∪ (B ×ˢ Set.univ)) (Set.univ ×ˢ B)
  simp only [μ, measureReal_prod_prod, probReal_univ, mul_one, one_mul] at h₁ h₂ h₃
  linarith

/-- Residual probability is bounded by twice the sum of the two coordinate tail probabilities. -/
theorem subset_residual_probability_union (n : ℕ) (t : ℝ) :
    ((subsetLaw n).prod (subsetLaw n)).real {p | grassmannianResidual n p.1 p.2 ≠ 0} ≤
      2 * ((subsetLaw n).real {V | t ≤ (V.card : ℝ)} +
        (subsetLaw n).real {V | ((V.sup PNat.val : ℕ) : ℝ) ≤ t}) := by
  let μ := (subsetLaw n).prod (subsetLaw n)
  let A := {V : Finset ℕ+ | t ≤ (V.card : ℝ)}
  let B := {V : Finset ℕ+ | ((V.sup PNat.val : ℕ) : ℝ) ≤ t}
  let S := ((A ×ˢ Set.univ) ∪ (Set.univ ×ˢ A)) ∪ (B ×ˢ Set.univ) ∪ (Set.univ ×ˢ B)
  have hs : {p | grassmannianResidual n p.1 p.2 ≠ 0} ≤ᵐ[μ] S := by
    filter_upwards [ae_subsetPairLaw n] with p hp
    intro hne
    have h := subset_residual_threshold_cases n p.1 p.2 hp.1 hp.2 t hne
    simp only [S, A, B, Set.mem_union, Set.mem_prod, Set.mem_univ, and_true,
      true_and, Set.mem_ofPred_eq]
    tauto
  calc
    _ ≤ μ.real S := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs)
    _ ≤ _ := pair_four_events n A B

/-- One positive rate gives a four-tail exponential bound on nonzero residual probability. -/
theorem subset_residual_probability_tail :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      ((subsetLaw n).prod (subsetLaw n)).real {p | grassmannianResidual n p.1 p.2 ≠ 0} ≤
        4 * Real.exp (-c * n) := by
  obtain ⟨c, hc, h⟩ := subsetLaw_extreme_tails
  refine ⟨c, hc, fun n => ?_⟩
  have h₁ := subset_residual_probability_union n ((3 : ℝ) * n / 4)
  have h₂ := h n
  linarith [h₂.1, h₂.2]

end RecordStability
