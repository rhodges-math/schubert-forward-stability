import SchubertForwardStability.LimitTheorems.Binomial.Gaussian
import SchubertForwardStability.Permutations.Random.CardLaw
import SchubertForwardStability.LimitTheorems.Convergence.LawChange
import SchubertForwardStability.LimitTheorems.Convergence.Independent

/-! # Gaussian limits for independent subset cardinalities

For a uniform random subset `V` of `[1, n]`, `(2*|V| - n)/sqrt(n)` tends to a standard
Gaussian, and the sizes of two independent subsets have independent Gaussian limits. Hence
`-(max(|V|, |W|) - n/2)/sqrt(n)` tends to `-max(Z_1, Z_2)/2`, where `Z_1` and `Z_2` are
independent standard Gaussians.
-/

open FinitaryPerm MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace RecordStability

/-- A symmetric sampled cardinality, centered and scaled, tends to a standard Gaussian. -/
theorem subset_card_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (V : Finset ℕ+) => (2 * (V.card : ℝ) - n) / Real.sqrt n)
      atTop id (fun n => subsetLaw n) (gaussianReal 0 1) := by
  apply LimitTheorems.tendstoInDistribution_law_congr LimitTheorems.tendsto_binomial_gaussian
  · intro n
    exact (measurable_of_countable _).aemeasurable
  · exact measurable_id.aemeasurable
  · intro n
    change Measure.map ((fun k : ℕ => (2 * (k : ℝ) - n) / Real.sqrt n) ∘ Finset.card)
      (subsetLaw n) = _
    rw [← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      subsetLaw_card_binomial]
    rfl
  · rfl

/-- The two sampled cardinalities have independent standard Gaussian limits. -/
theorem subset_card_joint_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : Finset ℕ+ × Finset ℕ+) =>
        ((2 * (p.1.card : ℝ) - n) / Real.sqrt n,
          (2 * (p.2.card : ℝ) - n) / Real.sqrt n))
      atTop id (fun n => (subsetLaw n).prod (subsetLaw n))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let X (n : ℕ) (V : Finset ℕ+) := (2 * (V.card : ℝ) - n) / Real.sqrt n
  have hX (n : ℕ) : Measurable (X n) := measurable_of_countable _
  have hf : TendstoInDistribution (fun (n : ℕ) p => X n p.1) atTop
      (Prod.fst : ℝ × ℝ → ℝ) (fun n => (subsetLaw n).prod (subsetLaw n))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    apply LimitTheorems.tendstoInDistribution_law_congr subset_card_gaussian
    · intro n
      exact ((hX n).comp measurable_fst).aemeasurable
    · exact measurable_fst.aemeasurable
    · intro n
      change Measure.map (X n ∘ Prod.fst) _ = _
      rw [← Measure.map_map (hX n) measurable_fst]
      simp [X]
    · simp
  have hs : TendstoInDistribution (fun (n : ℕ) p => X n p.2) atTop
      (Prod.snd : ℝ × ℝ → ℝ) (fun n => (subsetLaw n).prod (subsetLaw n))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    apply LimitTheorems.tendstoInDistribution_law_congr subset_card_gaussian
    · intro n
      exact ((hX n).comp measurable_snd).aemeasurable
    · exact measurable_snd.aemeasurable
    · intro n
      change Measure.map (X n ∘ Prod.snd) _ = _
      rw [← Measure.map_map (hX n) measurable_snd]
      simp [X]
    · simp
  apply LimitTheorems.tendstoInDistribution_indep hf hs
  · intro n
    exact indepFun_prod (hX n) (hX n)
  · exact indepFun_prod measurable_id measurable_id

private theorem neg_half_max_scaled (n : ℕ) (a b : ℝ) :
    -(1 / 2 : ℝ) * max ((2 * a - n) / Real.sqrt n) ((2 * b - n) / Real.sqrt n) =
      -(max a b - (n : ℝ) / 2) / Real.sqrt n := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right
      (by linarith : 2 * a - n ≤ 2 * b - n) (Real.sqrt_nonneg _))]
    ring
  · rw [max_eq_left h, max_eq_left (div_le_div_of_nonneg_right
      (by linarith : 2 * b - n ≤ 2 * a - n) (Real.sqrt_nonneg _))]
    ring

/-- The negative centered cardinality maximum tends to minus half a Gaussian maximum. -/
theorem subset_card_maximum_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : Finset ℕ+ × Finset ℕ+) =>
        -((max p.1.card p.2.card : ℝ) - (n : ℝ) / 2) / Real.sqrt n)
      atTop (fun p : ℝ × ℝ => -(1 / 2 : ℝ) * max p.1 p.2)
      (fun n => (subsetLaw n).prod (subsetLaw n))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have h := subset_card_joint_gaussian.continuous_comp
    (g := fun p : ℝ × ℝ => -(1 / 2 : ℝ) * max p.1 p.2) (by fun_prop)
  apply h.congr
  · intro n
    exact Filter.Eventually.of_forall fun p => neg_half_max_scaled n p.1.card p.2.card
  · exact Filter.Eventually.of_forall fun _ => rfl

end RecordStability
