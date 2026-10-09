import SchubertForwardStability.Paper.Backward.SubsetDeficit
import SchubertForwardStability.Paper.Backward.Clipping
import SchubertForwardStability.Paper.Grassmannian.Expectation
import SchubertForwardStability.Paper.Grassmannian.ProductGaussian
import SchubertForwardStability.LimitTheorems.Convergence.IdentTransfer

/-! # Clipped product forward stability for Grassmannian permutations

## Main results

* `grassmannian_product_lt_tail`: for independent uniform Grassmannian permutations,
  `F < n` has exponentially small probability.
* `grassmannian_deficit_tail`: the mean deficit `max 0 (n - F)` is exponentially small.
* `grassmannian_clipped_expectation`, `grassmannian_clipped_gaussian`: `max n F` has the
  mean asymptotic and the Gaussian maximum limit of `F`.

## Implementation notes

Here `F` is product forward stability of two independent uniform Grassmannian
permutations of size `n`. The event `F < n` is first bounded under independent subset
sampling and then transferred to the uniform pair law, whose total-variation distance to
the encoded pair law is at most `2 n / 2 ^ n`.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial MeasureTheory ProbabilityTheory Filter
open scoped Topology

private theorem natCast_mul_exp_neg_le {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (n : ℝ) * Real.exp (-a * n) ≤ 2 / a * Real.exp (-(a / 2) * n) := by
  have hx : (a / 2) * (n : ℝ) ≤ Real.exp ((a / 2) * n) := by
    have h := Real.add_one_le_exp ((a / 2) * n)
    linarith
  have hn : (n : ℝ) ≤ 2 / a * Real.exp ((a / 2) * n) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    nlinarith
  calc
    (n : ℝ) * Real.exp (-a * n) ≤ 2 / a * Real.exp ((a / 2) * n) * Real.exp (-a * n) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _)
    _ = 2 / a * Real.exp (-(a / 2) * n) := by
      rw [mul_assoc, ← Real.exp_add, show a / 2 * (n : ℝ) + -a * n = -(a / 2) * n by ring]

private theorem tendsto_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-c * n)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop hc)

/-- For independent uniform Grassmannian permutations, product forward stability is
below the ambient size with exponentially small probability. -/
theorem grassmannian_product_lt_tail :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      (pairLaw (grassmannian n)).real {p | productForwardStability p.1 p.2 < n} ≤
        C * Real.exp (-c * n) := by
  obtain ⟨c₀, hc₀, h⟩ := subset_product_lt_tail
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c := min c₀ (Real.log 2 / 2)
  have hc : 0 < c := lt_min hc₀ (by positivity)
  refine ⟨8 + 4 / Real.log 2, c, by positivity, hc, fun n => ?_⟩
  let E := {p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ | productForwardStability p.1 p.2 < n}
  have hmodel : ((grassmannianLaw n).prod (grassmannianLaw n)).real E =
      ((subsetLaw n).prod (subsetLaw n)).real
        {p | productForwardStability (subsetPermutation n p.1)
          (subsetPermutation n p.2) < n} := by
    rw [grassmannianLaw, Measure.map_prod_map _ _ (measurable_subsetPermutation n)
      (measurable_subsetPermutation n), map_measureReal_apply
      ((measurable_subsetPermutation n).prodMap (measurable_subsetPermutation n)) .of_discrete]
    rfl
  have htv := abs_sub_le_iff.mp (LimitTheorems.abs_measureReal_sub_le_totalVariation
    ((grassmannianLaw n).prod (grassmannianLaw n)) (pairLaw (grassmannian n)) E)
  have hpow := grass_pair_totalVariation_pow_le n
  have h2 : 2 * (n : ℝ) / (2 : ℝ) ^ n ≤
      4 / Real.log 2 * Real.exp (-(Real.log 2 / 2) * n) := by
    have hp : (2 : ℝ) ^ n = Real.exp (n * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have hm := natCast_mul_exp_neg_le hl n
    rw [hp, mul_div_assoc, div_eq_mul_inv, ← Real.exp_neg,
      show -((n : ℝ) * Real.log 2) = -Real.log 2 * n by ring]
    have he : 4 / Real.log 2 * Real.exp (-(Real.log 2 / 2) * n) =
        2 * (2 / Real.log 2 * Real.exp (-(Real.log 2 / 2) * n)) := by ring
    rw [he]
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he₁ : Real.exp (-c₀ * n) ≤ Real.exp (-c * n) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left c₀ (Real.log 2 / 2)])
  have he₂ : Real.exp (-(Real.log 2 / 2) * n) ≤ Real.exp (-c * n) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right c₀ (Real.log 2 / 2)])
  have hlog : 0 ≤ 4 / Real.log 2 := by positivity
  have h₃ := mul_le_mul_of_nonneg_left he₂ hlog
  have h₄ := h n
  rw [← hmodel] at h₄
  change (pairLaw (grassmannian n)).real E ≤ _
  nlinarith

/-- Off the event `F < n` the deficit vanishes, and on it the deficit is at most `n`. -/
theorem deficit_le_indicator (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) :
    max 0 ((n : ℝ) - productForwardStability p.1 p.2) ≤
      {q : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ | productForwardStability q.1 q.2 < n}.indicator
        (fun _ => (n : ℝ)) p := by
  have hF₀ : (0 : ℝ) ≤ productForwardStability p.1 p.2 := Nat.cast_nonneg _
  by_cases h : productForwardStability p.1 p.2 < n
  · rw [Set.indicator_of_mem (show p ∈ {q : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ |
      productForwardStability q.1 q.2 < n} from h)]
    exact max_le (Nat.cast_nonneg _) (by linarith)
  · rw [Set.indicator_of_notMem (show p ∉ {q : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ |
      productForwardStability q.1 q.2 < n} from h)]
    have hF : (n : ℝ) ≤ productForwardStability p.1 p.2 := by exact_mod_cast not_lt.mp h
    exact max_le le_rfl (by linarith)

/-- The mean deficit is at most the ambient size times the probability of `F < n`. -/
theorem integral_deficit_le_mul_prob (n : ℕ) (W : Finset (FinitaryPerm ℕ+)) :
    (∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2) ∂pairLaw W) ≤
      n * (pairLaw W).real {p | productForwardStability p.1 p.2 < n} := by
  calc
    _ ≤ ∫ p, {q : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ |
          productForwardStability q.1 q.2 < n}.indicator (fun _ => (n : ℝ)) p
        ∂pairLaw W :=
      integral_uniform_finset_mono _ _ _ fun p _ => deficit_le_indicator n p
    _ = _ := by rw [integral_indicator_const _ .of_discrete, smul_eq_mul, mul_comm]

/-- The uniform Grassmannian mean deficit below the ambient size is exponentially small. -/
theorem grassmannian_deficit_tail :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      (∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2)
        ∂pairLaw (grassmannian n)) ≤ C * Real.exp (-c * n) := by
  obtain ⟨C, c, hC, hc, h⟩ := grassmannian_product_lt_tail
  refine ⟨C * (2 / c), c / 2, by positivity, by positivity, fun n => ?_⟩
  calc
    _ ≤ n * (pairLaw (grassmannian n)).real {p | productForwardStability p.1 p.2 < n} :=
      integral_deficit_le_mul_prob n _
    _ ≤ n * (C * Real.exp (-c * n)) := mul_le_mul_of_nonneg_left (h n) (Nat.cast_nonneg n)
    _ = C * ((n : ℝ) * Real.exp (-c * n)) := by ring
    _ ≤ C * (2 / c * Real.exp (-(c / 2) * n)) :=
      mul_le_mul_of_nonneg_left (natCast_mul_exp_neg_le hc n) hC.le
    _ = _ := by ring

/-- The uniform Grassmannian mean deficit tends to zero. -/
theorem tendsto_integral_grass_deficit :
    Tendsto (fun n : ℕ => ∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2)
      ∂pairLaw (grassmannian n)) atTop (𝓝 0) := by
  obtain ⟨C, c, _, hc, h⟩ := grassmannian_deficit_tail
  have hlim := (tendsto_exp_neg_mul hc).const_mul C
  rw [mul_zero] at hlim
  exact squeeze_zero (fun n => integral_deficit_nonneg n _) h hlim

/-- Uniform Grassmannian forward stability clipped at the ambient size has the
three-halves mean with its square-root term. -/
theorem grassmannian_clipped_expectation :
    Tendsto (fun n : ℕ =>
      (∫ p, max (n : ℝ) (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (grassmannian n)) -
        ((3 : ℝ) / 2 * n - Real.sqrt n / (2 * Real.sqrt Real.pi) - 2)) atTop (𝓝 0) :=
  tendsto_clipped_integral grassmannian_expectation tendsto_integral_grass_deficit

/-- Uniform Grassmannian forward stability clipped at the ambient size has the Gaussian
maximum limit. -/
theorem grassmannian_clipped_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        (max (n : ℝ) (productForwardStability p.1 p.2 : ℝ) - (3 : ℝ) / 2 * n) /
          Real.sqrt n)
      atTop (fun p : ℝ × ℝ => -(1 / 2 : ℝ) * max p.1 p.2)
      (fun n => pairLaw (grassmannian n)) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
  tendstoInDistribution_clipped (a := fun n => (3 : ℝ) / 2 * n)
    (b := fun n => Real.sqrt n) (fun _ => Real.sqrt_nonneg _) grassmannian_gaussian
    (tendsto_integral_grass_deficit.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))

end RecordStability
