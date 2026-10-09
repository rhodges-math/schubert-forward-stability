import SchubertForwardStability.Paper.Grassmannian.ResidualEvents
import SchubertForwardStability.LimitTheorems.Binomial.Chernoff

/-! # Subset-encoded Grassmannian products below the ambient size

## Main results

* `subsetLaw_card_upper_tail`: the symmetric-binomial Chernoff bound for sampled sizes.
* `subsetLaw_maximum_lower_tail`: an exponential bound for small selected maxima.
* `subset_product_lt_cases`: product forward stability below the ambient size forces a
  nonzero residual, a selected maximum at most `7n/8`, or a sampled size at least `5n/8`.
* `subset_product_lt_tail`: under independent subset sampling, product forward stability
  is below the ambient size with exponentially small probability.

## Implementation notes

Product forward stability of two sampled subsets is the sum of the two selected maxima,
less the greater sampled size, plus the residual. Off the five exceptional events this sum
is at least `9n/8`.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial MeasureTheory ProbabilityTheory
open scoped Classical

/-- Sampled sizes at least `(1/2 + δ) n` have the symmetric-binomial Chernoff bound. -/
theorem subsetLaw_card_upper_tail (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (subsetLaw n).real {V | ((1 : ℝ) / 2 + δ) * n ≤ V.card} ≤
      Real.exp (-(2 * δ ^ 2) * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, Real.exp_zero]
    exact measureReal_le_one
  have hf (V : Finset ℕ+) :
      ({V : Finset ℕ+ | ((1 : ℝ) / 2 + δ) * n ≤ V.card}.indicator 1 V : ℝ) =
        (fun k : ℕ => if (n : ℝ) / 2 + δ * n ≤ k then (1 : ℝ) else 0) V.card := by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    rw [show ((1 : ℝ) / 2 + δ) * n = n / 2 + δ * n by ring]
  have hA : (subsetLaw n).real {V | ((1 : ℝ) / 2 + δ) * n ≤ V.card} =
      ∑ k ∈ Finset.range (n + 1),
        if (n : ℝ) / 2 + δ * n ≤ k then (n.choose k : ℝ) / 2 ^ n else 0 := by
    rw [← integral_indicator_one (.of_discrete), subsetLaw, integral_uniform_finset,
      Finset.card_powerset, card_positions, Finset.sum_congr rfl (fun V _ => hf V),
      sum_subset_sizes n (fun k : ℕ => if (n : ℝ) / 2 + δ * n ≤ k then (1 : ℝ) else 0),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs
    · rw [nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat, inv_mul_eq_div]
    · rw [smul_zero, mul_zero]
  rw [hA]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (LimitTheorems.binomial_chernoff n hn (δ * n) (by positivity)).trans
    (Real.exp_le_exp.mpr (le_of_eq ?_))
  field_simp

/-- A selected maximum at most `θ n` has probability at most `2^(-(1-θ) n)`. -/
theorem subsetLaw_maximum_lower_tail (n : ℕ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (subsetLaw n).real {V | ((V.sup PNat.val : ℕ) : ℝ) ≤ θ * n} ≤
      Real.exp (-((1 - θ) * Real.log 2) * n) := by
  have hn : (0 : ℝ) ≤ θ * n := by positivity
  have hm : ⌊θ * n⌋₊ ≤ n := by
    apply Nat.floor_le_of_le
    have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  rw [subsetLaw_maximum_real_le n _ hn, min_eq_right hm]
  have hp (k : ℕ) : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hp, hp, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hf := Nat.floor_le hn
  have hl : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hf hl]

/-- Product forward stability below the ambient size forces a nonzero residual, a small
selected maximum or a large sampled size. -/
theorem subset_product_lt_cases (n : ℕ) (V W : Finset ℕ+)
    (h : productForwardStability (subsetPermutation n V) (subsetPermutation n W) < n) :
    grassmannianResidual n V W ≠ 0 ∨
      ((V.sup PNat.val : ℕ) : ℝ) ≤ (7 / 8 : ℝ) * n ∨
      ((W.sup PNat.val : ℕ) : ℝ) ≤ (7 / 8 : ℝ) * n ∨
      ((1 : ℝ) / 2 + 1 / 8) * n ≤ V.card ∨ ((1 : ℝ) / 2 + 1 / 8) * n ≤ W.card := by
  by_contra hc
  push Not at hc
  obtain ⟨h0, hV, hW, hKV, hKW⟩ := hc
  have he := congrArg (fun z : ℤ => (z : ℝ)) h0
  simp only [grassmannianResidual, Int.cast_sub, Int.cast_add, Int.cast_natCast,
    Int.cast_zero, Nat.cast_max, Int.cast_max] at he
  have hK : max (V.card : ℝ) (W.card : ℝ) < ((1 : ℝ) / 2 + 1 / 8) * n := max_lt hKV hKW
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hF : (n : ℝ) ≤
      (productForwardStability (subsetPermutation n V) (subsetPermutation n W) : ℝ) := by
    linarith
  have hlt : (productForwardStability (subsetPermutation n V)
      (subsetPermutation n W) : ℝ) < n := by exact_mod_cast h
  linarith

/-- Under independent subset sampling, product forward stability is below the ambient
size with probability at most the residual probability plus four coordinate tails. -/
theorem subset_product_lt_probability (n : ℕ) :
    ((subsetLaw n).prod (subsetLaw n)).real
        {p | productForwardStability (subsetPermutation n p.1)
          (subsetPermutation n p.2) < n} ≤
      ((subsetLaw n).prod (subsetLaw n)).real {p | grassmannianResidual n p.1 p.2 ≠ 0} +
        2 * ((subsetLaw n).real {V | ((V.sup PNat.val : ℕ) : ℝ) ≤ (7 / 8 : ℝ) * n} +
          (subsetLaw n).real {V | ((1 : ℝ) / 2 + 1 / 8) * n ≤ V.card}) := by
  let μ := (subsetLaw n).prod (subsetLaw n)
  let R := {p : Finset ℕ+ × Finset ℕ+ | grassmannianResidual n p.1 p.2 ≠ 0}
  let A := {V : Finset ℕ+ | ((V.sup PNat.val : ℕ) : ℝ) ≤ (7 / 8 : ℝ) * n}
  let B := {V : Finset ℕ+ | ((1 : ℝ) / 2 + 1 / 8) * n ≤ V.card}
  have hs : {p : Finset ℕ+ × Finset ℕ+ | productForwardStability (subsetPermutation n p.1)
      (subsetPermutation n p.2) < n} ⊆
      R ∪ (A ×ˢ Set.univ) ∪ (Set.univ ×ˢ A) ∪ (B ×ˢ Set.univ) ∪ (Set.univ ×ˢ B) := by
    intro p hp
    have h := subset_product_lt_cases n p.1 p.2 hp
    simp only [R, A, B, Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and,
      Set.mem_ofPred_eq]
    tauto
  have h₁ := measureReal_union_le (μ := μ) R (A ×ˢ Set.univ)
  have h₂ := measureReal_union_le (μ := μ) (R ∪ (A ×ˢ Set.univ)) (Set.univ ×ˢ A)
  have h₃ := measureReal_union_le (μ := μ)
    (R ∪ (A ×ˢ Set.univ) ∪ (Set.univ ×ˢ A)) (B ×ˢ Set.univ)
  have h₄ := measureReal_union_le (μ := μ)
    (R ∪ (A ×ˢ Set.univ) ∪ (Set.univ ×ˢ A) ∪ (B ×ˢ Set.univ)) (Set.univ ×ˢ B)
  simp only [μ, measureReal_prod_prod, probReal_univ, mul_one, one_mul] at h₁ h₂ h₃ h₄
  have hm := measureReal_mono (μ := μ) hs (measure_ne_top _ _)
  simp only [μ] at hm
  change _ ≤ ((subsetLaw n).prod (subsetLaw n)).real R +
    2 * ((subsetLaw n).real A + (subsetLaw n).real B)
  linarith

/-- Under independent subset sampling, product forward stability is below the ambient
size with exponentially small probability. -/
theorem subset_product_lt_tail :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      ((subsetLaw n).prod (subsetLaw n)).real
        {p | productForwardStability (subsetPermutation n p.1)
          (subsetPermutation n p.2) < n} ≤ 8 * Real.exp (-c * n) := by
  obtain ⟨c₀, hc₀, hR⟩ := subset_residual_probability_tail
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c := min c₀ (min ((1 - 7 / 8) * Real.log 2) (2 * (1 / 8) ^ 2))
  have hc : 0 < c := lt_min hc₀ (lt_min (by positivity) (by norm_num))
  refine ⟨c, hc, fun n => ?_⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hexp {a : ℝ} (ha : c ≤ a) : Real.exp (-a * n) ≤ Real.exp (-c * n) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h₀ := (hR n).trans (mul_le_mul_of_nonneg_left (hexp (min_le_left _ _))
    (by norm_num : (0 : ℝ) ≤ 4))
  have h₁ := (subsetLaw_maximum_lower_tail n (θ := 7 / 8) (by norm_num) (by norm_num)).trans
    (hexp ((min_le_right _ _).trans (min_le_left _ _)))
  have h₂ := (subsetLaw_card_upper_tail n (δ := 1 / 8) (by norm_num)).trans
    (hexp ((min_le_right _ _).trans (min_le_right _ _)))
  have h := subset_product_lt_probability n
  linarith

end RecordStability
