import SchubertForwardStability.StrongMixing.Inequalities.RetainedSubset
import SchubertForwardStability.StrongMixing.Inequalities.SmallSubset

/-!
# Uniform quadratic control of the deterministic retained selector

The selector is chosen from the finite coordinate set before the Laplace parameter.
Its small branch uses the short-subset moment estimate; its large branch uses the
fixed logarithmic Cantor parameters and partial stopping estimate.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

private theorem moment_factor_le {c : ℝ} (hc : 0 < c) :
    1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c)) ≤
      6 * (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) + 384 / c ^ 2 := by
  have hr : Real.exp (-2 * c) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hK : 0 ≤ 1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c)) := by positivity
  have hp : 0 ≤ 384 / c ^ 2 := by positivity
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The deterministic retained subset has log-Laplace transform at most
`card(A)*(t*M)^2*(6*K_c+384/c^2)` for every centered measurable bounded sequence
with geometric coefficient rate `c>0`. The set is independent of `t`;
the uniform parameter conditions are `0<t*M<=1/192` and
`t*M<=c*log(2)/(6*log(max(card(A),2)))`. Empty sets are included. -/
theorem retained_subset_quadratic_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (ht : 0 < t) (hsmall : t * M ≤ 1 / 192)
    (hgate : t * M ≤ c * Real.log 2 / (6 * Real.log (max A.card 2))) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ retainedSubset A, X i ω) ∂μ) ≤
      A.card * (t * M) ^ 2 *
        (6 * (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) + 384 / c ^ 2) := by
  let u := t * M
  have hu : 0 < u := mul_pos ht hM
  by_cases hcard : A.card < 128
  · simp only [retainedSubset, dite_eq_left hcard]
    by_cases hA : A.Nonempty
    · have hn : (A.card : ℝ) ≤ 128 := by exact_mod_cast hcard.le
      have hs : |t| * A.card * M ≤ 1 := by
        rw [abs_of_pos ht]
        have hm := mul_le_mul_of_nonneg_left hsmall
          (Nat.cast_nonneg A.card : 0 ≤ (A.card : ℝ))
        nlinarith only [hm, hn]
      have h := finite_set_small_laplace_le μ X hX hcenter hM.le hc hbound hmix A hA t hs
      calc
        _ ≤ t ^ 2 * A.card * M ^ 2 *
            (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) := h
        _ = A.card * (t * M) ^ 2 *
            (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (moment_factor_le hc) (by positivity)
    · have hE : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      simp [hE]
  · have hn : 2 ≤ A.card := by omega
    have hA : A.Nonempty := Finset.card_pos.mp (by omega)
    let δ := cantorDeletionFraction A.card
    let N := cantorRetainedDepth A.card
    have hd := cantorDeletionFraction_bounds A.card hn
    have hd0 : 0 ≤ δ := hd.1.le
    have hd1 : δ ≤ 1 := hd.2.trans (by norm_num)
    have hlarge : 8 ≤ (A.card : ℝ) * cantorDeletionFraction A.card := by
      by_contra hk
      have hs := cantor_small_length_lt A.card (lt_of_not_ge hk)
      omega
    have hlen := cantorRetainedDepth_length_le A.card hn
    have hln : 0 < Real.log A.card := Real.log_pos
      (by exact_mod_cast (show 1 < A.card by omega))
    rw [max_eq_left (by exact_mod_cast hn : (2 : ℝ) ≤ A.card)] at hgate
    have he : c * δ / 3 = c * Real.log 2 / (6 * Real.log A.card) := by
      dsimp [δ, cantorDeletionFraction]
      field_simp
      norm_num
    have hsep : t * M ≤ c * δ / 3 := by rw [he]; exact hgate
    have hfinal : (t * M) ^ 2 * cantorLength δ A.card N ≤ c / 24 := by
      have hm := mul_le_mul_of_nonneg_right hsep
        (by positivity : 0 ≤ u * cantorLength δ A.card N)
      have hl := mul_le_mul_of_nonneg_left hlen (by positivity : 0 ≤ c * u / 3)
      have hs := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 8 * c)
      change δ * cantorLength δ A.card N ≤ 24 at hlen
      change c * u / 3 * (δ * cantorLength δ A.card N) ≤ c * u / 3 * 24 at hl
      change u ≤ c * δ / 3 at hsep
      change u ^ 2 * cantorLength δ A.card N ≤ c / 24
      nlinarith only [hm, hl, hs]
    have hp := cantorRetainedDepth_pow_le A.card hlarge
    change (2 : ℝ) ^ N ≤ (A.card : ℝ) * δ / 8 at hp
    have hscale := mul_le_mul_of_nonneg_left hd1 (Nat.cast_nonneg A.card : 0 ≤ (A.card : ℝ))
    have hpow : (2 : ℝ) ^ N ≤ A.card := hp.trans (by
      nlinarith [(Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)])
    have h := compressed_cantor_quadratic_le μ X hX hcenter hM hc hd0 hd1 hbound hmix
      A hA N ht (by linarith) hfinal hpow hsep
    simpa only [retainedSubset, dite_eq_right hcard] using h

end StrongMixing
