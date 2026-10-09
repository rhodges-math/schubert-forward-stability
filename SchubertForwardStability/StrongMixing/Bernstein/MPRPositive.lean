import SchubertForwardStability.StrongMixing.Bernstein.MPRAlmostEverywhere
import SchubertForwardStability.StrongMixing.Coefficients.Extension

/-!
# Positive-indexed MPR sums and Laplace bounds

The sum of the first `k` variables of a sequence indexed by the positive integers
equals the sum over a set of `k` integer coordinates of its constant extension. The
Laplace bound of Merlevède, Peligrad and Rio therefore holds for these sums, for
AEMeasurable and essentially bounded variables.

## References

* F. Merlevède, M. Peligrad and E. Rio, *Bernstein inequality and moderate deviations under
  strong mixing conditions*, High dimensional probability V: the Luminy volume, Inst. Math.
  Stat. (IMS) Collect. 5 (2009), 273-292, arXiv:1202.4777, Theorem 1 and (2.1).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

/-- The sum of the first `k` positive-indexed coordinates, with no omission or
endpoint duplication: `sum(i=0,...,k-1) X(i+1)`. It is zero when `k=0`. -/
def positiveSum {Ω : Type*} (X : ℕ+ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, X ⟨i + 1, by omega⟩ ω

/-- The positive sum equals the sum of the positive extension over the
image of `range(k)` under the injective integer map `i -> i+1`. -/
theorem positiveSum_extension {Ω : Type*} (X : ℕ+ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    (∑ i ∈ (Finset.range k).image (fun i : ℕ => (i : ℤ) + 1),
      positiveExtension X 0 i ω) = positiveSum X k ω := by
  rw [Finset.sum_image (by
    intro i _ j _ hij
    change (i : ℤ) + 1 = (j : ℤ) + 1 at hij
    omega)]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (0 : ℤ) < (i : ℤ) + 1 := by omega
  have he : ((i : ℤ) + 1).toNat = i + 1 := by omega
  simp only [positiveExtension, dite_eq_left hi, he]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Laplace bound of Merlevède, Peligrad and Rio (Theorem 1). Let `X` be a centered,
AEMeasurable sequence indexed by the positive integers, with `|X i| <= M` almost everywhere
and `alpha(h) <= exp(-2*c*h)`. For `k>=4`, the sum `S_k` of its first `k` variables satisfies
`log E exp(t*S_k) <= k*(t*M)^2*V_c/(1-R_c*M*log(k)*log(log(k))*t)`
whenever `0<=t` and the denominator is positive. The constants `V_c` and `R_c` depend
only on `c`. -/
theorem mpr_positive_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ+ → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ (positiveExtension X 0) h ≤
      Real.exp (-2 * c * h)) (k : ℕ) (hk : 4 ≤ k) (ht : 0 ≤ t)
    (hkt : peelingMprRate c * M * Real.log k * Real.log (Real.log k) * t < 1) :
    Integrable (fun ω => Real.exp (t * positiveSum X k ω)) μ ∧
      Real.log (∫ ω, Real.exp (t * positiveSum X k ω) ∂μ) ≤
        k * (t * M) ^ 2 * peelingMprVariance c /
          (1 - peelingMprRate c * M * Real.log k * Real.log (Real.log k) * t) := by
  have hE (i : ℤ) : AEMeasurable (positiveExtension X 0 i) μ := by
    by_cases hi : 0 < i
    · have he : positiveExtension X 0 i = X ⟨i.toNat, by omega⟩ := by
        funext ω
        simp only [positiveExtension, dite_eq_left hi]
      rw [he]
      exact hX _
    · have he : positiveExtension X 0 i = fun _ => (0 : ℝ) := by
        funext ω
        simp only [positiveExtension, dite_eq_right hi]
      rw [he]
      exact aemeasurable_const
  have hC (i : ℤ) : ∫ ω, positiveExtension X 0 i ω ∂μ = 0 := by
    by_cases hi : 0 < i
    · simpa only [positiveExtension, dite_eq_left hi] using hcenter ⟨i.toNat, by omega⟩
    · simp [positiveExtension, hi]
  have hB (i : ℤ) : ∀ᵐ ω ∂μ, |positiveExtension X 0 i ω| ≤ M := by
    by_cases hi : 0 < i
    · simpa only [positiveExtension, dite_eq_left hi] using hbound ⟨i.toNat, by omega⟩
    · exact Filter.Eventually.of_forall (fun _ => by simpa [positiveExtension, hi] using hM.le)
  let A := (Finset.range k).image (fun i : ℕ => (i : ℤ) + 1)
  have hcard : A.card = k := by
    rw [Finset.card_image_of_injective _ (by
      intro i j hij
      change (i : ℤ) + 1 = (j : ℤ) + 1 at hij
      omega), Finset.card_range]
  have h := mpr_laplace_ae_le μ (positiveExtension X 0) hE hC hM hc hB hmix A
    (by simpa only [hcard] using hk) ht (by simpa only [hcard] using hkt)
  simpa only [A, positiveSum_extension, hcard] using h

end StrongMixing
