import SchubertForwardStability.SchubertPolynomials.Backward.Identity
import SchubertForwardStability.Permutations.Random.LongestLaw
import SchubertForwardStability.Permutations.Random.FiberLaw

/-! # The law of backward stability

Let `𝒲_n` be one of `S_n`, the Grassmannian permutations `G_n` or the Boolean permutations `B_n`,
and let `u, v` be independent and uniform in `𝒲_n`. Conjugation by the longest element preserves
`𝒲_n` and the joint law of `(u, v)`, so the identity `BS(u,v) + n = max(n, FS(ρ(u), ρ(v)))` gives,
for `n ≥ 1`,
`BS(u,v) + n` has the law of `max(n, FS(u,v))`.
Writing `D_n = max(0, n - FS(u,v))`, this gives `𝔼[BS(u,v)] = 𝔼[FS(u,v)] - n + 𝔼[D_n]`.

## Main results

* `backward_identDistrib`: `BS(u,v) + n` and `max(n, FS(u,v))` have the same law.
* `backward_expectation`: `𝔼[BS] = 𝔼[FS] - n + 𝔼[max(0, n - FS)]`.

The two sides are equal in law, not pointwise: the pointwise identity uses the conjugated pair.

## References

Hardt, Hodges and Yin, The record statistic and forward stability of Schubert products,
arXiv:2604.02964, Section 6.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- Every real statistic of a pair is integrable under a uniform pair law. -/
theorem integrable_pairLaw (W : Finset (FinitaryPerm ℕ+))
    (f : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ → ℝ) : Integrable f (pairLaw W) := by
  by_cases hW : W.Nonempty
  · let s : Set (FinitaryPerm ℕ+ × FinitaryPerm ℕ+) := (W.product W : Finset _)
    have hf : IntegrableOn f s Measure.count := by
      rw [← s.biUnion_of_singleton, integrableOn_finite_biUnion (W.product W).finite_toSet]
      intro p _
      exact integrableOn_singleton (hx := by simp)
    rw [pairLaw, uniformOn, ProbabilityTheory.cond]
    apply hf.smul_measure
    rw [Measure.count_apply_finset, ENNReal.inv_ne_top]
    exact_mod_cast (Finset.card_pos.mpr (hW.product hW)).ne'
  · have hw : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    simp [hw, pairLaw]

private theorem family_nonempty {n : ℕ} {W : Finset (FinitaryPerm ℕ+)}
    (hW : W = symmetricGroup n ∨ W = grassmannian n ∨ W = boolean n) : W.Nonempty := by
  rcases hW with rfl | rfl | rfl
  · exact ⟨1, one_mem_symmetricGroup n⟩
  · exact ⟨1, one_mem_grassmannian n⟩
  · exact ⟨1, one_mem_boolean n⟩

/-- Backward stability shifted by the ambient size has the law of the forward stability clipped
below at the ambient size, in each of the three families. -/
theorem backward_identDistrib {n : ℕ} (hn : 1 ≤ n) (W : Finset (FinitaryPerm ℕ+))
    (hW : W = symmetricGroup n ∨ W = grassmannian n ∨ W = boolean n) :
    IdentDistrib (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ => productBackStability p.1 p.2 + n)
      (fun p => max n (productForwardStability p.1 p.2)) (pairLaw W) (pairLaw W) := by
  have hSupport (w : FinitaryPerm ℕ+) (hw : w ∈ W) : IsSupported n w := by
    rcases hW with rfl | rfl | rfl
    · exact (mem_symmetricGroup n w).mp hw
    · exact ((mem_grassmannian n w).mp hw).1
    · exact ((mem_boolean n w).mp hw).1
  have hd := (identDistrib_pair_longest n W hW).comp
    (measurable_of_countable (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
      max n (productForwardStability p.1 p.2)))
  have he : (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
      max n (productForwardStability (longestElement n * p.1 * longestElement n)
        (longestElement n * p.2 * longestElement n))) =ᵐ[pairLaw W]
      (fun p => productBackStability p.1 p.2 + n) := by
    filter_upwards [ae_mem_pairLaw W] with p hp
    rw [productBackStability_add_eq_max hn (hSupport p.1 hp.1) (hSupport p.2 hp.2)]
  exact (IdentDistrib.of_ae_eq hd.aemeasurable_fst he).symm.trans hd

/-- The expected backward stability is the expected forward stability minus the ambient size,
plus the expected deficit `max(0, n - FS)`. -/
theorem backward_expectation {n : ℕ} (hn : 1 ≤ n) (W : Finset (FinitaryPerm ℕ+))
    (hW : W = symmetricGroup n ∨ W = grassmannian n ∨ W = boolean n) :
    ∫ p, (productBackStability p.1 p.2 : ℝ) ∂pairLaw W =
      (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw W) - n +
        ∫ p, max 0 ((n : ℝ) - productForwardStability p.1 p.2) ∂pairLaw W := by
  have := isProbabilityMeasure_pairLaw (family_nonempty hW)
  have h := ((backward_identDistrib hn W hW).comp
    (measurable_of_countable (fun k : ℕ => (k : ℝ)))).integral_eq
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_max] at h
  have hmax (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) :
      max (n : ℝ) (productForwardStability p.1 p.2) = (productForwardStability p.1 p.2 : ℝ) +
        max 0 ((n : ℝ) - productForwardStability p.1 p.2) := by
    rcases le_total (n : ℝ) (productForwardStability p.1 p.2) with hle | hle
    · rw [max_eq_right hle, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left hle, max_eq_right (by linarith)]
      ring
  simp only [hmax] at h
  rw [integral_add (integrable_pairLaw W _) (integrable_pairLaw W _),
    integral_add (integrable_pairLaw W _) (integrable_pairLaw W _), integral_const,
    probReal_univ, smul_eq_mul, one_mul] at h
  linarith

end RecordStability
