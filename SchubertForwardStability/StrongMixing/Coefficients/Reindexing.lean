import SchubertForwardStability.StrongMixing.Coefficients.CoefficientBounds

/-!
# Increasing coordinate reindexing

Generated coordinate fields contract under index-set inclusions. A strictly
increasing integer reindexing increases every natural lag, so it cannot increase
the corresponding Rosenblatt coefficient.
-/

open MeasureTheory

namespace StrongMixing

/-- A reindexed coordinate family generates a sub-sigma-algebra of the original
family on `t` whenever the reindexing sends every selected index of `s` into `t`.
No coordinate measurability or measure hypothesis is required. -/
theorem generatedSigma_reindex_le {ι κ Ω E : Type*} [MeasurableSpace E]
    (X : κ → Ω → E) (g : ι → κ) {s : Set ι} {t : Set κ}
    (h : ∀ i ∈ s, g i ∈ t) :
    generatedSigma (fun i => X (g i)) s ≤ generatedSigma X t := by
  apply iSup_le
  intro i
  exact comap_le_generatedSigma X (h i i.property)

/-- A strictly increasing map on integer indices increases every natural lag:
`g(k)+h <= g(k+h)` for all integer cuts `k` and natural lags `h`, including zero. -/
theorem int_strictMono_add_le (g : ℤ → ℤ) (hg : StrictMono g) (k : ℤ) (h : ℕ) :
    g k + (h : ℤ) ≤ g (k + (h : ℤ)) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hs := hg (show k + (h : ℤ) < k + ((h + 1 : ℕ) : ℤ) by omega)
    push_cast at hs ⊢
    omega

/-- Strictly increasing integer reindexing cannot increase a sequence's
Rosenblatt coefficient at any natural lag. Past and future coordinate fields
embed at the original cut `g(k)`. No stationarity is required. -/
theorem mixingCoeff_reindex_le {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℤ → Ω → E)
    (g : ℤ → ℤ) (hg : StrictMono g) (h : ℕ) :
    mixingCoeff μ (fun i => X (g i)) h ≤ mixingCoeff μ X h := by
  apply ciSup_le
  intro k
  have hF : generatedSigma (fun i => X (g i)) {i | i ≤ k} ≤
      generatedSigma X {i | i ≤ g k} :=
    generatedSigma_reindex_le X g (fun _ hi => hg.monotone hi)
  have hG : generatedSigma (fun i => X (g i)) {i | k + (h : ℤ) ≤ i} ≤
      generatedSigma X {i | g k + (h : ℤ) ≤ i} :=
    generatedSigma_reindex_le X g (fun _ hi =>
      (int_strictMono_add_le g hg k h).trans (hg.monotone hi))
  exact (strongMixingCoeff_mono μ hF hG).trans (cutCoeff_le_mixingCoeff μ X h (g k))

end StrongMixing
