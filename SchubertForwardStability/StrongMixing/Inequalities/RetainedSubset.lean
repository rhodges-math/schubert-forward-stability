import SchubertForwardStability.StrongMixing.Inequalities.CompressedCantor
import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorSmallLengths

/-!
# A deterministic half-retained subset for finite peeling

Below the explicit finite threshold, keep the entire coordinate set. Otherwise,
use its compressed Cantor subset with fixed logarithmic parameters. This selector
does not depend on the measure, the random variables, or the Laplace parameter.
-/

namespace StrongMixing

/-- Select a fixed retained subset of a finite integer coordinate set. Keep the
whole set when its cardinality is below 128; otherwise use its sorted compressed
Cantor set with logarithmic deletion fraction and fixed retained depth. -/
noncomputable def retainedSubset (A : Finset ℤ) : Finset ℤ :=
  if h : A.card < 128 then A
  else compressedCantorSet A (Finset.card_pos.mp (by omega))
    (cantorDeletionFraction A.card) (cantorRetainedDepth A.card)

/-- The deterministic retained selector sends the empty coordinate set to itself. -/
theorem retainedSubset_empty : retainedSubset ∅ = ∅ := by simp [retainedSubset]

/-- Every deterministically retained coordinate belongs to the original finite
coordinate set, including the empty-set and small-cardinality branches. -/
theorem retainedSubset_subset (A : Finset ℤ) : retainedSubset A ⊆ A := by
  by_cases h : A.card < 128
  · simp [retainedSubset, h]
  · simp only [retainedSubset, dite_eq_right h]
    exact compressedCantorSet_subset _ _ _ _

/-- The deterministic retained subset has at least half the original cardinality.
The selected coordinates depend only on the original finite set, and the claim
holds for every cardinality, including zero and one. -/
theorem retainedSubset_half (A : Finset ℤ) :
    (A.card : ℝ) / 2 ≤ (retainedSubset A).card := by
  by_cases h : A.card < 128
  · simp only [retainedSubset, dite_eq_left h]
    have hn : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg _
    linarith
  · have hn : 2 ≤ A.card := by omega
    have hlarge : 8 ≤ (A.card : ℝ) * cantorDeletionFraction A.card := by
      by_contra hk
      have hs := cantor_small_length_lt A.card (lt_of_not_ge hk)
      omega
    simp only [retainedSubset, dite_eq_right h]
    rw [compressedCantorSet_card]
    exact cantorRetained_half A.card hn 0 hlarge

/-- Removing the deterministic retained subset leaves at most half the original
cardinality: `2*card(residual)<=card(A)` as natural numbers. -/
theorem retainedSubset_residual_card (A : Finset ℤ) :
    2 * (A \ retainedSubset A).card ≤ A.card := by
  have hs := retainedSubset_subset A
  have hh := retainedSubset_half A
  have hR : (A.card : ℝ) ≤ 2 * (retainedSubset A).card := by linarith
  have hN : A.card ≤ 2 * (retainedSubset A).card := by exact_mod_cast hR
  have hc := Finset.card_le_card hs
  rw [Finset.card_sdiff_of_subset hs]
  omega

end StrongMixing
