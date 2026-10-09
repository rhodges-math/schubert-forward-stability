import SchubertForwardStability.Permutations.Statistics.LehmerRanks

/-!
# Injectivity of the right Lehmer code

## Main results

* `apply_eq_of_rightCount` recovers a permutation entry from an agreed prefix
  and its right inversion count.
* `lehmerCode_injective` shows that all right inversion counts determine the
  finitary permutation uniquely.

## Implementation notes

The lower-value rank increases strictly on the remaining value set. Prefix
induction therefore recovers successive entries inside a common support bound.
-/

namespace FinitaryPerm

noncomputable section

open scoped Classical

private theorem rank_lt_rank {s : Finset ℕ+} {a b : ℕ+} (ha : a ∈ s) (hab : a < b) :
    (s.filter (· < a)).card < (s.filter (· < b)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hxs, hxa⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxs, hxa.trans hab⟩
  · intro he
    have hb : a ∈ s.filter (· < b) := Finset.mem_filter.mpr ⟨ha, hab⟩
    have haa : a ∈ s.filter (· < a) := he.symm ▸ hb
    exact (lt_irrefl a) (Finset.mem_filter.mp haa).2

/-- Agreement on the strict prefix and on the right inversion count determines
the current entry of two permutations with a common support bound. -/
theorem apply_eq_of_rightCount {n : ℕ} {w v : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (hv : IsSupported n v) (i : ℕ+) (hi : (i : ℕ) ≤ n)
    (hprefix : ∀ k : ℕ+, k < i → w k = v k)
    (hcount : w.rightInversionCount i = v.rightInversionCount i) : w i = v i := by
  have hs := remainingValues_congr (n := n) i hprefix
  have hw_rank := rightInversionCount_eq_rank hw i
  have hv_rank := rightInversionCount_eq_rank hv i
  rw [← hs] at hv_rank
  rcases lt_trichotomy (w i) (v i) with hlt | he | hgt
  · have hrank := rank_lt_rank (apply_mem_remainingValues hw i hi) hlt
    omega
  · exact he
  · have hav : v i ∈ remainingValues n w i := by
      rw [hs]
      exact apply_mem_remainingValues hv i hi
    have hrank := rank_lt_rank hav hgt
    omega

/-- The right Lehmer exponent vector determines a finitary permutation uniquely. -/
theorem lehmerCode_injective : Function.Injective (lehmerCode : FinitaryPerm ℕ+ → ℕ+ →₀ ℕ) := by
  intro w v hcode
  let n := max w.forwardStability v.forwardStability
  have hw : IsSupported n w := w.isSupported_forwardStability.mono (le_max_left _ _)
  have hv : IsSupported n v := v.isSupported_forwardStability.mono (le_max_right _ _)
  have hpoint : ∀ m : ℕ, ∀ i : ℕ+, (i : ℕ) = m → w i = v i := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i him
      by_cases hi : (i : ℕ) ≤ n
      · apply apply_eq_of_rightCount hw hv i hi
        · intro k hk
          apply ih (k : ℕ) ?_ k rfl
          change (k : ℕ) < (i : ℕ) at hk
          omega
        · have hcoeff := congrArg (fun a : ℕ+ →₀ ℕ => a i) hcode
          simpa only [lehmerCode_apply] using hcoeff
      · rw [hw i (lt_of_not_ge hi), hv i (lt_of_not_ge hi)]
  apply ext
  intro i
  exact hpoint (i : ℕ) i rfl

end

end FinitaryPerm
