import SchubertForwardStability.Permutations.Classes.Patterns.PatternMaxFibers
import SchubertForwardStability.Permutations.Classes.Patterns.PatternSizes
import SchubertForwardStability.Permutations.Classes.Patterns.PatternReversal

/-! # Catalan cardinalities from maximum-position joins

Disjoint maximum-position fibers give the Catalan recurrence, including the
empty interval. Reversal transfers the total cardinality to `132` avoidance.

## References

Knuth, The art of computer programming, Vol. 1, Fundamental algorithms,
third edition, Addison-Wesley (1997), Section 2.2.1.
-/

namespace PermutationPattern

open FinitaryPerm
open scoped Classical BigOperators

/-- The `231` avoidance cardinalities satisfy the maximum-position convolution. -/
theorem card_avoiding231_succ (n : ℕ) :
    (avoiding (n + 1) p231).card =
      ∑ a ∈ Finset.range (n + 1), (avoiding a p231).card * (avoiding (n - a) p231).card := by
  let f : FinitaryPerm ℕ+ → ℕ := fun w => (w⁻¹ n.succPNat : ℕ) - 1
  have hMap : (avoiding (n + 1) p231 : Set _).MapsTo f (Finset.range (n + 1)) := by
    intro w hw
    have hs := ((mem_avoiding _ _ _).mp hw).1
    have hBound := (hs.inv.apply_le_iff n.succPNat).mpr (by change n + 1 ≤ n + 1; rfl)
    have hPos := (w⁻¹ n.succPNat).pos
    apply Finset.mem_range.mpr
    change (w⁻¹ n.succPNat : ℕ) - 1 < n + 1
    omega
  rw [Finset.card_eq_sum_card_fiberwise hMap]
  apply Finset.sum_congr rfl
  intro a ha
  have hFilter : ((avoiding (n + 1) p231).filter fun w => f w = a) =
      maximumFiber (n + 1) p231 a.succPNat := by
    ext w
    simp only [Finset.mem_filter, mem_maximumFiber]
    constructor
    · rintro ⟨hw, hIndex⟩
      refine ⟨hw, ?_⟩
      have hPos := (w⁻¹ n.succPNat).pos
      have hEqual : w⁻¹ n.succPNat = a.succPNat := by
        apply PNat.eq
        change (w⁻¹ n.succPNat : ℕ) = a + 1
        change (w⁻¹ n.succPNat : ℕ) - 1 = a at hIndex
        omega
      have h := congrArg PNat.val (apply_inv_apply w n.succPNat)
      rwa [hEqual] at h
    · rintro ⟨hw, hm⟩
      refine ⟨hw, ?_⟩
      have hValue : w a.succPNat = n.succPNat := PNat.eq hm
      have hEqual : w⁻¹ n.succPNat = a.succPNat := by
        apply w.injective
        rw [apply_inv_apply]
        exact hValue.symm
      change (w⁻¹ n.succPNat : ℕ) - 1 = a
      rw [hEqual]
      change a + 1 - 1 = a
      omega
  rw [hFilter]
  have hA := Finset.mem_range.mp ha
  have hSize : a + (n - a) + 1 = n + 1 := by omega
  have h := card_maximumFiber_joinLow a (n - a)
  rwa [hSize] at h

/-- There are exactly n-th Catalan many `231`-avoiders, including size zero. -/
theorem card_avoiding231_catalan (n : ℕ) : (avoiding n p231).card = catalan n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [avoiding_zero p231 (by decide)]
    | succ n =>
      rw [card_avoiding231_succ, catalan_succ, Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i _
      rw [ih i.val (by omega), ih (n - i.val) (by omega)]

/-- There are exactly n-th Catalan many `132`-avoiders, including size zero. -/
theorem card_avoiding132_catalan (n : ℕ) : (avoiding n p132).card = catalan n := by
  rw [← card_avoiding231_eq_132, card_avoiding231_catalan]

end PermutationPattern
