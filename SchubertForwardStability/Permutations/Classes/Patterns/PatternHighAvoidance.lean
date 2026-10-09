import SchubertForwardStability.Permutations.Classes.Patterns.PatternHighJoin
import SchubertForwardStability.Permutations.Classes.Patterns.PatternFactors

/-! # Avoidance and unique factors for higher-left joins

A higher-left join `joinHigh a b u v` avoids `132` exactly when both factors do, and every
`132`-avoider of size `a+b+1` with its maximum at position `a+1` is such a join.
-/

namespace PermutationPattern

open FinitaryPerm
open scoped Classical

/-- Reversing a `132`-avoider gives a `231`-avoider. -/
theorem mem_reversed_avoiding132 (n : ℕ) (w : FinitaryPerm ℕ+) :
    w * longestElement n ∈ avoiding n p231 ↔ w ∈ avoiding n p132 := by
  simpa only [reversePattern_p231, mul_assoc, longestElement_mul_self, mul_one] using
    (mem_reverse_avoiding n p231 (w * longestElement n)).symm

/-- A higher-left join avoids `132` exactly when its two factors do. -/
theorem joinHigh_avoiding132_iff (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) :
    joinHigh a b u v ∈ avoiding (a + b + 1) p132 ↔
      u ∈ avoiding a p132 ∧ v ∈ avoiding b p132 := by
  have hSize : a + b + 1 = b + a + 1 := by omega
  have hRev := mem_reverse_avoiding (b + a + 1) p231
    (joinLow b a (v * longestElement b) (u * longestElement a))
  simp only [reversePattern_p231] at hRev
  rw [joinHigh, hSize, hRev, joinLow_avoiding231_iff b a _ _
    (hv.mul (isSupported_longestElement b)) (hu.mul (isSupported_longestElement a)),
    mem_reversed_avoiding132, mem_reversed_avoiding132, and_comm]

/-- Every bounded `132`-avoider splits into its two value intervals around the maximum. -/
theorem exists_joinHigh_avoiding132 (a b : ℕ) (w : FinitaryPerm ℕ+)
    (hw : w ∈ avoiding (a + b + 1) p132) (hm : (w a.succPNat : ℕ) = a + b + 1) :
    ∃ u v, u ∈ avoiding a p132 ∧ v ∈ avoiding b p132 ∧ w = joinHigh a b u v := by
  have hSize : a + b + 1 = b + a + 1 := by omega
  have hwRev := (mem_reversed_avoiding132 (a + b + 1) w).mpr hw
  have hIndex : longestElement (a + b + 1) b.succPNat = a.succPNat := by
    apply PNat.eq
    rw [longestElement_apply_val _ _ (by change b + 1 ≤ a + b + 1; omega)]
    change a + b + 1 + 1 - (b + 1) = a + 1
    omega
  have hmRev : ((w * longestElement (a + b + 1)) b.succPNat : ℕ) = b + a + 1 := by
    rw [mul_apply, hIndex, hm, hSize]
  have hwRev' : w * longestElement (a + b + 1) ∈ avoiding (b + a + 1) p231 := by
    rw [← hSize]
    exact hwRev
  obtain ⟨v, u, hv, hu, hEqual⟩ := exists_joinLow_avoiding231 b a
    (w * longestElement (a + b + 1)) hwRev' hmRev
  refine ⟨u * longestElement a, v * longestElement b, ?_, ?_, ?_⟩
  · simpa only [reversePattern_p231] using (mem_reverse_avoiding a p231 u).mpr hu
  · simpa only [reversePattern_p231] using (mem_reverse_avoiding b p231 v).mpr hv
  · simp only [joinHigh, mul_assoc, longestElement_mul_self, mul_one]
    rw [← hEqual]
    simp only [mul_assoc, longestElement_mul_self, mul_one]

end PermutationPattern
