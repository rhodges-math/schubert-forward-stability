import SchubertForwardStability.Permutations.Finitary.Relative
import SchubertForwardStability.Permutations.Classes.ReducedWords

/-! # Zero and maximum inversion lengths

## Main results

A finitary permutation has zero inversion length exactly when it is identity.
Within a supported symmetric group, the reversal uniquely has maximum length.

## Implementation notes

Reduced-word existence supplies the zero-length statement. Complementary relative
lengths supply both the upper bound and its equality characterization.
-/

namespace FinitaryPerm

/-- Zero inversion length characterizes the identity finitary permutation. -/
theorem length_eq_zero_iff (w : FinitaryPerm ℕ+) : w.length = 0 ↔ w = 1 := by
  constructor
  · intro hz
    obtain ⟨word, hword⟩ := exists_reducedWordIn w w.isSupported_forwardStability
    have hempty : word = [] := List.eq_nil_of_length_eq_zero (hword.1.2.trans hz)
    have hp := hword.1.1
    rw [hempty, wordProduct_nil] at hp
    exact hp.symm
  · rintro rfl
    exact length_one

/-- A supported permutation's inversion length is bounded by its ambient longest length. -/
theorem length_le_longest {n : ℕ} (w : FinitaryPerm ℕ+) (hw : IsSupported n w) :
    w.length ≤ (longestElement n).length := by
  have h := length_inv_mul_longest w hw
  omega

/-- The ambient longest element is the unique supported permutation of maximum length. -/
theorem length_eq_longest_iff {n : ℕ} (w : FinitaryPerm ℕ+) (hw : IsSupported n w) :
    w.length = (longestElement n).length ↔ w = longestElement n := by
  constructor
  · intro he
    have hc := length_inv_mul_longest w hw
    have hz : (w⁻¹ * longestElement n).length = 0 := by omega
    have hr := (length_eq_zero_iff _).mp hz
    calc w = w * 1 := (mul_one w).symm
      _ = w * (w⁻¹ * longestElement n) := by rw [hr]
      _ = longestElement n := by rw [← mul_assoc, mul_inv_cancel, one_mul]
  · rintro rfl
    rfl

end FinitaryPerm
