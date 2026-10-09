import SchubertForwardStability.Permutations.Finitary.Longest
import SchubertForwardStability.Permutations.Statistics.Inversions
import SchubertForwardStability.TypeA.Permutations.AdjacentLength

/-! # Relative inversion lengths at longest elements

## Main results

Finite extension preserves inverses. A supported permutation's relative product
with the longest element has complementary inversion length. Passing to the next
ambient size factors that relative product with additive lengths.

## Implementation notes

All permutations in the statements act on positive positions. The finite inversion
partition supplies the complementary-length proof, including ambient size zero.
-/

namespace FinitaryPerm

/-- The reversal of the empty interval is identity. -/
@[simp]
theorem longestElement_zero : longestElement 0 = 1 := by
  rw [longestElement, show (Fin.revPerm : Equiv.Perm (Fin 0)) = 1 from Subsingleton.elim _ _,
    ofFinite_one]

/-- The reversal of the size-one interval is identity. -/
@[simp]
theorem longestElement_one : longestElement 1 = 1 := by
  rw [longestElement, show (Fin.revPerm : Equiv.Perm (Fin 1)) = 1 from Subsingleton.elim _ _,
    ofFinite_one]

/-- Extending a finite permutation commutes with inversion. -/
theorem ofFinite_inv (n : ℕ) (w : Equiv.Perm (Fin n)) :
    ofFinite n w⁻¹ = (ofFinite n w)⁻¹ := by
  apply (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← ofFinite_mul, mul_inv_cancel, ofFinite_one]

/-- The inverse-relative longest product has complementary length inside its support bound. -/
theorem length_inv_mul_longest {n : ℕ} (w : FinitaryPerm ℕ+) (hw : IsSupported n w) :
    (w⁻¹ * longestElement n).length + w.length = (longestElement n).length := by
  let g : Equiv.Perm (Fin n) := toFinite n w hw
  have hgw : ofFinite n g = w := ofFinite_toFinite n w hw
  have hrel : ofFinite n (g⁻¹ * (Fin.revPerm : Equiv.Perm (Fin n))) =
      w⁻¹ * longestElement n := by
    rw [ofFinite_mul, ofFinite_inv, hgw]
    rfl
  calc (w⁻¹ * longestElement n).length + w.length =
      (ofFinite n (g⁻¹ * Fin.revPerm)).length + (ofFinite n g).length :=
        congrArg₂ Nat.add (congrArg length hrel.symm) (congrArg length hgw.symm)
    _ = finiteLength (g⁻¹ * Fin.revPerm) + finiteLength g := by
      rw [length_ofFinite, length_ofFinite]
    _ = finiteLength (Fin.revPerm : Equiv.Perm (Fin n)) :=
      Schubert.FinPermutation.length_longestRelative_add g
    _ = (longestElement n).length := (length_ofFinite n Fin.revPerm).symm

/-- Multiplication by the longest element complements a supported permutation's length. -/
theorem length_mul_longest {n : ℕ} (w : FinitaryPerm ℕ+) (hw : IsSupported n w) :
    (w * longestElement n).length + w.length = (longestElement n).length := by
  simpa only [inv_inv, length_inv] using length_inv_mul_longest w⁻¹ hw.inv

/-- Relative longest products gain the length of the successive-longest factor. -/
theorem length_relative_succ_add {n : ℕ} (w : FinitaryPerm ℕ+) (hw : IsSupported n w) :
    (w⁻¹ * longestElement (n + 1)).length = (w⁻¹ * longestElement n).length +
      (longestElement n * longestElement (n + 1)).length := by
  have hleft := length_inv_mul_longest (n := n) w hw
  have hright := length_inv_mul_longest (n := n + 1) w (hw.mono (Nat.le_succ n))
  have hstep := length_mul_longest (n := n + 1) (longestElement n)
    ((isSupported_longestElement n).mono (Nat.le_succ n))
  omega

end FinitaryPerm
