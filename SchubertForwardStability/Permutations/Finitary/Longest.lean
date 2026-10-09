import SchubertForwardStability.Permutations.Finitary.Finite
import Mathlib.Data.Fin.Rev

/-! # One-line notation and reversal

## Main definitions

* `oneLine`: values at the first `n` positive positions, in order.
* `longestElement`: reversal of the first `n` positive positions.
* `reversePosition`: the positive position with value `n + 1 - j` inside that interval.

## Implementation notes

Reversal is Mathlib's involution on `Fin n`, extended by the identity. Conjugation
therefore reverses both positions and values without changing the ambient support bound.
-/

namespace FinitaryPerm

/-- The first `n` values of a permutation, listed in increasing position order. -/
def oneLine (n : ℕ) (w : FinitaryPerm ℕ+) : List ℕ+ :=
  List.ofFn fun i : Fin n => w (positiveIndex n i).val

/-- One-line notation has the prescribed ambient length. -/
@[simp]
theorem oneLine_length (n : ℕ) (w : FinitaryPerm ℕ+) : (oneLine n w).length = n :=
  List.length_ofFn

/-- The reversal permutation of the first `n` positive positions. -/
def longestElement (n : ℕ) : FinitaryPerm ℕ+ := ofFinite n Fin.revPerm

/-- Reversal fixes every position larger than its ambient size. -/
theorem isSupported_longestElement (n : ℕ) : IsSupported n (longestElement n) :=
  isSupported_ofFinite n Fin.revPerm

/-- Reversal acts by the reflection formula on positions in its initial interval. -/
theorem longestElement_apply_val (n : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ n) :
    (longestElement n j : ℕ) = n + 1 - (j : ℕ) := by
  obtain ⟨i, hi⟩ := (positiveIndex n).surjective ⟨j, hj⟩
  have hv : (positiveIndex n i).val = j := congrArg Subtype.val hi
  rw [← hv]
  change (ofFinite n Fin.revPerm (positiveIndex n i).val : ℕ) = _
  rw [ofFinite_apply_position, positiveIndex_val, positiveIndex_val]
  change n - (i.val + 1) + 1 = n + 1 - (i.val + 1)
  have := i.isLt
  omega

/-- Reversal fixes a position outside its initial interval. -/
theorem longestElement_apply_above (n : ℕ) (j : ℕ+) (hj : n < (j : ℕ)) :
    longestElement n j = j := isSupported_longestElement n j hj

/-- Reversal is an involution. -/
@[simp]
theorem longestElement_mul_self (n : ℕ) : longestElement n * longestElement n = 1 := by
  rw [longestElement, ← ofFinite_mul]
  have h : (Fin.revPerm : Equiv.Perm (Fin n)) * Fin.revPerm = 1 := by
    apply Equiv.ext
    exact Fin.rev_rev
  rw [h, ofFinite_one]

/-- Reversal is its own inverse. -/
@[simp]
theorem longestElement_inv (n : ℕ) : (longestElement n)⁻¹ = longestElement n := by
  have h := longestElement_mul_self n
  exact inv_eq_of_mul_eq_one_right h

/-- Applying reversal twice fixes any positive position. -/
@[simp]
theorem longestElement_apply_twice (n : ℕ) (j : ℕ+) :
    longestElement n (longestElement n j) = j := by
  change (longestElement n * longestElement n) j = j
  rw [longestElement_mul_self, one_apply]

/-- The positive reflected position inside the first `n` positions. -/
def reversePosition (n : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ n) : ℕ+ :=
  ⟨n + 1 - (j : ℕ), by omega⟩

/-- Reversal sends an initial position to its explicitly reflected position. -/
theorem longestElement_apply (n : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ n) :
    longestElement n j = reversePosition n j hj :=
  PNat.eq (longestElement_apply_val n j hj)

/-- Conjugation by reversal preserves support in the same initial interval. -/
theorem IsSupported.conjugate_longest {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) : IsSupported n (longestElement n * w * longestElement n) :=
  ((isSupported_longestElement n).mul hw).mul (isSupported_longestElement n)

/-- Conjugation reverses the positions and values in the initial interval. -/
theorem conjugate_longest_apply_val {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (j : ℕ+) (hj : (j : ℕ) ≤ n) :
    ((longestElement n * w * longestElement n) j : ℕ) =
      n + 1 - (w (reversePosition n j hj) : ℕ) := by
  rw [mul_apply, mul_apply]
  have hr : (longestElement n j : ℕ) ≤ n :=
    ((isSupported_longestElement n).apply_le_iff j).mpr hj
  rw [longestElement_apply_val n _ ((hw.apply_le_iff _).mpr hr),
    longestElement_apply n j hj]

/-- Conjugating twice by reversal returns the original permutation. -/
@[simp]
theorem conjugate_longest_twice (n : ℕ) (w : FinitaryPerm ℕ+) :
    longestElement n * (longestElement n * w * longestElement n) * longestElement n = w := by
  apply ext
  intro j
  simp only [mul_apply, longestElement_apply_twice]

end FinitaryPerm
