import SchubertForwardStability.Permutations.Statistics.Inversions
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Right inversion counts and Lehmer exponents

## Main definitions

* `rightInversionSet w i` consists of the later positions with value smaller than `w i`.
* `rightInversionCount w i` is its cardinality.
* `lehmerCode w` is the finitely supported vector of right inversion counts.

## Main results

The right inversion sets are independent of any support truncation. Their cardinalities
are bounded by `n - i` when the permutation is supported in size `n`.

## Implementation notes

Positions and values are positive integers. The right inversion code is distinct from
the left inversion coordinates characterizing records.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter I.
-/

namespace FinitaryPerm

noncomputable section

open scoped Classical

/-- Later positions whose values are smaller than the value at the given position. -/
def rightInversionSet (w : FinitaryPerm ℕ+) (i : ℕ+) : Finset ℕ+ :=
  (positions w.forwardStability).filter fun j => i < j ∧ w j < w i

/-- Right inversion membership is given by the position and value inequalities. -/
@[simp] theorem mem_rightInversionSet (w : FinitaryPerm ℕ+) (i j : ℕ+) :
    j ∈ w.rightInversionSet i ↔ i < j ∧ w j < w i := by
  rw [rightInversionSet, Finset.mem_filter, mem_positions]
  constructor
  · exact fun h => h.2
  · rintro ⟨hij, hvalue⟩
    have hj : (j : ℕ) ≤ w.forwardStability := by
      by_contra h
      exact (not_lt_of_gt (w.isRecord_above (lt_of_not_ge h) i hij)) hvalue
    exact ⟨hj, hij, hvalue⟩

/-- The right inversion count is the number of smaller values strictly to the right. -/
def rightInversionCount (w : FinitaryPerm ℕ+) (i : ℕ+) : ℕ :=
  (w.rightInversionSet i).card

/-- A support bound truncates the right inversion set without changing it. -/
theorem rightInversionSet_eq_filter {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (i : ℕ+) :
    w.rightInversionSet i = (positions n).filter fun j => i < j ∧ w j < w i := by
  ext j
  rw [mem_rightInversionSet, Finset.mem_filter, mem_positions]
  constructor
  · rintro ⟨hij, hvalue⟩
    have hj : (j : ℕ) ≤ n := by
      by_contra h
      exact (not_lt_of_gt (hw.isRecord_above (lt_of_not_ge h) i hij)) hvalue
    exact ⟨hj, hij, hvalue⟩
  · exact fun h => h.2

/-- Every right inversion count is bounded by the number of later supported positions. -/
theorem rightInversionCount_le {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (i : ℕ+) : w.rightInversionCount i ≤ n - (i : ℕ) := by
  rw [rightInversionCount, rightInversionSet_eq_filter hw i]
  have hcard : ((positions n).filter fun j => i < j).card = n - (i : ℕ) := by
    rw [← Nat.card_Ico]
    apply Finset.card_bij (fun (j : ℕ+) _ => (j : ℕ) - 1)
    · intro j hj
      obtain ⟨hj, hij⟩ := Finset.mem_filter.mp hj
      have hjn := (mem_positions n j).mp hj
      have hjpos := PNat.pos j
      change (i : ℕ) < (j : ℕ) at hij
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro j _ k _ h
      apply PNat.eq
      have hjpos := PNat.pos j
      have hkpos := PNat.pos k
      omega
    · intro k hk
      obtain ⟨hik, hkn⟩ := Finset.mem_Ico.mp hk
      refine ⟨Nat.succPNat k, ?_, ?_⟩
      · rw [Finset.mem_filter, mem_positions]
        change k + 1 ≤ n ∧ (i : ℕ) < k + 1
        omega
      · change k + 1 - 1 = k
        omega
  rw [← hcard]
  apply Finset.card_le_card
  intro j hj
  obtain ⟨hjn, hij, _⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨hjn, hij⟩

/-- Right inversion counts vanish at and beyond every support bound. -/
theorem rightInversionCount_eq_zero {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (i : ℕ+) (hi : n ≤ (i : ℕ)) :
    w.rightInversionCount i = 0 := by
  have hle := rightInversionCount_le hw i
  omega

/-- The Lehmer exponent vector of a finitary permutation. -/
def lehmerCode (w : FinitaryPerm ℕ+) : ℕ+ →₀ ℕ :=
  Finsupp.onFinset (positions w.forwardStability) w.rightInversionCount fun i hi => by
    rw [mem_positions]
    have hle := rightInversionCount_le w.isSupported_forwardStability i
    omega

/-- A Lehmer exponent is exactly the right inversion count at that position. -/
@[simp] theorem lehmerCode_apply (w : FinitaryPerm ℕ+) (i : ℕ+) :
    w.lehmerCode i = w.rightInversionCount i := rfl

/-- Support containment gives the separate staircase bound on every Lehmer exponent. -/
theorem lehmerCode_le {n : ℕ} {w : FinitaryPerm ℕ+} (hw : IsSupported n w) (i : ℕ+) :
    w.lehmerCode i ≤ n - (i : ℕ) := rightInversionCount_le hw i

/-- The identity permutation has zero Lehmer code. -/
@[simp] theorem lehmerCode_one : lehmerCode (1 : FinitaryPerm ℕ+) = 0 := by
  ext i
  rw [lehmerCode_apply]
  exact rightInversionCount_eq_zero (isSupported_one 0) i (Nat.zero_le _)

end

end FinitaryPerm
