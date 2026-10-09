import SchubertForwardStability.Permutations.Statistics.SuffixPivot
import SchubertForwardStability.Permutations.Statistics.DescentOrder
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Finset.Max

/-! # Existence of increasing-tail pivots

## Main results

Every nonidentity finitary permutation has an increasing-tail pivot. The start is a
largest adjacent descent; the pivot is a largest later position carrying a smaller value.

## Implementation notes

Finite maxima give the two positions explicitly within the proof. Strict increase after
the last descent follows by chaining strict adjacent increases on positive indices.
-/

namespace FinitaryPerm

open scoped Classical

/-- Absence of adjacent descents after a position gives a strictly increasing tail. -/
theorem strictMono_after_last_descent {w : FinitaryPerm ℕ+} {r : ℕ+}
    (hlast : ∀ j : ℕ+, r < j → ¬HasDescent w j) :
    StrictMonoOn w {j : ℕ+ | r < j} := by
  let f : ℕ → ℕ+ := fun n => w ⟨n + 1, Nat.zero_lt_succ n⟩
  have hf : StrictMonoOn f (Set.Ici (r : ℕ)) := by
    apply strictMonoOn_of_lt_add_one Set.ordConnected_Ici
    intro n _ hn _
    have hpos : r < (⟨n + 1, Nat.zero_lt_succ n⟩ : ℕ+) := by
      change (r : ℕ) < n + 1
      exact Nat.lt_succ_of_le hn
    have hnot := hlast _ hpos
    have hne : w ⟨n + 1, Nat.zero_lt_succ n⟩ ≠
        w (⟨n + 1, Nat.zero_lt_succ n⟩ + 1) := by
      intro he
      have hp := congrArg (fun j : ℕ+ => (j : ℕ)) (w.injective he)
      change n + 1 = n + 1 + 1 at hp
      omega
    exact lt_of_le_of_ne (le_of_not_gt hnot) hne
  intro i hi j hj hij
  have hipos := PNat.pos i
  have hjpos := PNat.pos j
  have hi' : (r : ℕ) ≤ (i : ℕ) - 1 := by
    have hir : (r : ℕ) < (i : ℕ) := hi
    omega
  have hj' : (r : ℕ) ≤ (j : ℕ) - 1 := by
    have hjr : (r : ℕ) < (j : ℕ) := hj
    omega
  have hij' : (i : ℕ) - 1 < (j : ℕ) - 1 := by
    have hijNat : (i : ℕ) < (j : ℕ) := hij
    omega
  have hinc := hf hi' hj' hij'
  change w ⟨(i : ℕ) - 1 + 1, Nat.zero_lt_succ _⟩ <
    w ⟨(j : ℕ) - 1 + 1, Nat.zero_lt_succ _⟩ at hinc
  have hiindex : (⟨(i : ℕ) - 1 + 1, Nat.zero_lt_succ _⟩ : ℕ+) = i := PNat.eq (by
    change (i : ℕ) - 1 + 1 = (i : ℕ)
    omega)
  have hjindex : (⟨(j : ℕ) - 1 + 1, Nat.zero_lt_succ _⟩ : ℕ+) = j := PNat.eq (by
    change (j : ℕ) - 1 + 1 = (j : ℕ)
    omega)
  simpa only [hiindex, hjindex] using hinc

/-- A descent with an increasing tail has a pivot at its last later smaller value. -/
theorem exists_pivot_at_descent {w : FinitaryPerm ℕ+} {r : ℕ+}
    (hr : HasDescent w r) (htail : StrictMonoOn w {j : ℕ+ | r < j}) :
    ∃ s : ℕ+, IncreasingTailPivot w r s := by
  let smaller := (positions w.forwardStability).filter fun j => r < j ∧ w j < w r
  have hnext : r + 1 ∈ smaller := by
    apply Finset.mem_filter.mpr
    refine ⟨(mem_positions _ _).mpr ?_, ?_⟩
    · change (r : ℕ) + 1 ≤ w.forwardStability
      exact Nat.succ_le_of_lt (w.isSupported_forwardStability.descent_lt hr)
    · exact ⟨Nat.lt_succ_self (r : ℕ), hr⟩
  have hnonempty : smaller.Nonempty := ⟨r + 1, hnext⟩
  let s := smaller.max' hnonempty
  have hs := Finset.mem_filter.mp (Finset.max'_mem smaller hnonempty)
  refine ⟨s, ⟨hs.2.1, htail, hs.2.2, ?_⟩⟩
  intro j hsj
  apply lt_of_le_of_ne
  · apply le_of_not_gt
    intro hvalue
    have hrj : r < j := hs.2.1.trans hsj
    have hbound : (j : ℕ) ≤ w.forwardStability :=
      (show IsSuffixNonRecord w r j from ⟨r, le_rfl, hrj, hvalue⟩).le_forward
    have hjmem : j ∈ smaller :=
      Finset.mem_filter.mpr ⟨(mem_positions _ j).mpr hbound, hrj, hvalue⟩
    have hmax : j ≤ s := Finset.le_max' smaller j hjmem
    exact (not_le_of_gt hsj) hmax
  · exact fun he => (ne_of_lt (hs.2.1.trans hsj)) (w.injective he)

/-- A nonidentity finitary permutation has a greatest descent and a strictly increasing tail. -/
theorem exists_descent_with_tail {w : FinitaryPerm ℕ+} (hw : w ≠ 1) :
    ∃ r : ℕ+, HasDescent w r ∧ StrictMonoOn w {j : ℕ+ | r < j} := by
  obtain ⟨i, hi⟩ := exists_descent_of_ne_one w hw
  have hnonempty : w.descentSet.Nonempty := ⟨i, (mem_descentSet w i).mpr hi⟩
  let r := w.descentSet.max' hnonempty
  have hr : HasDescent w r :=
    (mem_descentSet w r).mp (Finset.max'_mem w.descentSet hnonempty)
  refine ⟨r, hr, strictMono_after_last_descent ?_⟩
  intro j hj hdescent
  have hmax : j ≤ r := Finset.le_max' w.descentSet j ((mem_descentSet w j).mpr hdescent)
  exact (not_le_of_gt hj) hmax

/-- Every nonidentity finitary permutation has an increasing-tail pivot. -/
theorem exists_increasingTailPivot {w : FinitaryPerm ℕ+} (hw : w ≠ 1) :
    ∃ r s : ℕ+, IncreasingTailPivot w r s := by
  obtain ⟨r, hr, htail⟩ := exists_descent_with_tail hw
  obtain ⟨s, hs⟩ := exists_pivot_at_descent hr htail
  exact ⟨r, s, hs⟩

/-- A permutation with an increasing-tail pivot is not the identity. -/
theorem IncreasingTailPivot.ne_one {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) : w ≠ 1 := by
  intro he
  have hvalue := h.value_lt
  rw [he, one_apply, one_apply] at hvalue
  exact (not_lt_of_gt h.start_lt) hvalue

/-- Increasing-tail pivots exist exactly for nonidentity finitary permutations. -/
theorem exists_increasingTailPivot_iff (w : FinitaryPerm ℕ+) :
    (∃ r s : ℕ+, IncreasingTailPivot w r s) ↔ w ≠ 1 := by
  constructor
  · rintro ⟨r, s, h⟩
    exact h.ne_one
  · exact exists_increasingTailPivot

end FinitaryPerm
