import SchubertForwardStability.Paper.Boolean.TagSuffixEvents
import SchubertForwardStability.StrongMixing.MarkovChains.TwoStateExpectations

/-! # Contraction of distant suffix-event probabilities

Dropping a fixed number of initial tags gives a future-event probability
under either boundary state. Exact suffix recursion and two-state contraction
bound the difference by one sixth to the number of dropped positions.
-/

open FinitaryPerm StrongMixing
open scoped BigOperators

namespace RecordStability

/-- Drop the first `g` symbols from a word of length `m+g`, retaining `m` symbols. -/
def tagDrop (m : ℕ) : (g : ℕ) → (Fin (m + g) → BlockTag) → Fin m → BlockTag
  | 0, T => T
  | g + 1, T => tagDrop m g (Fin.tail T)

/-- The dropped word's coordinate is the original coordinate shifted by the
number of removed initial symbols. -/
theorem tagDrop_apply (m g : ℕ) (T : Fin (m + g) → BlockTag) (j : Fin m) :
    tagDrop m g T j = T ⟨g + j.val, by omega⟩ := by
  induction g with
  | zero =>
    change T j = T ⟨0 + j.val, _⟩
    congr 1
    apply Fin.ext
    simp
  | succ g ih =>
    rw [tagDrop, ih]
    change T (⟨g + j.val, _⟩ : Fin (m + g)).succ = T ⟨g + 1 + j.val, _⟩
    congr 1
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

/-- A distant suffix event's probability is the uniform compatible completion
probability after removing its fixed initial gap. -/
noncomputable def tagFutureEventProb (m g : ℕ) (B : Set (Fin m → BlockTag))
    (present : Bool) : ℝ :=
  tagSuffixEventProb (m + g) present {T | tagDrop m g T ∈ B}

/-- Every distant suffix-event probability lies in the unit interval. -/
theorem tagFutureEventProb_bounds (m g : ℕ) (B : Set (Fin m → BlockTag)) (present : Bool) :
    0 ≤ tagFutureEventProb m g B present ∧ tagFutureEventProb m g B present ≤ 1 :=
  tagSuffixEventProb_bounds _ _ _

/-- Removing one additional initial tag averages the later event probabilities
against the exact completion-weighted two-state kernel. -/
theorem tagFutureEventProb_succ (m g : ℕ) (B : Set (Fin m → BlockTag)) (present : Bool) :
    tagFutureEventProb m (g + 1) B present =
      ∑ b : Bool, tagKernel (m + g) present b * tagFutureEventProb m g B b := by
  exact tagSuffixEventProb_tail (m + g) present {T | tagDrop m g T ∈ B}

/-- The probabilities of a future event under absent and present boundary
states differ by at most `(1/6)^g`, uniformly in its retained length and event. -/
theorem tagFutureEventProb_contract (m g : ℕ) (B : Set (Fin m → BlockTag)) :
    |tagFutureEventProb m g B false - tagFutureEventProb m g B true| ≤ (1 / 6 : ℝ) ^ g := by
  induction g with
  | zero =>
    have h0 := tagFutureEventProb_bounds m 0 B false
    have h1 := tagFutureEventProb_bounds m 0 B true
    simp only [pow_zero]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  | succ g ih =>
    rw [tagFutureEventProb_succ, tagFutureEventProb_succ,
      binary_expectation_difference _ _ _ (tagKernel_row_sum _ false)
        (tagKernel_row_sum _ true), abs_mul]
    calc
      _ ≤ (1 / 6 : ℝ) * (1 / 6 : ℝ) ^ g :=
        mul_le_mul (tagKernel_false_diff_le _) ih (abs_nonneg _) (by norm_num)
      _ = _ := by rw [pow_succ]; ring

end RecordStability
