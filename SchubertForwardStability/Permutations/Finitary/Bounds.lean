import SchubertForwardStability.Permutations.Finitary.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-! # Support bounds on positive indices

## Main definitions

* `IsSupported`: a permutation fixes every position above a natural bound.
* `forwardStability`: the least positive bound containing the moved support.

## Main results

`forwardStability_le_iff` characterizes the least bound, and inversion leaves it unchanged.

## Implementation notes

Positions are positive natural numbers; ambient sizes and bounds are natural numbers.
Forward stability is at least one, including for the identity permutation.
-/

namespace FinitaryPerm

/-- A permutation is supported in the first `n` positive positions. -/
def IsSupported (n : ℕ) (w : FinitaryPerm ℕ+) : Prop :=
  ∀ j : ℕ+, n < (j : ℕ) → w j = j

/-- Increasing a support bound preserves support containment. -/
theorem IsSupported.mono {m n : ℕ} {w : FinitaryPerm ℕ+}
    (h : IsSupported m w) (hmn : m ≤ n) : IsSupported n w :=
  fun j hj => h j (lt_of_le_of_lt hmn hj)

/-- The identity is supported in every initial interval. -/
@[simp]
theorem isSupported_one (n : ℕ) : IsSupported n (1 : FinitaryPerm ℕ+) :=
  fun _ _ => rfl

/-- A permutation is supported in the empty initial interval exactly when it is identity. -/
theorem isSupported_zero_iff (w : FinitaryPerm ℕ+) : IsSupported 0 w ↔ w = 1 := by
  constructor
  · intro h
    apply ext
    intro j
    exact h j (PNat.pos j)
  · rintro rfl
    exact isSupported_one 0

/-- Products preserve a common support bound. -/
theorem IsSupported.mul {n : ℕ} {w v : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (hv : IsSupported n v) : IsSupported n (w * v) := by
  intro j hj
  rw [mul_apply, hv j hj, hw j hj]

/-- The inverse preserves a support bound. -/
theorem IsSupported.inv {n : ℕ} {w : FinitaryPerm ℕ+}
    (h : IsSupported n w) : IsSupported n w⁻¹ := by
  intro j hj
  have he := congrArg (fun a => w⁻¹ a) (h j hj)
  simpa only [inv_apply_apply] using he.symm

/-- A permutation supported in an initial interval preserves that interval. -/
theorem IsSupported.apply_le_iff {n : ℕ} {w : FinitaryPerm ℕ+}
    (h : IsSupported n w) (j : ℕ+) : (w j : ℕ) ≤ n ↔ (j : ℕ) ≤ n := by
  constructor
  · intro hw
    by_contra hj
    have he := h j (lt_of_not_ge hj)
    rw [he] at hw
    exact hj hw
  · intro hj
    by_contra hw
    have he : w (w j) = w j := h (w j) (lt_of_not_ge hw)
    have hjw : w j = j := w.injective he
    exact hw (by rw [hjw]; exact hj)

noncomputable section

/-- The greatest moved position, or zero when no point is moved. -/
def supportBound (w : FinitaryPerm ℕ+) : ℕ := w.movedPoints.sup fun j => (j : ℕ)

/-- A support bound is at most `n` exactly when all larger points are fixed. -/
theorem supportBound_le_iff (w : FinitaryPerm ℕ+) (n : ℕ) :
    w.supportBound ≤ n ↔ IsSupported n w := by
  rw [supportBound, Finset.sup_le_iff]
  constructor
  · intro h j hj
    by_contra hm
    exact (not_le_of_gt hj) (h j ((mem_movedPoints _ _).mpr hm))
  · intro h j hj
    by_contra hn
    exact (mem_movedPoints _ _).mp hj (h j (lt_of_not_ge hn))

/-- Every point beyond the greatest moved position is fixed. -/
theorem isSupported_supportBound (w : FinitaryPerm ℕ+) : IsSupported w.supportBound w :=
  (supportBound_le_iff w _).mp le_rfl

/-- Inverting a permutation does not change its greatest moved position. -/
@[simp]
theorem supportBound_inv (w : FinitaryPerm ℕ+) : w⁻¹.supportBound = w.supportBound := by
  simp only [supportBound, movedPoints_inv]

/-- The identity's greatest moved position is zero. -/
@[simp]
theorem supportBound_one : supportBound (1 : FinitaryPerm ℕ+) = 0 := by
  simp only [supportBound, movedPoints_one, Finset.sup_empty, Nat.bot_eq_zero]

/-- The least positive ambient size containing a finitary permutation. -/
def forwardStability (w : FinitaryPerm ℕ+) : ℕ := max 1 w.supportBound

/-- Forward stability is always positive. -/
theorem one_le_forwardStability (w : FinitaryPerm ℕ+) : 1 ≤ w.forwardStability :=
  le_max_left _ _

/-- Forward stability is bounded by `n` precisely for permutations supported there,
provided `n` is positive. -/
theorem forwardStability_le_iff (w : FinitaryPerm ℕ+) {n : ℕ} (hn : 1 ≤ n) :
    w.forwardStability ≤ n ↔ IsSupported n w := by
  rw [forwardStability, max_le_iff, and_iff_right hn, supportBound_le_iff]

/-- A permutation fixes every position beyond its forward stability. -/
theorem isSupported_forwardStability (w : FinitaryPerm ℕ+) :
    IsSupported w.forwardStability w :=
  (forwardStability_le_iff w w.one_le_forwardStability).mp le_rfl

/-- The identity has forward stability one. -/
@[simp]
theorem forwardStability_one : forwardStability (1 : FinitaryPerm ℕ+) = 1 := by
  simp only [forwardStability, supportBound_one, max_eq_left (Nat.zero_le 1)]

/-- Inversion preserves forward stability. -/
@[simp]
theorem forwardStability_inv (w : FinitaryPerm ℕ+) :
    w⁻¹.forwardStability = w.forwardStability := by
  simp only [forwardStability, supportBound_inv]

/-- The support bound of a product is no larger than the greater input bound. -/
theorem forwardStability_mul_le (w v : FinitaryPerm ℕ+) :
    (w * v).forwardStability ≤ max w.forwardStability v.forwardStability := by
  apply (forwardStability_le_iff _
    (w.one_le_forwardStability.trans (le_max_left _ _))).mpr
  exact (w.isSupported_forwardStability.mono (le_max_left _ _)).mul
    (v.isSupported_forwardStability.mono (le_max_right _ _))

end

end FinitaryPerm
