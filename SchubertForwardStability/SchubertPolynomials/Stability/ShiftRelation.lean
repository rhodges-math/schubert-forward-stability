import SchubertForwardStability.Permutations.Finitary.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.PNat.Basic

/-! # Signed shifts of positive-index permutations

## Main definitions

* `SignedShift`: insertion or removal of initial fixed positions, with translated values.

## Main results

A signed shift determines its target uniquely. Zero shift is equality, identity is
fixed by every shift, and reversing a shift negates its integer amount.

## Implementation notes

The relation explicitly fixes every position removed by a negative shift and every
position inserted by a positive shift. Translation is stated using integer casts.
-/

namespace FinitaryPerm

/-- A signed shift removes only fixed positions, inserts fixed positions and translates values. -/
structure SignedShift (k : ℤ) (u v : FinitaryPerm ℕ+) : Prop where
  /-- Every original position translated out of the positive indices is fixed. -/
  removed_fixed : ∀ i : ℕ+, ((i : ℕ) : ℤ) + k ≤ 0 → u i = i
  /-- Every positive position inserted before the translated original indices is fixed. -/
  inserted_fixed : ∀ j : ℕ+, ((j : ℕ) : ℤ) ≤ k → v j = j
  /-- Positions and values both translate by the signed integer amount. -/
  translate : ∀ i j : ℕ+, ((j : ℕ) : ℤ) = ((i : ℕ) : ℤ) + k →
    ((v j : ℕ) : ℤ) = ((u i : ℕ) : ℤ) + k

/-- A signed shift has at most one target permutation. -/
theorem SignedShift.unique {k : ℤ} {u v w : FinitaryPerm ℕ+}
    (h : SignedShift k u v) (h' : SignedShift k u w) : v = w := by
  apply ext
  intro j
  by_cases hj : ((j : ℕ) : ℤ) ≤ k
  · exact (h.inserted_fixed j hj).trans (h'.inserted_fixed j hj).symm
  · have hp : 0 < (((j : ℕ) : ℤ) - k).toNat := by omega
    let i : ℕ+ := ⟨(((j : ℕ) : ℤ) - k).toNat, hp⟩
    have he : ((j : ℕ) : ℤ) = ((i : ℕ) : ℤ) + k := by
      change ((j : ℕ) : ℤ) = ((((j : ℕ) : ℤ) - k).toNat : ℤ) + k
      omega
    have hv := h.translate i j he
    have hw := h'.translate i j he
    apply PNat.eq
    omega

/-- Every permutation is its own zero shift. -/
theorem SignedShift.zero (u : FinitaryPerm ℕ+) : SignedShift 0 u u := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hp := i.pos
    omega
  · intro j hj
    have hp := j.pos
    omega
  · intro i j hij
    have he : i = j := by
      apply PNat.eq
      omega
    subst j
    omega

/-- Identity is fixed by every signed shift. -/
theorem SignedShift.one (k : ℤ) : SignedShift k (1 : FinitaryPerm ℕ+) 1 := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  intro i j hij
  simpa only [one_apply] using hij

/-- A zero signed shift is exactly equality of its source and target. -/
theorem signedShift_zero_iff (u v : FinitaryPerm ℕ+) : SignedShift 0 u v ↔ u = v := by
  constructor
  · intro h
    exact (SignedShift.zero u).unique h
  · rintro rfl
    exact SignedShift.zero u

/-- The only signed shift of identity is identity. -/
theorem SignedShift.eq_one {k : ℤ} {v : FinitaryPerm ℕ+}
    (h : SignedShift k (1 : FinitaryPerm ℕ+) v) : v = 1 := h.unique (SignedShift.one k)

/-- Reversing a signed shift negates its amount. -/
theorem SignedShift.symm {k : ℤ} {u v : FinitaryPerm ℕ+}
    (h : SignedShift k u v) : SignedShift (-k) v u := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    exact h.inserted_fixed j (by omega)
  · intro i hi
    exact h.removed_fixed i (by omega)
  · intro j i hij
    have hv := h.translate i j (by omega)
    omega

end FinitaryPerm
