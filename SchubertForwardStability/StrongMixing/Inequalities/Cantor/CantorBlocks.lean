import Mathlib.Data.Int.Interval
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite Cantor blocks of integer coordinates

Two equal-sized child intervals are retained at the ends of their parent interval.
The construction is repeated a finite number of times. Exact cardinality and spacing
hold for every nonnegative integer length schedule satisfying the child-size
constraint.
-/

namespace StrongMixing

/-- The finite integer Cantor block with length schedule `L`, initial level `j`,
left endpoint `a`, and depth `d`. At each step two child intervals of length
`L (j + 1)` are retained at the two ends of the current interval of length `L j`.
Depth zero retains the entire half-open integer interval. -/
def cantorBlock (L : ℕ → ℕ) (j : ℕ) (a : ℤ) : ℕ → Finset ℤ
  | 0 => Finset.Ico a (a + L j)
  | d + 1 => cantorBlock L (j + 1) a d ∪
      cantorBlock L (j + 1) (a + L j - L (j + 1)) d

/-- Every retained coordinate belongs to its initial half-open interval, provided
the two equal-sized child intervals fit within each parent. Zero lengths and
zero depth are allowed. -/
theorem cantorBlock_subset (L : ℕ → ℕ) (hL : ∀ j, 2 * L (j + 1) ≤ L j)
    (j : ℕ) (a : ℤ) (d : ℕ) : cantorBlock L j a d ⊆ Finset.Ico a (a + L j) := by
  induction d generalizing j a with
  | zero => exact Finset.Subset.refl _
  | succ d ih =>
    intro x hx
    rw [cantorBlock, Finset.mem_union] at hx
    have h := hL j
    have hc : (L (j + 1) : ℤ) ≤ L j := by exact_mod_cast (by omega : L (j + 1) ≤ L j)
    rcases hx with hx | hx
    · have hm := Finset.mem_Ico.mp (ih (j + 1) a hx)
      exact Finset.mem_Ico.mpr ⟨hm.1, by omega⟩
    · have hm := Finset.mem_Ico.mp (ih (j + 1) (a + L j - L (j + 1)) hx)
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

/-- The two recursively retained sibling blocks are disjoint whenever two child
lengths fit in the parent. This includes empty siblings and adjacent siblings. -/
theorem cantorBlock_disjoint (L : ℕ → ℕ) (hL : ∀ j, 2 * L (j + 1) ≤ L j)
    (j : ℕ) (a : ℤ) (d : ℕ) :
    Disjoint (cantorBlock L (j + 1) a d)
      (cantorBlock L (j + 1) (a + L j - L (j + 1)) d) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hl := Finset.mem_Ico.mp (cantorBlock_subset L hL (j + 1) a d hx)
  have hr := Finset.mem_Ico.mp
    (cantorBlock_subset L hL (j + 1) (a + L j - L (j + 1)) d hy)
  have h : 2 * (L (j + 1) : ℤ) ≤ L j := by exact_mod_cast hL j
  omega

/-- The retained integer Cantor block has exactly `2 ^ d * L (j + d)` coordinates.
The formula is independent of translation and remains valid when terminal lengths
vanish, since all sibling blocks are disjoint. -/
theorem cantorBlock_card (L : ℕ → ℕ) (hL : ∀ j, 2 * L (j + 1) ≤ L j)
    (j : ℕ) (a : ℤ) (d : ℕ) :
    (cantorBlock L j a d).card = 2 ^ d * L (j + d) := by
  induction d generalizing j a with
  | zero => simp [cantorBlock]
  | succ d ih =>
    rw [cantorBlock, Finset.card_union_of_disjoint (cantorBlock_disjoint L hL j a d)]
    rw [ih, ih]
    have hj : j + 1 + d = j + (d + 1) := by omega
    rw [hj, pow_succ]
    ring

/-- The retained block has no more coordinates than its initial interval. -/
theorem cantorBlock_card_le (L : ℕ → ℕ) (hL : ∀ j, 2 * L (j + 1) ≤ L j)
    (j : ℕ) (a : ℤ) (d : ℕ) : (cantorBlock L j a d).card ≤ L j := by
  simpa using Finset.card_le_card (cantorBlock_subset L hL j a d)

/-- Sibling Cantor blocks lie on opposite sides of the natural mixing cut
`a + L (j + 1) - 1`, at natural lag `L j - 2 * L (j + 1) + 1`. Thus even
adjacent nonempty children have lag one, and deleted coordinates increase the lag.
Both inclusions hold without a positive-length assumption. -/
theorem cantorBlock_separated (L : ℕ → ℕ) (hL : ∀ j, 2 * L (j + 1) ≤ L j)
    (j : ℕ) (a : ℤ) (d : ℕ) :
    (∀ x ∈ cantorBlock L (j + 1) a d, x ≤ a + L (j + 1) - 1) ∧
      (∀ y ∈ cantorBlock L (j + 1) (a + L j - L (j + 1)) d,
        a + L (j + 1) - 1 + ((L j - 2 * L (j + 1) + 1 : ℕ) : ℤ) ≤ y) := by
  constructor
  · intro x hx
    have hl := Finset.mem_Ico.mp (cantorBlock_subset L hL (j + 1) a d hx)
    omega
  · intro y hy
    have hr := Finset.mem_Ico.mp
      (cantorBlock_subset L hL (j + 1) (a + L j - L (j + 1)) d hy)
    have h := hL j
    omega

end StrongMixing
