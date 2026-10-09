import SchubertForwardStability.Permutations.Classes.Intervals.IntervalWords
import SchubertForwardStability.Permutations.Classes.Intervals.IntervalEndpoints

/-! # Products at an overlapping position

The two selected words occupy disjoint generator intervals, so their product
is Boolean. A record at the shared position has a pointwise endpoint criterion.
-/

namespace FinitaryPerm

/-- Products of initial and final Boolean factors sharing one position are Boolean. -/
theorem boolean_interval_product (n : ℕ) (r : ℕ+) (u v : FinitaryPerm ℕ+)
    (hu : u ∈ booleanOn n (positions (r : ℕ)))
    (hv : v ∈ booleanOn n (positionInterval (r : ℕ) n)) : u * v ∈ boolean n := by
  have hU := (mem_booleanOn_initial_word n r u).mp hu
  have hV := (mem_booleanOn_interval_word n r v).mp hv
  have hBoolU := (mem_boolean _ _).mp hU.1
  have hBoolV := (mem_boolean _ _).mp hV.1
  have hDis : List.Disjoint u.lexFirstReducedWord v.lexFirstReducedWord := by
    apply List.disjoint_left.mpr
    intro i hi hvi
    exact (not_lt_of_ge (hV.2 i hvi)) (hU.2 i hi)
  have hN := hBoolU.2.lexFirst_nodup.append hBoolV.2.lexFirst_nodup hDis
  have hUpper : ∀ i ∈ u.lexFirstReducedWord ++ v.lexFirstReducedWord, (i : ℕ) < n := by
    intro i hi
    rcases List.mem_append.mp hi with h | h
    · exact lexFirst_letter_bound u hBoolU.1 i h
    · exact lexFirst_letter_bound v hBoolV.1 i h
  have h := wordProduct_mem_boolean n _ hN hUpper
  simpa only [wordProduct_append, (isReducedWordIn_lexFirst u).1.1,
    (isReducedWordIn_lexFirst v).1.1] using h

/-- A record at the shared position occurs exactly in the two endpoint cases. -/
theorem isRecord_interval_product_iff (r : ℕ+) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported (r : ℕ) u) (hv : ∀ k : ℕ+, k < r → v k = k) :
    IsRecord (u * v) r ↔ u r = r ∨ v r ≠ r := by
  have hImage : r ≤ v r := le_of_not_gt fun h =>
    (ne_of_lt h) (v.injective (hv (v r) h))
  have hHighRecord (hNe : v r ≠ r) : IsRecord (u * v) r := by
    have hHigh : r < v r := lt_of_le_of_ne hImage (fun he => hNe he.symm)
    intro k hk
    rw [mul_apply, hv k hk, mul_apply, hu (v r) hHigh]
    exact lt_of_le_of_lt ((hu.apply_le_iff k).mpr hk.le) hHigh
  constructor
  · intro hr
    by_cases hFixed : v r = r
    · left
      apply (hu.isRecord_last_iff r).mp
      intro k hk
      have h := hr k hk
      simpa only [mul_apply, hv k hk, hFixed] using h
    · exact Or.inr hFixed
  · rintro (hFixed | hNe)
    · by_cases hV : v r = r
      · intro k hk
        simpa only [mul_apply, hv k hk, hV] using
          (hu.isRecord_last_iff r).mpr hFixed k hk
      · exact hHighRecord hV
    · exact hHighRecord hNe

end FinitaryPerm
