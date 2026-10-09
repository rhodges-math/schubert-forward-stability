import SchubertForwardStability.Permutations.Classes.Intervals.BoundaryBijections

/-! # Cardinalities of the two record boundary fibers

The two boundary fibers form a disjoint partition of the Boolean
record fiber. Their product bijections transfer cardinality exactly.
-/

namespace FinitaryPerm

open scoped Classical

/-- The zero-boundary fiber is contained in the full record fiber. -/
theorem booleanBoundaryOne_subset (n : ℕ) (r : ℕ+) :
    booleanBoundaryOne n r ⊆ booleanRecordFiber n r := fun _ h =>
  (Finset.mem_filter.mp h).1

/-- The nonzero-boundary fiber is contained in the full record fiber. -/
theorem booleanBoundaryTwo_subset (n : ℕ) (r : ℕ+) :
    booleanBoundaryTwo n r ⊆ booleanRecordFiber n r := fun _ h =>
  (Finset.mem_sdiff.mp h).1

/-- The two boundary record fibers are disjoint. -/
theorem booleanBoundary_disjoint (n : ℕ) (r : ℕ+) :
    Disjoint (booleanBoundaryOne n r) (booleanBoundaryTwo n r) := by
  apply Finset.disjoint_left.mpr
  intro w hOne hTwo
  exact (Finset.mem_sdiff.mp hTwo).2 hOne

/-- The two boundary fibers partition the full Boolean record fiber. -/
theorem booleanBoundary_union (n : ℕ) (r : ℕ+) :
    booleanRecordFiber n r = booleanBoundaryOne n r ∪ booleanBoundaryTwo n r := by
  ext w
  simp only [Finset.mem_union, booleanBoundaryTwo, Finset.mem_sdiff]
  have h : w ∈ booleanBoundaryOne n r → w ∈ booleanRecordFiber n r :=
    fun hw => booleanBoundaryOne_subset n r hw
  tauto

/-- The zero-boundary record count is the product of the two factor-family counts. -/
theorem card_booleanBoundaryOne (n : ℕ) (r : ℕ+) :
    (booleanBoundaryOne n r).card =
      (booleanOn n (positions ((r : ℕ) - 1))).card *
        (booleanOn n (positionInterval (r : ℕ) n)).card := by
  have h := (Finset.card_nbij (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ => p.1 * p.2)
    (booleanBoundaryOne_bijOn n r).1 (booleanBoundaryOne_bijOn n r).2.1
    (booleanBoundaryOne_bijOn n r).2.2).symm
  rw [Finset.product_eq_sprod, Finset.card_product] at h
  exact h

/-- The nonzero-boundary record count is the product of the two difference-family counts. -/
theorem card_booleanBoundaryTwo (n : ℕ) (r : ℕ+) :
    (booleanBoundaryTwo n r).card =
      (booleanOn n (positions (r : ℕ)) \ booleanOn n (positions ((r : ℕ) - 1))).card *
        (booleanOn n (positionInterval (r : ℕ) n) \
          booleanOn n (positionInterval ((r : ℕ) + 1) n)).card := by
  have h := (Finset.card_nbij (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ => p.1 * p.2)
    (booleanBoundaryTwo_bijOn n r).1 (booleanBoundaryTwo_bijOn n r).2.1
    (booleanBoundaryTwo_bijOn n r).2.2).symm
  rw [Finset.product_eq_sprod, Finset.card_product] at h
  exact h

/-- Every Boolean record count is the sum of its two interval-factor product counts. -/
theorem booleanRecordCount_interval (n : ℕ) (r : ℕ+) :
    booleanRecordCount n r =
      (booleanOn n (positions ((r : ℕ) - 1))).card *
        (booleanOn n (positionInterval (r : ℕ) n)).card +
      (booleanOn n (positions (r : ℕ)) \ booleanOn n (positions ((r : ℕ) - 1))).card *
        (booleanOn n (positionInterval (r : ℕ) n) \
          booleanOn n (positionInterval ((r : ℕ) + 1) n)).card := by
  rw [booleanRecordCount, booleanBoundary_union,
    Finset.card_union_of_disjoint (booleanBoundary_disjoint n r),
    card_booleanBoundaryOne, card_booleanBoundaryTwo]

end FinitaryPerm
