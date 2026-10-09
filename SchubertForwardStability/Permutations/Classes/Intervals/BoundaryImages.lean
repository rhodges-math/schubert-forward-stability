import SchubertForwardStability.Permutations.Classes.Intervals.BoundaryCuts

/-! # Images of the two boundary factor domains

The predecessor-zero image is characterized by the smaller initial family.
The other record image requires both factors to avoid their smaller families.
-/

namespace FinitaryPerm

open scoped Classical

/-- Enlarging a position set enlarges the restricted Boolean family. -/
theorem booleanOn_mono (n : ℕ) {I J : Finset ℕ+} (hIJ : I ⊆ J) :
    booleanOn n I ⊆ booleanOn n J := by
  intro w hw
  have h := (mem_booleanOn _ _ _).mp hw
  exact (mem_booleanOn _ _ _).mpr ⟨h.1, fun k hk => h.2 k (fun hi => hk (hIJ hi))⟩

/-- The first boundary fiber is given by the Boolean, record and zero-symbol conditions. -/
theorem mem_booleanBoundaryOne (n : ℕ) (r : ℕ+) (w : FinitaryPerm ℕ+) :
    w ∈ booleanBoundaryOne n r ↔
      w ∈ boolean n ∧ IsRecord w r ∧ blockTag n w ((r : ℕ) - 1) = .zero := by
  simp only [booleanBoundaryOne, Finset.mem_filter, mem_booleanRecordFiber, and_assoc]

/-- The second boundary fiber is given by the Boolean, record and nonzero-symbol
conditions. -/
theorem mem_booleanBoundaryTwo (n : ℕ) (r : ℕ+) (w : FinitaryPerm ℕ+) :
    w ∈ booleanBoundaryTwo n r ↔
      w ∈ boolean n ∧ IsRecord w r ∧ blockTag n w ((r : ℕ) - 1) ≠ .zero := by
  simp only [booleanBoundaryTwo, Finset.mem_sdiff, mem_booleanRecordFiber,
    mem_booleanBoundaryOne]
  tauto

/-- The first boundary image is equivalent to the smaller initial factor condition. -/
theorem boolean_boundaryOne_product (n : ℕ) (r : ℕ+) (u v : FinitaryPerm ℕ+)
    (hu : u ∈ booleanOn n (positions (r : ℕ)))
    (hv : v ∈ booleanOn n (positionInterval (r : ℕ) n)) :
    u * v ∈ booleanBoundaryOne n r ↔
      u ∈ booleanOn n (positions ((r : ℕ) - 1)) := by
  have hU := (mem_booleanOn _ _ _).mp hu
  have hV := (mem_booleanOn _ _ _).mp hv
  have hs : IsSupported (r : ℕ) u := fun k hk =>
    hU.2 k (by rw [mem_positions]; exact not_le_of_gt hk)
  have hFix : ∀ k : ℕ+, k < r → v k = k := by
    intro k hk
    exact hV.2 k (by rw [mem_positionInterval]; exact fun h => (not_le_of_gt hk) h.2)
  rw [mem_booleanBoundaryOne,
    isRecord_interval_product_iff r u v hs hFix,
    boundary_zero_iff_left_fixed n r u v hu hv,
    mem_booleanOn_initial_pred_iff n r u hu]
  have hBool := boolean_interval_product n r u v hu hv
  tauto

/-- The second boundary image is equivalent to avoiding both smaller factor families. -/
theorem boolean_boundaryTwo_product (n : ℕ) (r : ℕ+) (u v : FinitaryPerm ℕ+)
    (hu : u ∈ booleanOn n (positions (r : ℕ)))
    (hv : v ∈ booleanOn n (positionInterval (r : ℕ) n)) :
    u * v ∈ booleanBoundaryTwo n r ↔
      u ∉ booleanOn n (positions ((r : ℕ) - 1)) ∧
        v ∉ booleanOn n (positionInterval ((r : ℕ) + 1) n) := by
  have hU := (mem_booleanOn _ _ _).mp hu
  have hV := (mem_booleanOn _ _ _).mp hv
  have hs : IsSupported (r : ℕ) u := fun k hk =>
    hU.2 k (by rw [mem_positions]; exact not_le_of_gt hk)
  have hFix : ∀ k : ℕ+, k < r → v k = k := by
    intro k hk
    exact hV.2 k (by rw [mem_positionInterval]; exact fun h => (not_le_of_gt hk) h.2)
  rw [mem_booleanBoundaryTwo, isRecord_interval_product_iff r u v hs hFix]
  simp only [ne_eq,
    boundary_zero_iff_left_fixed n r u v hu hv,
    mem_booleanOn_initial_pred_iff n r u hu,
    mem_booleanOn_interval_next_iff n r v hv]
  have hBool := boolean_interval_product n r u v hu hv
  tauto

end FinitaryPerm
