import SchubertForwardStability.Permutations.Classes.Intervals.BoundaryImages
import SchubertForwardStability.Permutations.Classes.Intervals.RecordFactors

/-! # Bijections onto the two Boolean record boundary fibers

The constructed interval factors provide every inverse image. Overlapping
interval injectivity then gives both restricted product bijections.
-/

namespace FinitaryPerm

open scoped Classical

private theorem initial_pred_mem (n : ℕ) (r : ℕ+) (u : FinitaryPerm ℕ+)
    (hu : u ∈ booleanOn n (positions ((r : ℕ) - 1))) :
    u ∈ booleanOn n (positions (r : ℕ)) := by
  apply booleanOn_mono n (fun k hk => ?_) hu
  rw [mem_positions] at hk ⊢
  exact hk.trans (Nat.sub_le (r : ℕ) 1)

/-- The smaller initial and final factor families map bijectively onto the zero-boundary fiber. -/
theorem booleanBoundaryOne_bijOn (n : ℕ) (r : ℕ+) :
    Set.BijOn (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ => p.1 * p.2)
      ((booleanOn n (positions ((r : ℕ) - 1))).product
        (booleanOn n (positionInterval (r : ℕ) n)) : Set _) (booleanBoundaryOne n r : Set _) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    change p ∈ (booleanOn n (positions ((r : ℕ) - 1))).product
      (booleanOn n (positionInterval (r : ℕ) n)) at hp
    have h := Finset.mem_product.mp hp
    exact (boolean_boundaryOne_product n r p.1 p.2 (initial_pred_mem n r p.1 h.1) h.2).mpr h.1
  · intro p hp q hq he
    change p ∈ (booleanOn n (positions ((r : ℕ) - 1))).product
      (booleanOn n (positionInterval (r : ℕ) n)) at hp
    change q ∈ (booleanOn n (positions ((r : ℕ) - 1))).product
      (booleanOn n (positionInterval (r : ℕ) n)) at hq
    have hP := Finset.mem_product.mp hp
    have hQ := Finset.mem_product.mp hq
    exact booleanInterval_product_injOn n r
      (Finset.mem_product.mpr ⟨initial_pred_mem n r p.1 hP.1, hP.2⟩)
      (Finset.mem_product.mpr ⟨initial_pred_mem n r q.1 hQ.1, hQ.2⟩) he
  · intro w hw
    change w ∈ booleanBoundaryOne n r at hw
    have h := (mem_booleanBoundaryOne n r w).mp hw
    obtain ⟨p, hp1, hp2, he⟩ := boolean_record_factor_exists n w h.1 r h.2.1
    have hSmall := (boolean_boundaryOne_product n r p.1 p.2 hp1 hp2).mp
      (by rw [he]; exact hw)
    exact ⟨p, Finset.mem_product.mpr ⟨hSmall, hp2⟩, he⟩

/-- The two factor differences map bijectively onto the nonzero-boundary record fiber. -/
theorem booleanBoundaryTwo_bijOn (n : ℕ) (r : ℕ+) :
    Set.BijOn (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ => p.1 * p.2)
      (((booleanOn n (positions (r : ℕ)) \ booleanOn n (positions ((r : ℕ) - 1))).product
        (booleanOn n (positionInterval (r : ℕ) n) \
          booleanOn n (positionInterval ((r : ℕ) + 1) n))) : Set _)
      (booleanBoundaryTwo n r : Set _) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    change p ∈ (booleanOn n (positions (r : ℕ)) \ booleanOn n (positions ((r : ℕ) - 1))).product
      (booleanOn n (positionInterval (r : ℕ) n) \
        booleanOn n (positionInterval ((r : ℕ) + 1) n)) at hp
    have h := Finset.mem_product.mp hp
    have hP := Finset.mem_sdiff.mp h.1
    have hQ := Finset.mem_sdiff.mp h.2
    exact (boolean_boundaryTwo_product n r p.1 p.2 hP.1 hQ.1).mpr ⟨hP.2, hQ.2⟩
  · intro p hp q hq he
    have hP := Finset.mem_product.mp hp
    have hQ := Finset.mem_product.mp hq
    exact booleanInterval_product_injOn n r
      (Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp hP.1).1, (Finset.mem_sdiff.mp hP.2).1⟩)
      (Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp hQ.1).1, (Finset.mem_sdiff.mp hQ.2).1⟩) he
  · intro w hw
    change w ∈ booleanBoundaryTwo n r at hw
    have h := (mem_booleanBoundaryTwo n r w).mp hw
    obtain ⟨p, hp1, hp2, he⟩ := boolean_record_factor_exists n w h.1 r h.2.1
    have hSmall := (boolean_boundaryTwo_product n r p.1 p.2 hp1 hp2).mp
      (by rw [he]; exact hw)
    exact ⟨p, Finset.mem_product.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hp1, hSmall.1⟩, Finset.mem_sdiff.mpr ⟨hp2, hSmall.2⟩⟩, he⟩

end FinitaryPerm
