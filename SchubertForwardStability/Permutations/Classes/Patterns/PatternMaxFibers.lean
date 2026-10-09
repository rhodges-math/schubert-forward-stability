import SchubertForwardStability.Permutations.Classes.Patterns.PatternFactors
import SchubertForwardStability.Permutations.Classes.Patterns.PatternJoinInjective

/-! # Maximum-position fibers of Catalan avoidance families

`maximumFiber n π r` is the set of `π`-avoiders of size `n` with the value `n` at position
`r`. For `231`, the lower-left join is a bijection from pairs of avoiders of sizes `a` and
`b` onto the fiber with maximum at `a+1`, so the size of the fiber is a product.
-/

namespace PermutationPattern

open FinitaryPerm
open scoped Classical

/-- The avoidance fiber where a specified position carries the largest ambient value. -/
noncomputable def maximumFiber {k : ℕ} (n : ℕ) (π : PermutationPattern k)
    (r : ℕ+) : Finset (FinitaryPerm ℕ+) :=
  (avoiding n π).filter fun w => (w r : ℕ) = n

/-- Membership in the maximum fiber means avoidance and the value `n` at position `r`. -/
@[simp]
theorem mem_maximumFiber {k : ℕ} (n : ℕ) (π : PermutationPattern k)
    (r : ℕ+) (w : FinitaryPerm ℕ+) :
    w ∈ maximumFiber n π r ↔ w ∈ avoiding n π ∧ (w r : ℕ) = n := by
  simp only [maximumFiber, Finset.mem_filter]

/-- Joining two `231`-avoiders bijects their product with a specified maximum fiber. -/
theorem maximumFiber_joinLow_bij (a b : ℕ) :
    Set.BijOn (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ => joinLow a b p.1 p.2)
      (((avoiding a p231).product (avoiding b p231)) : Set _)
      (maximumFiber (a + b + 1) p231 a.succPNat : Set _) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
    have huS := ((mem_avoiding _ _ _).mp hu).1
    have hvS := ((mem_avoiding _ _ _).mp hv).1
    refine (mem_maximumFiber _ _ _ _).mpr
      ⟨(joinLow_avoiding231_iff a b p.1 p.2 huS hvS).mpr ⟨hu, hv⟩, ?_⟩
    rw [joinLow_apply_max a b p.1 p.2 huS hvS]
    rfl
  · intro p hp q hq hEqual
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
    obtain ⟨hu', hv'⟩ := Finset.mem_product.mp hq
    have h := joinLow_factors_eq a b p.1 p.2 q.1 q.2
      ((mem_avoiding _ _ _).mp hu).1 ((mem_avoiding _ _ _).mp hv).1
      ((mem_avoiding _ _ _).mp hu').1 ((mem_avoiding _ _ _).mp hv').1 hEqual
    exact Prod.ext h.1 h.2
  · intro w hw
    obtain ⟨hAvoid, hm⟩ := (mem_maximumFiber _ _ _ _).mp hw
    obtain ⟨u, v, hu, hv, hEqual⟩ := exists_joinLow_avoiding231 a b w hAvoid hm
    exact ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, hEqual.symm⟩

/-- The `231` maximum-position fiber has the product cardinality of its two factors. -/
theorem card_maximumFiber_joinLow (a b : ℕ) :
    (maximumFiber (a + b + 1) p231 a.succPNat).card =
      (avoiding a p231).card * (avoiding b p231).card := by
  have h := maximumFiber_joinLow_bij a b
  have hCard := Finset.card_nbij _ h.1 h.2.1 h.2.2
  simpa only [Finset.product_eq_sprod, Finset.card_product] using hCard.symm

end PermutationPattern
