import SchubertForwardStability.Permutations.Classes.Patterns.PatternMaxFibers
import SchubertForwardStability.Permutations.Classes.Patterns.PatternJoinRecords
import SchubertForwardStability.Permutations.Statistics.RecordMaximum
import SchubertForwardStability.Permutations.Classes.Patterns.PatternRecords

/-! # Record fibers of lower-left maximum joins

The lower-left join is a bijection from the product of a `231` record fiber of size `a` and
the `231`-avoiders of size `b` onto the `231` record fiber of size `a+b+1` whose record set
also contains `a+1`. Hence the fiber sizes multiply.
-/

namespace PermutationPattern

open FinitaryPerm
open scoped Classical

/-- Joining a prescribed left record fiber and an arbitrary right avoider is bijective. -/
theorem recordFiber_joinLow_bij (a b : ℕ) (R : Finset ℕ+)
    (hR : R ⊆ positions a) :
    Set.BijOn (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ => joinLow a b p.1 p.2)
      ((recordFiber a p231 R).product (avoiding b p231) : Set _)
      (recordFiber (a + b + 1) p231 (insert a.succPNat R) : Set _) := by
  have hrR : a.succPNat ∉ R := by
    intro hr
    have h := (mem_positions a a.succPNat).mp (hR hr)
    change a + 1 ≤ a at h
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
    obtain ⟨huA, huR⟩ := (mem_recordFiber _ _ _ _).mp hu
    have huS := ((mem_avoiding _ _ _).mp huA).1
    have hvS := ((mem_avoiding _ _ _).mp hv).1
    refine (mem_recordFiber _ _ _ _).mpr
      ⟨(joinLow_avoiding231_iff a b p.1 p.2 huS hvS).mpr ⟨huA, hv⟩, ?_⟩
    rw [joinLow_recordSet a b p.1 p.2 huS hvS, huR]
  · intro p hp q hq hEqual
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
    obtain ⟨hu', hv'⟩ := Finset.mem_product.mp hq
    have h := joinLow_factors_eq a b p.1 p.2 q.1 q.2
      ((mem_avoiding _ _ _).mp ((mem_recordFiber _ _ _ _).mp hu).1).1
      ((mem_avoiding _ _ _).mp hv).1
      ((mem_avoiding _ _ _).mp ((mem_recordFiber _ _ _ _).mp hu').1).1
      ((mem_avoiding _ _ _).mp hv').1 hEqual
    exact Prod.ext h.1 h.2
  · intro w hw
    obtain ⟨hwA, hwR⟩ := (mem_recordFiber _ _ _ _).mp hw
    have hwS := ((mem_avoiding _ _ _).mp hwA).1
    have hr : a.succPNat ∈ recordSet (a + b + 1) w := by rw [hwR]; simp
    have hLast : ∀ j ∈ recordSet (a + b + 1) w, j ≤ a.succPNat := by
      intro j hj
      rw [hwR] at hj
      obtain he | hjR := Finset.mem_insert.mp hj
      · exact he.le
      · have h := (mem_positions a j).mp (hR hjR)
        change (j : ℕ) ≤ a + 1
        omega
    have hm := lastRecord_value (a + b + 1) w hwS a.succPNat hr hLast
    obtain ⟨u, v, hu, hv, hEqual⟩ := exists_joinLow_avoiding231 a b w hwA hm
    have huS := ((mem_avoiding _ _ _).mp hu).1
    have hvS := ((mem_avoiding _ _ _).mp hv).1
    have hRecords : insert a.succPNat (recordSet a u) = insert a.succPNat R := by
      rw [← joinLow_recordSet a b u v huS hvS, ← hEqual]
      exact hwR
    have hrU : a.succPNat ∉ recordSet a u := by
      intro h
      have hx := ((mem_recordSet _ _ _).mp h).1
      change a + 1 ≤ a at hx
      omega
    have huR : recordSet a u = R := by
      have h := congrArg (fun S : Finset ℕ+ => S.erase a.succPNat) hRecords
      simpa only [Finset.erase_insert hrU, Finset.erase_insert hrR] using h
    exact ⟨(u, v), Finset.mem_product.mpr
      ⟨(mem_recordFiber _ _ _ _).mpr ⟨hu, huR⟩, hv⟩, hEqual.symm⟩

/-- Prescribing the joined record set gives the product of the two factor sizes. -/
theorem card_recordFiber_joinLow (a b : ℕ) (R : Finset ℕ+)
    (hR : R ⊆ positions a) :
    recordFiberCard (a + b + 1) p231 (insert a.succPNat R) =
      recordFiberCard a p231 R * (avoiding b p231).card := by
  have h := recordFiber_joinLow_bij a b R hR
  have hCard := Finset.card_nbij _ h.1 h.2.1 h.2.2
  simpa only [recordFiberCard, Finset.product_eq_sprod, Finset.card_product] using hCard.symm

end PermutationPattern
