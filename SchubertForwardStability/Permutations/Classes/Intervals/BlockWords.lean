import SchubertForwardStability.Permutations.Classes.Intervals.BooleanBlocks
import Mathlib.Data.List.Range
import Mathlib.Data.List.Nodup

/-! # Decreasing words on positive intervals

The decreasing block has precisely the generators in its endpoint
interval, with no repetitions. Adding the next endpoint prepends that generator.
-/

namespace FinitaryPerm

/-- A decreasing block has interval length, and an inverted interval has length zero. -/
theorem decreasingBlockWord_length (i j : ℕ+) :
    (decreasingBlockWord i j).length = if i ≤ j then (j : ℕ) - (i : ℕ) + 1 else 0 := by
  by_cases h : i ≤ j <;> simp [decreasingBlockWord, h]

/-- Extending a nonempty decreasing interval prepends its new upper endpoint. -/
theorem decreasingBlockWord_succ (i j : ℕ+) (h : i ≤ j) :
    decreasingBlockWord i (j + 1) = (j + 1) :: decreasingBlockWord i j := by
  have hN : (i : ℕ) ≤ (j : ℕ) := h
  have hs : i ≤ j + 1 := by
    change (i : ℕ) ≤ (j : ℕ) + 1
    omega
  have hl : ((j + 1 : ℕ+) : ℕ) - (i : ℕ) + 1 =
      ((j : ℕ) - (i : ℕ) + 1) + 1 := by
    change (j : ℕ) + 1 - (i : ℕ) + 1 = ((j : ℕ) - (i : ℕ) + 1) + 1
    omega
  rw [decreasingBlockWord, ite_eq_left hs, hl, List.range_succ_eq_map, List.map_cons,
    List.map_map, decreasingBlockWord, ite_eq_left h]
  simp only [Function.comp_def, Nat.succ_eq_add_one, Nat.sub_zero, PNat.coe_toPNat']
  congr 1
  apply List.map_congr_left
  intro r _
  change ((j : ℕ) + 1 - (r + 1)).toPNat' = ((j : ℕ) - r).toPNat'
  rw [Nat.add_sub_add_right]

/-- The generators in a decreasing block are exactly those in its closed endpoint interval. -/
theorem mem_decreasingBlockWord (i j k : ℕ+) :
    k ∈ decreasingBlockWord i j ↔ i ≤ k ∧ k ≤ j := by
  by_cases hij : i ≤ j
  · rw [decreasingBlockWord, ite_eq_left hij, List.mem_map]
    have hijN : (i : ℕ) ≤ (j : ℕ) := hij
    have hi := PNat.pos i
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hrN := List.mem_range.mp hr
      have hp : 0 < (j : ℕ) - r := by omega
      constructor
      · change (i : ℕ) ≤ (((j : ℕ) - r).toPNat' : ℕ)
        rw [PNat.toPNat'_coe hp]
        omega
      · change (((j : ℕ) - r).toPNat' : ℕ) ≤ (j : ℕ)
        rw [PNat.toPNat'_coe hp]
        omega
    · rintro ⟨hik, hkj⟩
      have hikN : (i : ℕ) ≤ (k : ℕ) := hik
      have hkjN : (k : ℕ) ≤ (j : ℕ) := hkj
      have hk := PNat.pos k
      refine ⟨(j : ℕ) - (k : ℕ), List.mem_range.mpr (by omega), ?_⟩
      apply PNat.eq
      rw [PNat.toPNat'_coe (by omega : 0 < (j : ℕ) - ((j : ℕ) - (k : ℕ)))]
      omega
  · rw [decreasingBlockWord, ite_eq_right hij]
    constructor
    · intro h
      exact (List.not_mem_nil h).elim
    · rintro ⟨hik, hkj⟩
      exact (hij (hik.trans hkj)).elim

/-- No generator occurs twice in a decreasing block, including an inverted interval. -/
theorem decreasingBlockWord_nodup (i j : ℕ+) : (decreasingBlockWord i j).Nodup := by
  by_cases hij : i ≤ j
  · rw [decreasingBlockWord, ite_eq_left hij]
    apply List.Nodup.map_on _ List.nodup_range
    intro r hr s hs he
    have hrN := List.mem_range.mp hr
    have hsN := List.mem_range.mp hs
    have hijN : (i : ℕ) ≤ (j : ℕ) := hij
    have hi := PNat.pos i
    have hpR : 0 < (j : ℕ) - r := by omega
    have hpS : 0 < (j : ℕ) - s := by omega
    have heN := congrArg PNat.val he
    rw [PNat.toPNat'_coe hpR, PNat.toPNat'_coe hpS] at heN
    omega
  · simp only [decreasingBlockWord, ite_eq_right hij, List.nodup_nil]

/-- A nonempty decreasing interval begins with its upper endpoint. -/
theorem decreasingBlockWord_head (i j : ℕ+) (hij : i ≤ j) :
    ∃ tail : List ℕ+, decreasingBlockWord i j = j :: tail := by
  rw [decreasingBlockWord, ite_eq_left hij, List.range_succ_eq_map, List.map_cons,
    Nat.sub_zero, PNat.coe_toPNat']
  exact ⟨_, rfl⟩

/-- A nonempty decreasing interval ends with its lower endpoint. -/
theorem decreasingBlockWord_snoc (i j : ℕ+) (hij : i ≤ j) :
    ∃ pre : List ℕ+, decreasingBlockWord i j = pre ++ [i] := by
  have hN : (i : ℕ) ≤ (j : ℕ) := hij
  have hval : (j : ℕ) - ((j : ℕ) - (i : ℕ)) = (i : ℕ) := by omega
  rw [decreasingBlockWord, ite_eq_left hij, List.range_succ, List.map_append,
    List.map_singleton, hval, PNat.coe_toPNat']
  exact ⟨_, rfl⟩

end FinitaryPerm
