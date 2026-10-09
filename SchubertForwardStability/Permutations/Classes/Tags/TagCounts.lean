import SchubertForwardStability.Permutations.Classes.Tags.BlockTags
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Fib.Basic

/-!
# Boundary-word completion counts

## Main results

Prepending a symbol gives an explicit finite suffix equivalence. Its cardinality
proves the two transfer recurrences and the odd/even Fibonacci completion counts.

## Implementation notes

The alphabet has absent, initial-present and continuing-present symbols. These
results concern its finite language of valid words and include empty suffixes.

-/

namespace FinitaryPerm

open scoped Classical
open scoped BigOperators

noncomputable section

/-- Prepending a symbol changes the continuation boundary to its presence status. -/
theorem validTagSuffix_cons {m : ℕ} (present : Bool) (a : BlockTag)
    (T : Fin m → BlockTag) :
    ValidTagSuffix present (Fin.cons a T) ↔
      (a = .cont → present = true) ∧ ValidTagSuffix (decide (a ≠ .zero)) T := by
  constructor
  · intro h
    constructor
    · intro ha
      obtain (⟨_, hp⟩ | ⟨j, hj, _⟩) := h 0 (by simpa using ha)
      · exact hp
      · simp only [Fin.val_zero] at hj
        have := j.isLt
        omega
    · intro i hi
      obtain (⟨hz, _⟩ | ⟨j, hj, hv⟩) := h i.succ (by simpa using hi)
      · simp only [Fin.val_succ] at hz
        omega
      · by_cases hz : i.val = 0
        · left
          refine ⟨hz, ?_⟩
          have hjz : j = 0 := by
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_zero] at hj ⊢
            omega
          rw [hjz, Fin.cons_zero] at hv
          exact decide_eq_true hv
        · right
          let k : Fin m := ⟨j.val - 1, by have := j.isLt; omega⟩
          have hjk : j = k.succ := by
            apply Fin.ext
            have := j.isLt
            simp only [Fin.val_succ] at hj ⊢
            dsimp [k]
            omega
          refine ⟨k, ?_, ?_⟩
          · simp only [Fin.val_succ] at hj
            dsimp [k]
            omega
          · simpa only [hjk, Fin.cons_succ] using hv
  · rintro ⟨ha, h⟩ i hi
    induction i using Fin.cases with
    | zero =>
      left
      exact ⟨rfl, ha (by simpa using hi)⟩
    | succ i =>
      have hti : T i = .cont := by simpa using hi
      obtain (⟨hz, hp⟩ | ⟨j, hj, hv⟩) := h i hti
      · right
        refine ⟨0, ?_, ?_⟩
        · simp only [Fin.val_zero, Fin.val_succ]
          omega
        · simp only [Fin.cons_zero]
          exact of_decide_eq_true hp
      · right
        exact ⟨j.succ, by simpa only [Fin.val_succ] using congrArg Nat.succ hj,
          by simpa only [Fin.cons_succ] using hv⟩

private def suffixSplit (m : ℕ) (present : Bool) :
    {T : Fin (m + 1) → BlockTag // ValidTagSuffix present T} ≃
      Σ a : {a : BlockTag // a = .cont → present = true},
        {T : Fin m → BlockTag // ValidTagSuffix (decide (a.val ≠ .zero)) T} where
  toFun T := by
    have h := (validTagSuffix_cons present (T.val 0) (Fin.tail T.val)).mp
      (by rw [Fin.cons_self_tail]; exact T.property)
    exact ⟨⟨T.val 0, h.1⟩, ⟨Fin.tail T.val, h.2⟩⟩
  invFun a := ⟨Fin.cons a.1.val a.2.val,
    (validTagSuffix_cons present a.1.val a.2.val).mpr ⟨a.1.property, a.2.property⟩⟩
  left_inv T := Subtype.ext (Fin.cons_self_tail T.val)
  right_inv a := by
    rcases a with ⟨⟨a, ha⟩, ⟨T, hT⟩⟩
    dsimp only
    refine Sigma.ext ?_ ?_
    · apply Subtype.ext
      exact @Fin.cons_zero m (fun _ : Fin (m + 1) => BlockTag) a T
    · apply heq_of_eq
      exact Subtype.ext (@Fin.tail_cons m (fun _ : Fin (m + 1) => BlockTag) a T)

private theorem extensionCount_card (m : ℕ) (present : Bool) :
    extensionCount m present =
      Fintype.card {T : Fin m → BlockTag // ValidTagSuffix present T} := by
  rw [Fintype.card_subtype, extensionCount]

private theorem extensionCount_sum (m : ℕ) (present : Bool) :
    extensionCount (m + 1) present =
      ∑ a ∈ (Finset.univ : Finset BlockTag).filter (fun a => a = .cont → present = true),
        extensionCount m (decide (a ≠ .zero)) := by
  rw [extensionCount_card, Fintype.card_congr (suffixSplit m present), Fintype.card_sigma]
  simp_rw [← extensionCount_card]
  apply Finset.sum_bij (fun a _ => a.val)
  · intro a _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.property⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro a ha
    exact ⟨⟨a, (Finset.mem_filter.mp ha).2⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl

/-- Absent-boundary completion counts satisfy the first transfer recurrence. -/
theorem extensionCount_false_succ (m : ℕ) :
    extensionCount (m + 1) false = extensionCount m false + extensionCount m true := by
  rw [extensionCount_sum]
  change (∑ a ∈ ({.zero, .start, .cont} : Finset BlockTag).filter
    (fun a => a = .cont → false = true), extensionCount m (decide (a ≠ .zero))) = _
  simp [Finset.filter_insert]

/-- Present-boundary completion counts satisfy the second transfer recurrence. -/
theorem extensionCount_true_succ (m : ℕ) :
    extensionCount (m + 1) true = extensionCount m false + 2 * extensionCount m true := by
  rw [extensionCount_sum]
  change (∑ a ∈ ({.zero, .start, .cont} : Finset BlockTag).filter
    (fun a => a = .cont → true = true), extensionCount m (decide (a ≠ .zero))) = _
  simp [Finset.filter_insert]
  omega

private theorem extensionCounts_fib (m : ℕ) :
    extensionCount m false = Nat.fib (2 * m + 1) ∧
      extensionCount m true = Nat.fib (2 * m + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [extensionCount_false_succ, extensionCount_true_succ, ih.1, ih.2]
    have h3 : Nat.fib (2 * (m + 1) + 1) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 2) := by
      have he : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
      have he' : (2 * m + 1) + 1 = 2 * m + 2 := by omega
      rw [he, Nat.fib_add_two, he']
    have h4 : Nat.fib (2 * (m + 1) + 2) =
        Nat.fib (2 * m + 2) + Nat.fib (2 * (m + 1) + 1) := by
      have he : 2 * (m + 1) + 2 = (2 * m + 2) + 2 := by omega
      have he' : (2 * m + 2) + 1 = 2 * (m + 1) + 1 := by omega
      rw [he, Nat.fib_add_two, he']
    constructor
    · exact h3.symm
    · rw [h4, h3]
      omega

/-- Absent-boundary suffixes are counted by odd-index Fibonacci numbers. -/
theorem extensionCount_false_fib (m : ℕ) :
    extensionCount m false = Nat.fib (2 * m + 1) := (extensionCounts_fib m).1

/-- Present-boundary suffixes are counted by even-index Fibonacci numbers. -/
theorem extensionCount_true_fib (m : ℕ) :
    extensionCount m true = Nat.fib (2 * m + 2) := (extensionCounts_fib m).2

/-- Valid boundary words are counted by the same odd-index Fibonacci numbers. -/
theorem card_tagWords (m : ℕ) : (tagWords m).card = Nat.fib (2 * m + 1) := by
  change extensionCount m false = _
  exact extensionCount_false_fib m

end

end FinitaryPerm
