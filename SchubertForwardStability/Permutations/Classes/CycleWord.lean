import SchubertForwardStability.Permutations.Classes.ReducedWords
import SchubertForwardStability.Permutations.Finitary.Longest

/-! # A descending word between successive longest elements

## Main definitions

* `initialDescendingWord`: the positive adjacent word n, n-1, ..., 1.

## Main results

The word product sends position one to n+1, decreases the other first n+1 positions
by one, and fixes the complement. Its inversion length is n. It is therefore a
reduced expression for the product of the size-n and size-(n+1) longest elements.

## Implementation notes

The word is empty at size zero. Numerical descending order of its letters is
distinct from the length-decreasing sorting-word predicate.
-/

namespace FinitaryPerm

/-- The adjacent word consisting of positive letters n down to one. -/
def initialDescendingWord : ℕ → List ℕ+
  | 0 => []
  | n + 1 => Nat.succPNat n :: initialDescendingWord n

/-- The size-zero descending word is empty. -/
theorem initialDescendingWord_zero : initialDescendingWord 0 = [] := rfl

/-- Increasing the size prepends the next positive letter. -/
theorem initialDescendingWord_succ (n : ℕ) :
    initialDescendingWord (n + 1) = Nat.succPNat n :: initialDescendingWord n := rfl

/-- The initial descending word has exactly n letters. -/
theorem initialDescendingWord_length (n : ℕ) : (initialDescendingWord n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [initialDescendingWord_succ, List.length_cons, ih]

/-- The descending-word product sends position one to the next ambient endpoint. -/
theorem initialDescendingWord_apply_one (n : ℕ) :
    wordProduct (initialDescendingWord n) 1 = Nat.succPNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [initialDescendingWord_succ, wordProduct_cons, mul_apply, ih,
      simpleTransposition_apply_left]
    rfl

/-- The descending-word product fixes every position above n+1. -/
theorem initialDescendingWord_apply_above (n : ℕ) (j : ℕ+) (hj : n + 1 < (j : ℕ)) :
    wordProduct (initialDescendingWord n) j = j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [initialDescendingWord_succ, wordProduct_cons, mul_apply, ih (by omega)]
    change swap (Nat.succPNat n) (Nat.succPNat n + 1) j = j
    apply swap_apply_of_ne
    · intro h
      have hv := congrArg PNat.val h
      change (j : ℕ) = n + 1 at hv
      omega
    · intro h
      have hv := congrArg PNat.val h
      change (j : ℕ) = n + 2 at hv
      omega

/-- The descending-word product decreases each remaining initial position by one. -/
theorem initialDescendingWord_apply_inside (n : ℕ) (j : ℕ+)
    (hjone : 1 < (j : ℕ)) (hj : (j : ℕ) ≤ n + 1) :
    (wordProduct (initialDescendingWord n) j : ℕ) = (j : ℕ) - 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [initialDescendingWord_succ, wordProduct_cons, mul_apply]
    by_cases hold : (j : ℕ) ≤ n + 1
    · have hvalue := ih hold
      have hfix : simpleTransposition (Nat.succPNat n)
          (wordProduct (initialDescendingWord n) j) =
            wordProduct (initialDescendingWord n) j := by
        apply swap_apply_of_ne
        · intro h
          have hv := congrArg PNat.val h
          change (wordProduct (initialDescendingWord n) j : ℕ) = n + 1 at hv
          omega
        · intro h
          have hv := congrArg PNat.val h
          change (wordProduct (initialDescendingWord n) j : ℕ) = n + 2 at hv
          omega
      rw [hfix]
      exact hvalue
    · have hfixed := initialDescendingWord_apply_above n j (by omega)
      have hlast : j = Nat.succPNat n + 1 := by
        apply PNat.eq
        change (j : ℕ) = n + 2
        omega
      rw [hfixed, hlast, simpleTransposition_apply_right]
      change n + 1 = n + 2 - 1
      omega

/-- The descending word is the relative permutation between successive longest elements. -/
theorem initialDescendingWord_product (n : ℕ) :
    wordProduct (initialDescendingWord n) = longestElement n * longestElement (n + 1) := by
  apply ext
  intro j
  apply PNat.eq
  by_cases hone : j = 1
  · subst j
    rw [initialDescendingWord_apply_one, mul_apply]
    have hrev : longestElement (n + 1) 1 = Nat.succPNat n := by
      apply PNat.eq
      rw [longestElement_apply_val (n + 1) 1 (by change 1 ≤ n + 1; omega)]
      change n + 1 + 1 - 1 = n + 1
      omega
    rw [hrev, longestElement_apply_above n _ (by change n < n + 1; omega)]
  · have hjone : 1 < (j : ℕ) := by
      have hjne : (j : ℕ) ≠ 1 := fun h => hone (PNat.eq h)
      have := j.pos
      omega
    by_cases hj : (j : ℕ) ≤ n + 1
    · rw [initialDescendingWord_apply_inside n j hjone hj, mul_apply]
      have hvalue := longestElement_apply_val (n + 1) j hj
      have hbound : (longestElement (n + 1) j : ℕ) ≤ n := by omega
      rw [longestElement_apply_val n _ hbound, hvalue]
      omega
    · rw [initialDescendingWord_apply_above n j (by omega), mul_apply,
        longestElement_apply_above (n + 1) j (by omega),
        longestElement_apply_above n j (by omega)]

/-- The descending-word inversions start at one and end within its ambient interval. -/
theorem initialDescendingWord_inversion_iff (n : ℕ) (i j : ℕ+) :
    (i, j) ∈ (wordProduct (initialDescendingWord n)).inversionSet ↔
      i = 1 ∧ 1 < (j : ℕ) ∧ (j : ℕ) ≤ n + 1 := by
  rw [mem_inversionSet]
  constructor
  · rintro ⟨hij, hvalue⟩
    have hijnat : (i : ℕ) < (j : ℕ) := hij
    have hsupp : IsSupported (n + 1) (wordProduct (initialDescendingWord n)) :=
      initialDescendingWord_apply_above n
    have hj : (j : ℕ) ≤ n + 1 := by
      by_contra h
      exact (not_lt_of_gt (hsupp.isRecord_above (by omega) i hij)) hvalue
    have hjone : 1 < (j : ℕ) := by have := i.pos; omega
    refine ⟨?_, hjone, hj⟩
    by_contra hone
    have hine : (i : ℕ) ≠ 1 := fun h => hone (PNat.eq h)
    have hione : 1 < (i : ℕ) := by have := i.pos; omega
    change (wordProduct (initialDescendingWord n) j : ℕ) <
      (wordProduct (initialDescendingWord n) i : ℕ) at hvalue
    rw [initialDescendingWord_apply_inside n j hjone hj,
      initialDescendingWord_apply_inside n i hione (by omega)] at hvalue
    omega
  · rintro ⟨rfl, hjone, hj⟩
    refine ⟨hjone, ?_⟩
    change (wordProduct (initialDescendingWord n) j : ℕ) <
      (wordProduct (initialDescendingWord n) 1 : ℕ)
    rw [initialDescendingWord_apply_inside n j hjone hj, initialDescendingWord_apply_one]
    change (j : ℕ) - 1 < n + 1
    omega

/-- The inversions of the descending word are indexed by the n positive predecessor positions. -/
theorem initialDescendingWord_inversions (n : ℕ) :
    (wordProduct (initialDescendingWord n)).inversionSet =
      (positions n).image (fun j : ℕ+ => (1, j + 1)) := by
  classical
  ext p
  rcases p with ⟨i, j⟩
  rw [initialDescendingWord_inversion_iff, Finset.mem_image]
  constructor
  · rintro ⟨rfl, hjone, hj⟩
    let k : ℕ+ := ⟨(j : ℕ) - 1, by omega⟩
    refine ⟨k, (mem_positions n k).mpr (by change (j : ℕ) - 1 ≤ n; omega), ?_⟩
    apply Prod.ext
    · rfl
    · apply PNat.eq
      change (j : ℕ) - 1 + 1 = (j : ℕ)
      omega
  · rintro ⟨k, hk, hpair⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    have hkbound := (mem_positions n k).mp hk
    have := k.pos
    refine ⟨rfl, ?_, ?_⟩
    · change 1 < (k : ℕ) + 1
      omega
    · change (k : ℕ) + 1 ≤ n + 1
      omega

/-- The descending-word product has inversion length n. -/
theorem length_initialDescendingWord (n : ℕ) :
    (wordProduct (initialDescendingWord n)).length = n := by
  rw [length, initialDescendingWord_inversions, Finset.card_image_of_injective,
    card_positions]
  intro i j h
  have hv := congrArg (fun p : ℕ+ × ℕ+ => (p.2 : ℕ)) h
  apply PNat.eq
  change (i : ℕ) + 1 = (j : ℕ) + 1 at hv
  omega

/-- The initial descending word is reduced for the successive-longest product. -/
theorem isReduced_initialDescendingWord (n : ℕ) :
    IsReducedWord (longestElement n * longestElement (n + 1)) (initialDescendingWord n) := by
  refine ⟨initialDescendingWord_product n, ?_⟩
  rw [initialDescendingWord_length, ← initialDescendingWord_product,
    length_initialDescendingWord]

end FinitaryPerm
