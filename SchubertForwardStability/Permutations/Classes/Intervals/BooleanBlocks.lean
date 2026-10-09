import SchubertForwardStability.Permutations.Classes.Boolean.BooleanRecords

/-! # Maximal decreasing blocks of adjacent words

## Main definitions

Descending adjacent-generator blocks, their maximal concatenation predicate,
and the ascending interval-order predicate used for Boolean normal forms.

## Implementation notes

An inverted endpoint interval denotes the empty word. Maximality prevents a
decreasing continuation across the boundary of two consecutive blocks.
-/

namespace FinitaryPerm

/-- The decreasing adjacent word from `j` through `i`, empty for inverted endpoints. -/
def decreasingBlockWord (i j : ℕ+) : List ℕ+ :=
  if i ≤ j then (List.range ((j : ℕ) - (i : ℕ) + 1)).map
    fun r => ((j : ℕ) - r).toPNat'
  else []

/-- The permutation represented by a decreasing adjacent-generator block. -/
def decreasingBlock (i j : ℕ+) : FinitaryPerm ℕ+ := wordProduct (decreasingBlockWord i j)

/-- A maximal factorization has descending nonempty blocks and no mergeable boundary. -/
def IsMaximalBlocks (word : List ℕ+) (blocks : List (List ℕ+)) : Prop :=
  blocks.flatten = word ∧
    (∀ b ∈ blocks, ∃ i j : ℕ+, i ≤ j ∧ b = decreasingBlockWord i j) ∧
    ∀ pre suf : List (List ℕ+), ∀ a b : List ℕ+, blocks = pre ++ a :: b :: suf →
      ¬∃ i j : ℕ+, a.getLast? = some i ∧ b.head? = some j ∧ j + 1 = i

/-- Ascending block intervals place every generator of one block below those of the next. -/
def IsAscendingBlocks (blocks : List (List ℕ+)) : Prop :=
  ∀ pre suf : List (List ℕ+), ∀ a b : List ℕ+, blocks = pre ++ a :: b :: suf →
    ∀ i ∈ a, ∀ j ∈ b, i < j

/-- A block with equal endpoints contains exactly that one generator. -/
@[simp]
theorem decreasingBlockWord_self (i : ℕ+) : decreasingBlockWord i i = [i] := by
  simp [decreasingBlockWord]

end FinitaryPerm
