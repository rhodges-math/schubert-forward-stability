import SchubertForwardStability.StrongMixing.Inequalities.RetainedSubset

/-!
# Finite peeling by deterministic half-retained subsets

At each stage, remove the fixed retained selector from the residual coordinate
set. The finite decomposition is exact, and every residual cardinality decreases
by a factor of at least two, with no limiting or rounding convention.
-/

open scoped BigOperators

namespace StrongMixing

/-- The residual finite coordinate set after `k` deterministic peeling stages.
Stage zero is the original set; each next stage removes its retained selector. -/
noncomputable def peelingRemainder (A : Finset ℤ) : ℕ → Finset ℤ
  | 0 => A
  | k + 1 => peelingRemainder A k \ retainedSubset (peelingRemainder A k)

/-- The coordinates removed at peeling stage `k`, namely the retained selector
of the residual set before that stage. This set depends only on `A` and `k`. -/
noncomputable def peelingPiece (A : Finset ℤ) (k : ℕ) : Finset ℤ :=
  retainedSubset (peelingRemainder A k)

/-- One deterministic peeling step can only remove coordinates from the
preceding residual set. -/
theorem peelingRemainder_step_subset (A : Finset ℤ) (k : ℕ) :
    peelingRemainder A (k + 1) ⊆ peelingRemainder A k := Finset.sdiff_subset

/-- Every residual coordinate at every finite peeling stage belongs to the
original finite set, including the empty-set case. -/
theorem peelingRemainder_subset (A : Finset ℤ) (k : ℕ) :
    peelingRemainder A k ⊆ A := by
  induction k with
  | zero => exact Finset.Subset.refl A
  | succ k ih => exact (peelingRemainder_step_subset A k).trans ih

/-- Each removed peeling piece is contained in the residual set from which it
was selected. -/
theorem peelingPiece_subset (A : Finset ℤ) (k : ℕ) :
    peelingPiece A k ⊆ peelingRemainder A k := retainedSubset_subset _

/-- Peeling an empty coordinate set leaves the empty set at every stage. -/
theorem peelingRemainder_empty (k : ℕ) : peelingRemainder ∅ k = ∅ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [peelingRemainder, ih, retainedSubset_empty]

/-- The residual cardinality after `k` peeling stages satisfies the exact
natural-number inequality `2^k*card(residual)<=card(A)`. -/
theorem peelingRemainder_card_mul (A : Finset ℤ) (k : ℕ) :
    2 ^ k * (peelingRemainder A k).card ≤ A.card := by
  induction k with
  | zero => simp [peelingRemainder]
  | succ k ih =>
    have hs := Nat.mul_le_mul_left (2 ^ k)
      (retainedSubset_residual_card (peelingRemainder A k))
    calc
      2 ^ (k + 1) * (peelingRemainder A (k + 1)).card =
          2 ^ k * (2 * (peelingRemainder A (k + 1)).card) := by rw [pow_succ]; ring
      _ ≤ 2 ^ k * (peelingRemainder A k).card := hs
      _ ≤ A.card := ih

/-- The residual cardinality after `k` peeling stages is bounded by
`card(A)/2^k` as a real number. -/
theorem peelingRemainder_card_le (A : Finset ℤ) (k : ℕ) :
    ((peelingRemainder A k).card : ℝ) ≤ (A.card : ℝ) / (2 : ℝ) ^ k := by
  have h : (2 : ℝ) ^ k * (peelingRemainder A k).card ≤ A.card := by
    exact_mod_cast peelingRemainder_card_mul A k
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).mpr
  nlinarith only [h]

/-- The piece selected at stage `k` has cardinality at most `card(A)/2^k`,
so its square-root size decays at a geometric rate for Laplace aggregation. -/
theorem peelingPiece_card_le (A : Finset ℤ) (k : ℕ) :
    ((peelingPiece A k).card : ℝ) ≤ (A.card : ℝ) / (2 : ℝ) ^ k := by
  have h : ((peelingPiece A k).card : ℝ) ≤ (peelingRemainder A k).card := by
    exact_mod_cast Finset.card_le_card (peelingPiece_subset A k)
  exact h.trans (peelingRemainder_card_le A k)

/-- Once `2^k` exceeds the original cardinality, the residual set is
empty. Thus the deterministic peeling procedure terminates in finitely many stages. -/
theorem peelingRemainder_eq_empty (A : Finset ℤ) (k : ℕ) (hk : A.card < 2 ^ k) :
    peelingRemainder A k = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := peelingRemainder_card_mul A k
  by_contra hp
  have hone : 1 ≤ (peelingRemainder A k).card := by omega
  have hh := Nat.mul_le_mul_left (2 ^ k) hone
  simp only [mul_one] at hh
  omega

/-- A single peeling stage partitions the residual sum exactly into the
selected piece and the next residual sum, for every real coordinate function. -/
theorem peeling_step_sum (A : Finset ℤ) (k : ℕ) (f : ℤ → ℝ) :
    (∑ i ∈ peelingRemainder A k, f i) =
      (∑ i ∈ peelingPiece A k, f i) + ∑ i ∈ peelingRemainder A (k + 1), f i := by
  have h := Finset.sum_sdiff (f := f) (retainedSubset_subset (peelingRemainder A k))
  change (∑ i ∈ peelingRemainder A (k + 1), f i) +
    (∑ i ∈ peelingPiece A k, f i) = _ at h
  linarith

/-- After any finite number of stages, the original coordinate sum is exactly
the sum of all selected piece sums plus the remaining residual sum. -/
theorem peeling_sum_decomposition (A : Finset ℤ) (k : ℕ) (f : ℤ → ℝ) :
    (∑ i ∈ A, f i) =
      (∑ j ∈ Finset.range k, ∑ i ∈ peelingPiece A j, f i) +
        ∑ i ∈ peelingRemainder A k, f i := by
  induction k with
  | zero => simp [peelingRemainder]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h := peeling_step_sum A k f
    linarith

end StrongMixing
