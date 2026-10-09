import SchubertForwardStability.Permutations.Classes.GrassRecordStructure
import SchubertForwardStability.Permutations.Statistics.Blocks.TwoBlockMaximum
import SchubertForwardStability.Permutations.Random.Subsets
import SchubertForwardStability.Paper.Walk.Basic
import SchubertForwardStability.Paper.Grassmannian.Residual
import SchubertForwardStability.SchubertPolynomials.Products.RecordBound

/-! # Records of subset-encoded Grassmannian permutations

## Main results

The sampled subset cardinality and maximum determine every intrinsic non-record
tail. Under the overlapping-prefix condition they also determine the four walk
pieces and the exact product forward bound.

## Implementation notes

The sampled cardinality need not equal a descent position. Empty subsets and
initial segments retain their identity encoding.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial
open scoped Classical

/-- The sampled maximum fixes the later positions and is the forward bound off identity. -/
theorem subset_support_maximum (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) :
    let w := subsetPermutation n V
    let M := V.sup PNat.val
    (∀ j : ℕ+, M < (j : ℕ) → w j = j) ∧
      (w ≠ 1 → 1 ≤ M ∧ w.forwardStability = M) ∧
      (w = 1 → w.forwardStability = 1) := by
  dsimp only
  rw [subsetPermutation_eq n V hV]
  refine ⟨grassmannian_fixed_above_max n V hV, ?_, ?_⟩
  · intro hw
    have he := grassmannian_forward_eq_max n V hV hw
    exact ⟨he ▸ (grassmannianOfSubset n V hV).one_le_forwardStability, he⟩
  · intro hw
    rw [hw, forwardStability_one]

/-- A nonidentity subset encoding has the sampled maximum as its forward bound. -/
theorem subset_forward_eq_max (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n)
    (hw : subsetPermutation n V ≠ 1) :
    (subsetPermutation n V).forwardStability = V.sup PNat.val :=
  ((subset_support_maximum n V hV).2.1 hw).2

/-- The non-record positions are the sampled open-closed block interval. -/
theorem subset_notRecord_iff (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) (i : ℕ+) :
    ¬IsRecord (subsetPermutation n V) i ↔
      V.card < (i : ℕ) ∧ (i : ℕ) ≤ V.sup PNat.val := by
  rw [subsetPermutation_eq n V hV]
  exact grassmannian_notRecord_iff n V hV i

/-- The non-record indicator is exactly the sampled block-interval indicator. -/
theorem subset_nonRecordIndicator (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) (i : ℕ+) :
    (subsetPermutation n V).nonRecordIndicator i =
      if V.card < (i : ℕ) ∧ (i : ℕ) ≤ V.sup PNat.val then 1 else 0 := by
  by_cases hi : V.card < (i : ℕ) ∧ (i : ℕ) ≤ V.sup PNat.val
  · rw [ite_eq_left hi, nonRecordIndicator_eq_one ((subset_notRecord_iff n V hV i).mpr hi)]
  · have hr : IsRecord (subsetPermutation n V) i := by
      by_contra hn
      exact hi ((subset_notRecord_iff n V hV i).mp hn)
    rw [ite_eq_right hi, nonRecordIndicator_eq_zero hr]

/-- Every sampled subset has the three-piece intrinsic non-record tail. -/
theorem subset_nonRecordsFrom (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) (i : ℕ+) :
    (subsetPermutation n V).nonRecordsFrom i =
      if (i : ℕ) ≤ V.card then V.sup PNat.val - V.card
      else if (i : ℕ) ≤ V.sup PNat.val then V.sup PNat.val - (i : ℕ) + 1 else 0 := by
  rw [subsetPermutation_eq n V hV]
  exact grassmannian_tail_formula n V hV i

/-- A paired subset walk step is one minus the two block-interval indicators. -/
theorem subset_recordWalkStep (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) (i : ℕ+) :
    recordWalkStep (subsetPermutation n V) (subsetPermutation n W) i =
      1 - ((if V.card < (i : ℕ) ∧ (i : ℕ) ≤ V.sup PNat.val then 1 else 0 : ℕ) : ℤ) -
        ((if W.card < (i : ℕ) ∧ (i : ℕ) ≤ W.sup PNat.val then 1 else 0 : ℕ) : ℤ) := by
  rw [recordWalkStep_eq, subset_nonRecordIndicator n V hV i,
    subset_nonRecordIndicator n W hW i]

/-- Overlapping sampled prefixes give the four increasing, flat and decreasing pieces. -/
theorem subset_walk_shape (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) :
    let u := subsetPermutation n V
    let v := subsetPermutation n W
    let a := min V.card W.card
    let b := max V.card W.card
    let c := min (V.sup PNat.val) (W.sup PNat.val)
    let m := max u.forwardStability v.forwardStability
    u ≠ 1 → v ≠ 1 → b < c →
      (∀ i : ℕ+, (i : ℕ) ≤ a → recordWalk u v i < recordWalk u v (i + 1)) ∧
      (∀ i : ℕ+, a + 1 ≤ (i : ℕ) → (i : ℕ) ≤ b →
        recordWalk u v i = recordWalk u v (i + 1)) ∧
      (∀ i : ℕ+, b + 1 ≤ (i : ℕ) → (i : ℕ) ≤ c →
        recordWalk u v (i + 1) < recordWalk u v i) ∧
      (∀ i : ℕ+, c + 1 ≤ (i : ℕ) → (i : ℕ) ≤ m →
        recordWalk u v i = recordWalk u v (i + 1)) := by
  dsimp only
  intro hu hv hsep
  have hfu := subset_forward_eq_max n V hV hu
  have hfv := subset_forward_eq_max n W hW hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hs := subset_recordWalkStep n V W hV hW i
    unfold recordWalkStep at hs
    split_ifs at hs <;> omega
  · intro i hlo hhi
    have hs := subset_recordWalkStep n V W hV hW i
    unfold recordWalkStep at hs
    split_ifs at hs <;> omega
  · intro i hlo hhi
    have hs := subset_recordWalkStep n V W hV hW i
    unfold recordWalkStep at hs
    split_ifs at hs <;> omega
  · intro i hlo hhi
    rw [hfu, hfv] at hhi
    have hs := subset_recordWalkStep n V W hV hW i
    unfold recordWalkStep at hs
    split_ifs at hs <;> omega

/-- The overlapping-prefix product has the sum of maxima minus the greater sampled size. -/
theorem subset_productForwardStability (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) (hu : subsetPermutation n V ≠ 1)
    (hv : subsetPermutation n W ≠ 1)
    (hsep : max V.card W.card < min (V.sup PNat.val) (W.sup PNat.val)) :
    productForwardStability (subsetPermutation n V) (subsetPermutation n W) =
      V.sup PNat.val + W.sup PNat.val - max V.card W.card := by
  rw [productForwardStability_eq_recordBound]
  unfold pairRecordBound
  rw [subset_forward_eq_max n V hV hu, subset_forward_eq_max n W hW hv]
  convert twoBlock_pairMax_eq hsep using 1
  congr 1
  funext i
  rw [subset_nonRecordsFrom n V hV i, subset_nonRecordsFrom n W hW i]

/-- The signed sampled residual vanishes on the overlapping-prefix event. -/
theorem subset_residual_eq_zero (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) (hu : subsetPermutation n V ≠ 1)
    (hv : subsetPermutation n W ≠ 1)
    (hsep : max V.card W.card < min (V.sup PNat.val) (W.sup PNat.val)) :
    grassmannianResidual n V W = 0 := by
  rw [grassmannianResidual_eq, subset_productForwardStability n V W hV hW hu hv hsep]
  omega

end RecordStability
