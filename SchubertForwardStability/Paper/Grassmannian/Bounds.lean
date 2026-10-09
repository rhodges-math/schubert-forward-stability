import SchubertForwardStability.Paper.Grassmannian.Records
import SchubertForwardStability.Permutations.Statistics.Blocks.TwoBlockGeneral

/-! # Deterministic residual bounds for subset pairs

## Main results

For two nonidentity encodings the signed residual is the nonnegative sampled
block-size excess above the smaller maximum. A nonzero residual can occur only at
an identity encoding or at this excess event.

## Implementation notes

All exact support formulas require both encodings to be nonidentity. Initial-segment
encodings keep their intrinsic forward bound one, independently of their sampled size.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial
open scoped Classical

private theorem card_le_maximum (V : Finset ℕ+) : V.card ≤ V.sup PNat.val := by
  have hs : V ⊆ positions (V.sup PNat.val) := by
    intro j hj
    exact (mem_positions _ _).mpr (Finset.le_sup (f := PNat.val) hj)
  simpa only [card_positions] using Finset.card_le_card hs

/-- The general nonidentity pair has the greater endpoint-or-interior forward bound. -/
theorem subset_productForwardStability_general (n : ℕ) (V W : Finset ℕ+)
    (hV : V ⊆ positions n) (hW : W ⊆ positions n) (hu : subsetPermutation n V ≠ 1)
    (hv : subsetPermutation n W ≠ 1) :
    productForwardStability (subsetPermutation n V) (subsetPermutation n W) =
      max (max (V.sup PNat.val) (W.sup PNat.val))
        (V.sup PNat.val + W.sup PNat.val - max V.card W.card) := by
  rw [productForwardStability_eq_recordBound]
  unfold pairRecordBound
  rw [subset_forward_eq_max n V hV hu, subset_forward_eq_max n W hW hv]
  convert twoBlock_pairMax_general (card_le_maximum V) (card_le_maximum W) using 1
  congr 1
  funext i
  rw [subset_nonRecordsFrom n V hV i, subset_nonRecordsFrom n W hW i]

/-- Off identity, the residual is precisely the sampled endpoint excess. -/
theorem subset_residual_eq_defect (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) (hu : subsetPermutation n V ≠ 1)
    (hv : subsetPermutation n W ≠ 1) :
    grassmannianResidual n V W =
      ((max V.card W.card - min (V.sup PNat.val) (W.sup PNat.val) : ℕ) : ℤ) := by
  rw [grassmannianResidual_eq, subset_productForwardStability_general n V W hV hW hu hv]
  have hk := card_le_maximum V
  have hl := card_le_maximum W
  omega

/-- A pair of nonidentity subset encodings has nonnegative residual. -/
theorem subset_residual_nonneg (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) (hu : subsetPermutation n V ≠ 1)
    (hv : subsetPermutation n W ≠ 1) : 0 ≤ grassmannianResidual n V W := by
  rw [subset_residual_eq_defect n V W hV hW hu hv]
  exact Int.natCast_nonneg _

/-- A nonidentity pair's residual cannot exceed its greater sampled size. -/
theorem subset_residual_le_card (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) (hu : subsetPermutation n V ≠ 1)
    (hv : subsetPermutation n W ≠ 1) :
    grassmannianResidual n V W ≤ (max V.card W.card : ℤ) := by
  rw [subset_residual_eq_defect n V W hV hW hu hv]
  omega

/-- Weak endpoint overlap already forces the nonidentity pair's residual to vanish. -/
theorem subset_residual_eq_zero_of_le (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) (hu : subsetPermutation n V ≠ 1)
    (hv : subsetPermutation n W ≠ 1)
    (hsep : max V.card W.card ≤ min (V.sup PNat.val) (W.sup PNat.val)) :
    grassmannianResidual n V W = 0 := by
  rw [subset_residual_eq_defect n V W hV hW hu hv]
  omega

/-- A nonidentity pair has nonzero residual exactly when its sampled endpoints exceed overlap. -/
theorem subset_residual_ne_zero_iff (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) (hu : subsetPermutation n V ≠ 1)
    (hv : subsetPermutation n W ≠ 1) :
    grassmannianResidual n V W ≠ 0 ↔
      min (V.sup PNat.val) (W.sup PNat.val) < max V.card W.card := by
  rw [subset_residual_eq_defect n V W hV hW hu hv]
  omega

/-- Every nonzero residual belongs to an identity or sampled-overlap exception event. -/
theorem subset_residual_exception (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) (hne : grassmannianResidual n V W ≠ 0) :
    subsetPermutation n V = 1 ∨ subsetPermutation n W = 1 ∨
      min (V.sup PNat.val) (W.sup PNat.val) < max V.card W.card := by
  by_cases hu : subsetPermutation n V = 1
  · exact Or.inl hu
  by_cases hv : subsetPermutation n W = 1
  · exact Or.inr (Or.inl hv)
  exact Or.inr (Or.inr ((subset_residual_ne_zero_iff n V W hV hW hu hv).mp hne))

end RecordStability
