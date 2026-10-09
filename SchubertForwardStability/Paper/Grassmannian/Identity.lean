import SchubertForwardStability.Paper.Grassmannian.Bounds
import Mathlib.Algebra.Order.Ring.Abs

/-! # Residuals at identity subset encodings

## Main results

A single identity encoding gives a naturally truncated sampled-size difference.
Two identity encodings give the signed value one minus the smaller sampled size.
Together with the nonidentity defect formula these yield an absolute bound by the
greater of one and the ambient size, including size zero.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial
open scoped Classical

/-- The selected maximum of an identity encoding equals its sampled cardinality. -/
theorem subset_identity_maximum (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n)
    (hw : subsetPermutation n V = 1) : V.sup PNat.val = V.card := by
  by_cases hz : V.card = 0
  · rw [Finset.card_eq_zero.mp hz]
    rfl
  · have hv := Nat.pos_of_ne_zero hz
    have hm := grassmannian_first_maximum n V hV hv
    rw [←subsetPermutation_eq n V hV, hw] at hm
    exact hm.symm

/-- Two identity encodings have the signed residual one minus their smaller sampled size. -/
theorem subset_residual_both_identity (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) (hu : subsetPermutation n V = 1)
    (hv : subsetPermutation n W = 1) :
    grassmannianResidual n V W = 1 - (min V.card W.card : ℤ) := by
  rw [grassmannianResidual_eq, hu, hv, productForwardStability_one,
    subset_identity_maximum n V hV hu, subset_identity_maximum n W hW hv]
  omega

/-- A left identity encoding gives the naturally truncated difference of sampled sizes. -/
theorem subset_residual_left_identity (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) (hu : subsetPermutation n V = 1)
    (hv : subsetPermutation n W ≠ 1) :
    grassmannianResidual n V W = ((W.card - V.card : ℕ) : ℤ) := by
  rw [grassmannianResidual_eq, hu, productForwardStability_one_left,
    subset_forward_eq_max n W hW hv, subset_identity_maximum n V hV hu]
  omega

/-- A right identity encoding gives the naturally truncated reversed sampled-size difference. -/
theorem subset_residual_right_identity (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) (hu : subsetPermutation n V ≠ 1)
    (hv : subsetPermutation n W = 1) :
    grassmannianResidual n V W = ((V.card - W.card : ℕ) : ℤ) := by
  rw [grassmannianResidual_comm]
  exact subset_residual_left_identity n W V hW hV hv hu

/-- Every admissible pair's absolute residual is bounded by the positive ambient bound. -/
theorem subset_residual_abs_le (n : ℕ) (V W : Finset ℕ+) (hV : V ⊆ positions n)
    (hW : W ⊆ positions n) : |grassmannianResidual n V W| ≤ (max 1 n : ℕ) := by
  have hk : V.card ≤ n := by simpa only [card_positions] using Finset.card_le_card hV
  have hl : W.card ≤ n := by simpa only [card_positions] using Finset.card_le_card hW
  by_cases hu : subsetPermutation n V = 1
  · by_cases hv : subsetPermutation n W = 1
    · rw [subset_residual_both_identity n V W hV hW hu hv]
      apply abs_le.mpr
      constructor <;> omega
    · rw [subset_residual_left_identity n V W hV hW hu hv]
      rw [abs_of_nonneg (Int.natCast_nonneg _)]
      omega
  · by_cases hv : subsetPermutation n W = 1
    · rw [subset_residual_right_identity n V W hV hW hu hv]
      rw [abs_of_nonneg (Int.natCast_nonneg _)]
      omega
    · rw [abs_of_nonneg (subset_residual_nonneg n V W hV hW hu hv)]
      exact (subset_residual_le_card n V W hV hW hu hv).trans (by omega)

/-- At positive ambient size the absolute residual is bounded by that size itself. -/
theorem subset_residual_abs_le_of_pos {n : ℕ} (hn : 1 ≤ n) (V W : Finset ℕ+)
    (hV : V ⊆ positions n) (hW : W ⊆ positions n) :
    |grassmannianResidual n V W| ≤ (n : ℤ) := by
  simpa only [max_eq_right hn] using subset_residual_abs_le n V W hV hW

end RecordStability
