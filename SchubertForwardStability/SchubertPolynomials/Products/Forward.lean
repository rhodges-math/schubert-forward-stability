import SchubertForwardStability.SchubertPolynomials.Products.Constants
import SchubertForwardStability.SchubertPolynomials.Basis.Support

/-! # Forward support bounds of Schubert products

## Main definitions

* `productForwardStability`: the least positive size supporting every nonzero
  integer Schubert product coordinate.

## Main results

The coordinate maximum equals the least positive Artin size of the product.
Identity factors recover the forward stability of the other permutation.

## Implementation notes

An explicit floor of one records the positive-size convention. Integer products
have nonempty coordinate support, so this floor does not alter their maximum.
-/

namespace SchubertPolynomial

noncomputable section

open scoped Classical

/-- The least positive bound containing every nonzero Schubert product coordinate. -/
def productForwardStability (u v : FinitaryPerm ℕ+) : ℕ :=
  max 1 ((structureCoefficients ℤ u v).support.sup FinitaryPerm.forwardStability)

/-- Every integer Schubert product has at least one nonzero coordinate. -/
theorem structureCoefficients_support_nonempty (u v : FinitaryPerm ℕ+) :
    (structureCoefficients ℤ u v).support.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  exact structureCoefficients_ne_zero u v (Finsupp.support_eq_empty.mp he)

/-- Product forward stability is positive, including at two identity factors. -/
theorem one_le_productForwardStability (u v : FinitaryPerm ℕ+) :
    1 ≤ productForwardStability u v := le_max_left _ _

/-- The positive floor is redundant for the nonempty support of an integer product. -/
theorem productForwardStability_eq_sup (u v : FinitaryPerm ℕ+) :
    productForwardStability u v =
      (structureCoefficients ℤ u v).support.sup FinitaryPerm.forwardStability := by
  obtain ⟨w, hw⟩ := structureCoefficients_support_nonempty u v
  exact max_eq_right (w.one_le_forwardStability.trans (Finset.le_sup hw))

/-- A bound contains a Schubert product exactly when it is positive and contains
the forward stability of each nonzero coordinate. -/
theorem productForwardStability_le_iff (u v : FinitaryPerm ℕ+) (n : ℕ) :
    productForwardStability u v ≤ n ↔
      1 ≤ n ∧ ∀ w, structureConst u v w ≠ 0 → w.forwardStability ≤ n := by
  rw [productForwardStability, max_le_iff, Finset.sup_le_iff]
  simp only [Finsupp.mem_support_iff, structureConst]

/-- A positive forward bound is exactly an ambient support bound on nonzero coordinates. -/
theorem productForwardStability_le_iff_support (u v : FinitaryPerm ℕ+)
    {n : ℕ} (hn : 1 ≤ n) :
    productForwardStability u v ≤ n ↔
      ∀ w, structureConst u v w ≠ 0 → FinitaryPerm.IsSupported n w := by
  rw [productForwardStability_le_iff, and_iff_right hn]
  simp only [FinitaryPerm.forwardStability_le_iff _ hn]

/-- A nonzero product coordinate's permutation is contained in the product bound. -/
theorem forwardStability_le_product {u v w : FinitaryPerm ℕ+}
    (hw : structureConst u v w ≠ 0) : w.forwardStability ≤ productForwardStability u v :=
  ((productForwardStability_le_iff u v _).mp le_rfl).2 w hw

/-- Exchanging input factors preserves product forward stability. -/
theorem productForwardStability_comm (u v : FinitaryPerm ℕ+) :
    productForwardStability u v = productForwardStability v u := by
  rw [productForwardStability, structureCoefficients_comm, productForwardStability]

/-- An identity left factor recovers the other permutation's positive support bound. -/
@[simp] theorem productForwardStability_one_left (v : FinitaryPerm ℕ+) :
    productForwardStability 1 v = v.forwardStability := by
  simp only [productForwardStability, structureCoefficients_one_left,
    Finsupp.support_single _ one_ne_zero, Finset.sup_singleton,
    max_eq_right v.one_le_forwardStability]

/-- An identity right factor recovers the other permutation's positive support bound. -/
@[simp] theorem productForwardStability_one_right (u : FinitaryPerm ℕ+) :
    productForwardStability u 1 = u.forwardStability := by
  rw [productForwardStability_comm, productForwardStability_one_left]

/-- The product of the two identity permutations has forward stability one. -/
theorem productForwardStability_one : productForwardStability 1 1 = 1 := by
  rw [productForwardStability_one_left, FinitaryPerm.forwardStability_one]

/-- A positive size bounds the product coordinates exactly when the polynomial
product belongs to that size's Artin span. -/
theorem productForwardStability_le_iff_artin (u v : FinitaryPerm ℕ+)
    {n : ℕ} (hn : 1 ≤ n) :
    productForwardStability u v ≤ n ↔ schubert ℤ u * schubert ℤ v ∈ artinSpan ℤ n := by
  rw [productForwardStability_le_iff_support u v hn, mem_artinSpan_iff_schubert]
  rfl

/-- Product forward stability is the least positive Artin bound of the product. -/
theorem productForwardStability_isLeast (u v : FinitaryPerm ℕ+) :
    IsLeast {n : ℕ | 1 ≤ n ∧ schubert ℤ u * schubert ℤ v ∈ artinSpan ℤ n}
      (productForwardStability u v) := by
  refine ⟨⟨one_le_productForwardStability u v, ?_⟩, ?_⟩
  · exact (productForwardStability_le_iff_artin u v
      (one_le_productForwardStability u v)).mp le_rfl
  · intro n hn
    exact (productForwardStability_le_iff_artin u v hn.1).mpr hn.2

end

end SchubertPolynomial
