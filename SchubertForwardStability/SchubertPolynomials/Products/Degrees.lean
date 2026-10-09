import SchubertForwardStability.SchubertPolynomials.Products.Forward
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Product forward bounds through variable degrees

## Main results

Over a domain the separate degrees of a Schubert product add. Over the integers,
its forward bound is consequently the positive maximum of index plus summed
variable degree, with zero-degree variables omitted.

## Implementation notes

Artin membership and the finite/global basis support criterion connect polynomial
degrees to the support of the structure constants.
-/

namespace SchubertPolynomial

noncomputable section

open scoped Classical

/-- Separate variable degrees add in a Schubert product over a domain. -/
theorem schubert_mul_degreeOf {R : Type*} [CommRing R] [IsDomain R]
    (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    (schubert R u * schubert R v).degreeOf i =
      (schubert R u).degreeOf i + (schubert R v).degreeOf i :=
  MvPolynomial.degreeOf_mul_eq (n := i) (schubert_ne_zero u) (schubert_ne_zero v)

/-- A positive forward bound is equivalent to all positive summed-degree Artin bounds. -/
theorem productForwardStability_le_iff_degree (u v : FinitaryPerm ℕ+)
    {n : ℕ} (hn : 1 ≤ n) :
    productForwardStability u v ≤ n ↔ ∀ i : ℕ+,
      0 < (schubert ℤ u).degreeOf i + (schubert ℤ v).degreeOf i →
      (i : ℕ) + ((schubert ℤ u).degreeOf i + (schubert ℤ v).degreeOf i) ≤ n := by
  rw [productForwardStability_le_iff_artin u v hn, mem_artinSpan_iff_degree_pos]
  simp only [schubert_mul_degreeOf]

private theorem mem_vars_union (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    i ∈ (schubert ℤ u).vars ∪ (schubert ℤ v).vars ↔
      0 < (schubert ℤ u).degreeOf i + (schubert ℤ v).degreeOf i := by
  rw [Finset.mem_union, MvPolynomial.mem_vars_iff_degreeOf_ne_zero,
    MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
  omega

/-- Product forward stability is the positive maximum of index plus nonzero
summed variable degrees of its factors. -/
theorem productForwardStability_eq_degreeSup (u v : FinitaryPerm ℕ+) :
    productForwardStability u v = max 1
      (((schubert ℤ u).vars ∪ (schubert ℤ v).vars).sup fun i : ℕ+ =>
        (i : ℕ) + ((schubert ℤ u).degreeOf i + (schubert ℤ v).degreeOf i)) := by
  let s := (schubert ℤ u).vars ∪ (schubert ℤ v).vars
  let f := fun i : ℕ+ => (i : ℕ) +
    ((schubert ℤ u).degreeOf i + (schubert ℤ v).degreeOf i)
  let n := max 1 (s.sup f)
  change productForwardStability u v = n
  have hn : 1 ≤ n := le_max_left _ _
  apply le_antisymm
  · apply (productForwardStability_le_iff_degree u v (n := n) hn).mpr
    intro i hi
    have hmem : i ∈ s := (mem_vars_union u v i).mpr hi
    have hle : f i ≤ s.sup f := Finset.le_sup (f := f) hmem
    exact hle.trans (le_max_right _ _)
  · apply max_le (one_le_productForwardStability u v)
    apply Finset.sup_le
    intro i hi
    exact (productForwardStability_le_iff_degree u v
      (one_le_productForwardStability u v)).mp le_rfl i ((mem_vars_union u v i).mp hi)

end

end SchubertPolynomial
