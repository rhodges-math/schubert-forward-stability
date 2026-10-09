import SchubertForwardStability.Permutations.Random.Subsets
import SchubertForwardStability.SchubertPolynomials.Products.Forward

/-! # Grassmannian subset residuals

## Main definitions

* `grassmannianResidual`: product stability minus the sum of sampled prefix maxima
  less the greater sampled subset cardinality.

## Implementation notes

The sampled cardinality remains an encoding parameter even when the encoded
permutation is the identity. The maximum of the empty subset is zero.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial MeasureTheory

/-- The integer error in the sampled Grassmannian product formula. -/
noncomputable def grassmannianResidual (n : ℕ) (V W : Finset ℕ+) : ℤ :=
  (productForwardStability (subsetPermutation n V) (subsetPermutation n W) : ℤ) -
    (((V.sup PNat.val : ℕ) : ℤ) + ((W.sup PNat.val : ℕ) : ℤ) -
      ((max V.card W.card : ℕ) : ℤ))

/-- The residual has its displayed product-stability expression. -/
theorem grassmannianResidual_eq (n : ℕ) (V W : Finset ℕ+) :
    grassmannianResidual n V W =
      (productForwardStability (subsetPermutation n V) (subsetPermutation n W) : ℤ) -
        (((V.sup PNat.val : ℕ) : ℤ) + ((W.sup PNat.val : ℕ) : ℤ) -
          ((max V.card W.card : ℕ) : ℤ)) :=
  rfl

/-- Interchanging the two sampled subsets preserves the residual. -/
theorem grassmannianResidual_comm (n : ℕ) (V W : Finset ℕ+) :
    grassmannianResidual n V W = grassmannianResidual n W V := by
  unfold grassmannianResidual
  rw [productForwardStability_comm, add_comm ((V.sup PNat.val : ℕ) : ℤ),
    max_comm V.card W.card]

/-- The residual is measurable on the countable subset-pair space. -/
theorem measurable_grassmannianResidual (n : ℕ) :
    Measurable (fun p : Finset ℕ+ × Finset ℕ+ => grassmannianResidual n p.1 p.2) :=
  measurable_of_countable _

end RecordStability
