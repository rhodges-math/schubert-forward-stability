import SchubertForwardStability.Permutations.Statistics.PivotCovers
import SchubertForwardStability.SchubertPolynomials.Stability.LinearExtraction

/-! # Finite left-cover Schubert sums

## Main definitions

* `transitionSum`: the Schubert sum of gap-free left covers at a fixed right endpoint.

## Main results

The finite sum is homogeneous of the next inversion length. Its divided-difference
coordinates count the distinct left-cover outputs and vanish at the pivot output.
-/

namespace SchubertPolynomial

open FinitaryPerm
open scoped Classical BigOperators

variable {R : Type*} [CommRing R]

/-- The finite positive sum of Schubert polynomials at the left-cover outputs. -/
noncomputable def transitionSum (R : Type*) [CommRing R] (v : FinitaryPerm ℕ+) (r : ℕ+) :
    MvPolynomial ℕ+ R := ∑ q ∈ transitionPositions v r, schubert R (v * swap q r)

/-- All left-cover summands have homogeneous degree one above the starting length. -/
theorem transitionSum_isHomogeneous (v : FinitaryPerm ℕ+) (r : ℕ+) :
    (transitionSum R v r).IsHomogeneous (v.length + 1) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro q hq
  rw [← transitionPositions_length hq]
  exact schubert_isHomogeneous _

/-- Extraction of the left-cover sum is its finite sum of product-indexed deltas. -/
theorem transitionSum_functional (v z : FinitaryPerm ℕ+) (r : ℕ+) :
    schubertFunctional R z (transitionSum R v r) =
      ∑ q ∈ transitionPositions v r, if z = v * swap q r then 1 else 0 := by
  simp only [transitionSum, map_sum, schubertFunctional_schubert]

/-- Every left-cover output has coefficient one in the finite sum. -/
theorem transitionSum_functional_at {v : FinitaryPerm ℕ+} {q r : ℕ+}
    (hq : q ∈ transitionPositions v r) :
    schubertFunctional R (v * swap q r) (transitionSum R v r) = 1 := by
  rw [transitionSum_functional, Finset.sum_eq_single q]
  · exact ite_eq_left rfl
  · intro t ht hne
    apply ite_eq_right
    intro he
    exact hne (transitionOutput_injective hq ht he).symm
  · intro hn
    exact False.elim (hn hq)

/-- Every index outside the left-cover outputs has coefficient zero in the finite sum. -/
theorem transitionSum_functional_outside (v z : FinitaryPerm ℕ+) (r : ℕ+)
    (hn : ∀ q ∈ transitionPositions v r, z ≠ v * swap q r) :
    schubertFunctional R z (transitionSum R v r) = 0 := by
  rw [transitionSum_functional]
  exact Finset.sum_eq_zero (fun q hq => ite_eq_right (hn q hq))

/-- The pivot output does not occur among the left-cover summands. -/
theorem transitionSum_functional_pivot {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) :
    schubertFunctional R w (transitionSum R (w * swap r s) r) = 0 := by
  apply transitionSum_functional_outside
  intro q hq he
  have hs : (swap r s : FinitaryPerm ℕ+) * swap r s = 1 := by
    simpa only [swap_inv] using mul_inv_cancel (swap r s)
  have hb : (w * swap r s) * swap r s = w := by rw [mul_assoc, hs, mul_one]
  have hq' := (mem_transitionPositions _ _ _).mp hq
  have he' := swap_ordered_injective h.start_lt hq'.left_lt
    (mul_left_cancel (hb.trans he))
  exact (ne_of_gt hq'.left_lt) he'.1

end SchubertPolynomial
