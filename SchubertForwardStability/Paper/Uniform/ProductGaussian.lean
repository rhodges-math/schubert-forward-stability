import SchubertForwardStability.Paper.Uniform.Excess
import SchubertForwardStability.SchubertPolynomials.Products.RecordBound

/-! # The Gaussian limit of uniform product forward stability

## Main results

The record formula decomposes product forward stability into its second walk
value and intrinsic excess. Their Gaussian and vanishing limits give the product limit.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Theorem 1.3.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

/-- Product forward stability is the second walk value plus its intrinsic excess. -/
theorem productForwardStability_eq_second_excess (u v : FinitaryPerm ℕ+) :
    (productForwardStability u v : ℤ) = recordWalk u v 2 + recordWalkExcess u v := by
  rw [productForwardStability_eq_recordBound]
  unfold recordWalkExcess recordWalkMax
  ring

/-- Uniform product forward stability, with logarithmic centering, tends to standard Gaussian. -/
theorem uniform_product_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        ((productForwardStability p.1 p.2 : ℝ) - (2 * n - 2 * Real.log n)) /
          Real.sqrt (2 * Real.log n))
      atTop id (fun n => pairLaw (symmetricGroup n)) (gaussianReal 0 1) := by
  have h := LimitTheorems.slutsky_add uniform_second_gaussian uniform_excess_vanishes
    (fun _ => (measurable_of_countable _).aemeasurable)
  apply h.congr (T := id)
  · intro n
    exact Filter.Eventually.of_forall fun p => by
      have he := congrArg (fun z : ℤ => (z : ℝ))
        (productForwardStability_eq_second_excess p.1 p.2)
      push_cast at he
      dsimp only
      rw [he]
      ring
  · exact Filter.Eventually.of_forall (fun x : ℝ => by simp)

end RecordStability
