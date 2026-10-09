import SchubertForwardStability.Paper.Catalan.RecordLaws
import SchubertForwardStability.SchubertPolynomials.Products.RecordFactors

/-! # Forward-stability laws in the two Catalan avoidance classes

By the record formula, product forward stability factors through the two record sets.
Their equal fiber counts therefore give identical forward-stability laws, point
probabilities and expectations for independent uniform pairs from the two classes.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Section 8.
-/

namespace RecordStability

open FinitaryPerm PermutationPattern SchubertPolynomial MeasureTheory ProbabilityTheory
open scoped Classical

/-- Independent uniform Catalan pairs have identically distributed product forward stability. -/
theorem catalan_stability_identDistrib (n : ℕ) :
    IdentDistrib (fun p => productForwardStability p.1 p.2)
      (fun p => productForwardStability p.1 p.2)
      (pairLaw (avoiding n p132)) (pairLaw (avoiding n p231)) := by
  apply identDistrib_pairFactor_of_fibers _ _ (recordSet n) (recordSet n)
    (recordPairBound n) _ _
  · intro R
    convert card_recordSet_catalan_eq n R using 1 <;> congr 1 <;> ext w <;> simp
  · intro p hp hq
    exact productForward_eq_recordPairBound ((mem_avoiding n p132 p.1).mp hp).1
      ((mem_avoiding n p132 p.2).mp hq).1
  · intro p hp hq
    exact productForward_eq_recordPairBound ((mem_avoiding n p231 p.1).mp hp).1
      ((mem_avoiding n p231 p.2).mp hq).1

/-- Every integer-valued forward-stability event has the same Catalan pair probability. -/
theorem catalan_stability_probability (n : ℕ) (t : ℤ) :
    (pairLaw (avoiding n p132)).real {p | (productForwardStability p.1 p.2 : ℤ) = t} =
      (pairLaw (avoiding n p231)).real {p | (productForwardStability p.1 p.2 : ℤ) = t} := by
  have h := ((catalan_stability_identDistrib n).comp
    (measurable_of_countable (fun k : ℕ => (k : ℤ)))).measure_mem_eq
      (measurableSet_singleton t)
  simpa only [measureReal_def, Set.preimage, Set.mem_singleton_iff, Function.comp_apply] using
    congrArg ENNReal.toReal h

/-- The mean product forward stability agrees for the two independent uniform Catalan
pairs. -/
theorem catalan_stability_expectation (n : ℕ) :
    (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (avoiding n p132)) =
      ∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (avoiding n p231) :=
  ((catalan_stability_identDistrib n).comp
    (measurable_of_countable (fun k : ℕ => (k : ℝ)))).integral_eq

/-- The two Catalan classes share product stability laws, probabilities and expectations. -/
theorem catalan_stability_law (n : ℕ) :
    IdentDistrib (fun p => productForwardStability p.1 p.2)
      (fun p => productForwardStability p.1 p.2)
      (pairLaw (avoiding n p132)) (pairLaw (avoiding n p231)) ∧
    (∀ t : ℤ, (pairLaw (avoiding n p132)).real
      {p | (productForwardStability p.1 p.2 : ℤ) = t} =
      (pairLaw (avoiding n p231)).real {p | (productForwardStability p.1 p.2 : ℤ) = t}) ∧
    (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (avoiding n p132)) =
      ∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (avoiding n p231) :=
  ⟨catalan_stability_identDistrib n, catalan_stability_probability n,
    catalan_stability_expectation n⟩

end RecordStability
