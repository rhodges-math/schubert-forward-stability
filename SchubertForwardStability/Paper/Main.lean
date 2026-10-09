import SchubertForwardStability.Paper.Walk.Basic
import SchubertForwardStability.Paper.Grassmannian.TotalVariation
import SchubertForwardStability.Paper.Boolean.SixDecay
import SchubertForwardStability.Paper.Boolean.Examples
import SchubertForwardStability.Paper.Walk.Tails
import SchubertForwardStability.Paper.Walk.Overshoot
import SchubertForwardStability.Paper.Uniform.Overshoot
import SchubertForwardStability.Paper.Uniform.Means
import SchubertForwardStability.Paper.Uniform.Moments
import SchubertForwardStability.Paper.Uniform.Variance
import SchubertForwardStability.Paper.Uniform.CentralLimit
import SchubertForwardStability.Paper.Uniform.LogScale
import SchubertForwardStability.Paper.Uniform.PairGaussian
import SchubertForwardStability.Paper.Uniform.SecondGaussian
import SchubertForwardStability.Paper.Uniform.Excess
import SchubertForwardStability.Paper.Uniform.ProductGaussian
import SchubertForwardStability.Paper.Uniform.MaximumGap
import SchubertForwardStability.Paper.Uniform.AmbientBounds
import SchubertForwardStability.Paper.Uniform.PrefixWalk
import SchubertForwardStability.Paper.Uniform.Expectation
import SchubertForwardStability.Paper.Grassmannian.Residual
import SchubertForwardStability.Paper.Grassmannian.Records
import SchubertForwardStability.Paper.Grassmannian.Bounds
import SchubertForwardStability.Paper.Grassmannian.Identity
import SchubertForwardStability.Paper.Grassmannian.ResidualEvents
import SchubertForwardStability.Paper.Grassmannian.ResidualMeans
import SchubertForwardStability.Paper.Grassmannian.CardMean
import SchubertForwardStability.Paper.Grassmannian.Transfer
import SchubertForwardStability.Paper.Grassmannian.Expectation
import SchubertForwardStability.Paper.Grassmannian.Negligible
import SchubertForwardStability.Paper.Grassmannian.CardGaussian
import SchubertForwardStability.Paper.Grassmannian.LimitTransfer
import SchubertForwardStability.Paper.Grassmannian.ProductGaussian
import SchubertForwardStability.Paper.Conjectures
import SchubertForwardStability.Paper.RecordProbabilities
import SchubertForwardStability.Paper.Walk.Differences
import SchubertForwardStability.Paper.Boolean.Means
import SchubertForwardStability.Paper.Boolean.Drift
import SchubertForwardStability.Paper.Boolean.Terminal
import SchubertForwardStability.Paper.Boolean.Centered
import SchubertForwardStability.Paper.Boolean.StabilityLower
import SchubertForwardStability.Paper.Boolean.MaximumExcess
import SchubertForwardStability.Paper.Boolean.LogTail
import SchubertForwardStability.Paper.Boolean.Expectation
import SchubertForwardStability.Paper.Boolean.SamplerCost
import SchubertForwardStability.Paper.Boolean.TagConditioning
import SchubertForwardStability.Paper.Boolean.TagSuffixEvents
import SchubertForwardStability.Paper.Boolean.TagFutureEvents
import SchubertForwardStability.Paper.Boolean.TagMixing
import SchubertForwardStability.Paper.Boolean.TagFields
import SchubertForwardStability.Paper.Boolean.TagCoefficients
import SchubertForwardStability.Paper.Boolean.BooleanCoefficients
import SchubertForwardStability.Paper.Catalan.Stability
import SchubertForwardStability.Paper.Backward.Law
import SchubertForwardStability.Paper.Backward.Asymptotics

/-! # Records and forward stability

This module imports the formalization of *The record statistic and forward stability of
Schubert products* (Andrew Hardt, Reuven Hodges and Hanzhang Yin, 2026), arXiv:2604.02964,
together with the general libraries it uses. For independent uniform permutations `u, v`
from the symmetric, Grassmannian and Boolean families, it describes the forward stability
`FS(u,v)` of the Schubert product `𝔖_u 𝔖_v` through the records of `u` and `v`.

## Main results

* `RecordStability.record_probability_families`: record probabilities in the three families
  (Theorem 1.1).
* `SchubertPolynomial.productForwardStability_eq_recordBound`: the record formula (1.2) for
  `FS(u,v)`.
* `RecordStability.uniform_product_expectation`, `RecordStability.uniform_product_gaussian`:
  the mean and the Gaussian limit for uniform permutations (Theorem 1.3).
* `RecordStability.grassmannian_expectation`, `RecordStability.grassmannian_gaussian`: the
  mean and the limit law for Grassmannian permutations (Theorem 1.4).
* `RecordStability.boolean_product_expectation`: the mean for Boolean permutations
  (Theorem 1.5).

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Theorems 1.1, 1.3, 1.4 and 1.5.
-/
