import SchubertForwardStability.LimitTheorems.Convergence.Probability
import SchubertForwardStability.LimitTheorems.Convergence.Deterministic
import SchubertForwardStability.LimitTheorems.Convergence.LawChange
import SchubertForwardStability.LimitTheorems.Convergence.FirstMoment
import SchubertForwardStability.LimitTheorems.Asymptotics.LogDecay
import SchubertForwardStability.LimitTheorems.Convergence.Slutsky
import SchubertForwardStability.LimitTheorems.Convergence.Distribution
import SchubertForwardStability.LimitTheorems.Convergence.Independent
import SchubertForwardStability.LimitTheorems.TotalVariation.Basic
import SchubertForwardStability.LimitTheorems.TotalVariation.Masses
import SchubertForwardStability.LimitTheorems.TotalVariation.Coupling
import SchubertForwardStability.LimitTheorems.TotalVariation.Product
import SchubertForwardStability.LimitTheorems.TotalVariation.Support
import SchubertForwardStability.LimitTheorems.TotalVariation.Comparison
import SchubertForwardStability.LimitTheorems.ForMathlib.ProductBounds
import SchubertForwardStability.LimitTheorems.CentralLimit.Taylor
import SchubertForwardStability.LimitTheorems.CentralLimit.MomentBounds
import SchubertForwardStability.LimitTheorems.CentralLimit.Infinitesimal
import SchubertForwardStability.LimitTheorems.CentralLimit.RowBounds
import SchubertForwardStability.LimitTheorems.CentralLimit.Lyapunov
import SchubertForwardStability.LimitTheorems.CentralLimit.Normalization
import SchubertForwardStability.LimitTheorems.CentralLimit.Truncation
import SchubertForwardStability.LimitTheorems.CentralLimit.GaussianError
import SchubertForwardStability.LimitTheorems.CentralLimit.TruncatedRows
import SchubertForwardStability.LimitTheorems.CentralLimit.Lindeberg
import SchubertForwardStability.LimitTheorems.CentralLimit.ThirdMomentTail
import SchubertForwardStability.LimitTheorems.Binomial.StirlingRate
import SchubertForwardStability.LimitTheorems.Binomial.CentralBinomial
import SchubertForwardStability.LimitTheorems.Binomial.Deviation
import SchubertForwardStability.LimitTheorems.Binomial.Chernoff
import SchubertForwardStability.LimitTheorems.Binomial.Gaussian
import SchubertForwardStability.LimitTheorems.Convergence.FiniteLawChange
import SchubertForwardStability.LimitTheorems.Convergence.IdentTransfer

/-! # Limit theorems for random variables

This module imports the whole limit theorems library. It covers convergence in probability
and Slutsky's theorem for random variables on varying probability spaces; the Lindeberg and
Lyapunov central limit theorems for triangular arrays with finite rows; the total variation
distance and maximal couplings of laws on finite sets; and binomial estimates: a Chernoff
bound, De Moivre's mean absolute deviation, a Stirling estimate of the central binomial
coefficient and the binomial central limit theorem.

## Main results

* `LimitTheorems.tendstoInDistribution_lindeberg`: Lindeberg's central limit theorem for
  triangular arrays.
* `LimitTheorems.tendstoInDistribution_lyapunov`: Lyapunov's central limit theorem.
* `LimitTheorems.slutsky_prod`: Slutsky's theorem, joint form, on varying spaces.
* `LimitTheorems.totalVariation_eq_half_sum`: total variation as half the `ℓ¹` distance.
* `LimitTheorems.exists_maximalCoupling`: a coupling attaining the total variation.
* `LimitTheorems.binomial_deviation_mean`: De Moivre's `E|S-n|` for the symmetric binomial.
* `LimitTheorems.centralBinomial_error_isBigO`: `C(2n,n)*sqrt(pi*n)/4^n = 1 + O(1/n)`.
* `LimitTheorems.tendsto_binomial_gaussian`: the normalized symmetric binomial tends to
  `N(0,1)`.
-/
