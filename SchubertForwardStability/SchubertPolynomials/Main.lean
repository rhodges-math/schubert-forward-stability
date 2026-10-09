import SchubertForwardStability.SchubertPolynomials.ForMathlib.RootRegular
import SchubertForwardStability.SchubertPolynomials.ForMathlib.PositiveDegrees
import SchubertForwardStability.SchubertPolynomials.Divided.Exponents
import SchubertForwardStability.SchubertPolynomials.Divided.Monomials
import SchubertForwardStability.SchubertPolynomials.Divided.Basic
import SchubertForwardStability.SchubertPolynomials.Divided.Positive
import SchubertForwardStability.SchubertPolynomials.Divided.Naturality
import SchubertForwardStability.SchubertPolynomials.Divided.FiniteRelations
import SchubertForwardStability.SchubertPolynomials.Divided.FiniteVariables
import SchubertForwardStability.SchubertPolynomials.Divided.Relations
import SchubertForwardStability.SchubertPolynomials.Divided.Words
import SchubertForwardStability.SchubertPolynomials.Divided.FiniteWords
import SchubertForwardStability.SchubertPolynomials.Divided.Independence
import SchubertForwardStability.SchubertPolynomials.Divided.Unreduced
import SchubertForwardStability.SchubertPolynomials.Divided.Multiplication
import SchubertForwardStability.SchubertPolynomials.Divided.MonomialStep
import SchubertForwardStability.SchubertPolynomials.Divided.Homogeneous
import SchubertForwardStability.SchubertPolynomials.Stability.Staircase
import SchubertForwardStability.SchubertPolynomials.Stability.Cycle
import SchubertForwardStability.SchubertPolynomials.Stability.Construction
import SchubertForwardStability.SchubertPolynomials.Stability.Ambient
import SchubertForwardStability.SchubertPolynomials.Stability.Extraction
import SchubertForwardStability.SchubertPolynomials.Stability.Homogeneous
import SchubertForwardStability.SchubertPolynomials.Stability.Duality
import SchubertForwardStability.SchubertPolynomials.Stability.Divided
import SchubertForwardStability.SchubertPolynomials.Basis.ArtinSpan
import SchubertForwardStability.SchubertPolynomials.Basis.ArtinOperators
import SchubertForwardStability.SchubertPolynomials.Basis.ArtinSchubert
import SchubertForwardStability.SchubertPolynomials.Basis.ArtinMonomials
import SchubertForwardStability.SchubertPolynomials.Basis.ArtinCoordinates
import SchubertForwardStability.SchubertPolynomials.Basis.DualFamily
import SchubertForwardStability.SchubertPolynomials.Basis.FiniteIndices
import SchubertForwardStability.SchubertPolynomials.Basis.Finite
import SchubertForwardStability.SchubertPolynomials.Basis.Global
import SchubertForwardStability.SchubertPolynomials.Basis.Support
import SchubertForwardStability.SchubertPolynomials.Basis.Lehmer
import SchubertForwardStability.SchubertPolynomials.Products.Constants
import SchubertForwardStability.SchubertPolynomials.Products.Forward
import SchubertForwardStability.SchubertPolynomials.Products.Degrees
import SchubertForwardStability.SchubertPolynomials.Products.Naturality
import SchubertForwardStability.SchubertPolynomials.Stability.ShiftRelation
import SchubertForwardStability.SchubertPolynomials.Stability.RightShift
import SchubertForwardStability.SchubertPolynomials.Backward.Witnesses
import SchubertForwardStability.SchubertPolynomials.Stability.Simple
import SchubertForwardStability.SchubertPolynomials.Stability.LinearOperators
import SchubertForwardStability.SchubertPolynomials.Stability.LinearExtraction
import SchubertForwardStability.SchubertPolynomials.Stability.MonkCoefficients
import SchubertForwardStability.SchubertPolynomials.Stability.Recurrence.TransitionTerms
import SchubertForwardStability.SchubertPolynomials.Stability.Recurrence.Transition
import SchubertForwardStability.SchubertPolynomials.Stability.Positive
import SchubertForwardStability.SchubertPolynomials.Stability.Recurrence.SuffixDegrees
import SchubertForwardStability.SchubertPolynomials.Products.RecordBound
import SchubertForwardStability.SchubertPolynomials.Products.RecordFactors
import SchubertForwardStability.SchubertPolynomials.Coinvariants.SymmetricIdeal
import SchubertForwardStability.SchubertPolynomials.Coinvariants.SignedVariables
import SchubertForwardStability.SchubertPolynomials.Coinvariants.SymmetricFunctionals
import SchubertForwardStability.SchubertPolynomials.Coinvariants.CompleteSymmetric
import SchubertForwardStability.SchubertPolynomials.Coinvariants.TriangularRelations
import SchubertForwardStability.SchubertPolynomials.Coinvariants.CompleteMonic
import SchubertForwardStability.SchubertPolynomials.Coinvariants.ArtinRelations
import SchubertForwardStability.SchubertPolynomials.Coinvariants.AscendingRemainder
import SchubertForwardStability.SchubertPolynomials.Coinvariants.ArtinRemainder
import SchubertForwardStability.SchubertPolynomials.Coinvariants.CoordinateIdeal
import SchubertForwardStability.SchubertPolynomials.Coinvariants.FiniteArtinLift
import SchubertForwardStability.SchubertPolynomials.Coinvariants.QuotientBasis
import SchubertForwardStability.SchubertPolynomials.Coinvariants.LongestProducts
import SchubertForwardStability.SchubertPolynomials.Stability.ShiftConstants
import SchubertForwardStability.SchubertPolynomials.Stability.ShiftForward
import SchubertForwardStability.SchubertPolynomials.Stability.RightShiftIterate
import SchubertForwardStability.SchubertPolynomials.Backward.Stabilization
import SchubertForwardStability.SchubertPolynomials.Backward.Identity

/-! # Schubert polynomials and their products

This module imports the whole Schubert polynomials library. It covers divided differences on
`MvPolynomial ℕ+ R`; Schubert polynomials over any commutative ring, their stability and the
fact that they form a basis; Schubert structure constants, with Monk-type coefficients, the
coinvariant algebra, the symmetry under conjugation by `w_0` and Li's shift stability; and
the forward and back stability of a product of two Schubert polynomials, with the record
formula of Hardt and Wallach for forward stability.

## Main results

* `SchubertPolynomial.schubertBasis`: the Schubert polynomials form a basis of the polynomial
  ring.
* `SchubertPolynomial.structureCoefficients`: the structure constants `c^w_{u,v}`.
* `SchubertPolynomial.structureConst_conjugate_longest`: `w_0`-symmetry of the structure
  constants.
* `SchubertPolynomial.structureConst_shiftRight`: `c^{1×w}_{1×u,1×v} = c^w_{u,v}` (Li).
* `SchubertPolynomial.schubert_degreeOf_eq_suffixCount`: the degree of `𝔖_w` in `x_i` is
  the suffix non-record count.
* `SchubertPolynomial.productForwardStability_eq_recordBound`:
  `FS(u,v) = max (Λ_i(u) + Λ_i(v) + i - 1)` (Hardt and Wallach).
* `SchubertPolynomial.productBackStability`: backward stability, the least number of right
  shifts from which the product support is stable, and `productBackStability_eq_sSup`.
* `SchubertPolynomial.productBackStability_add_eq_max`:
  `BS(u,v) + n = max(n, FS(w₀uw₀, w₀vw₀))` for `u, v ∈ S_n` with `n ≥ 1`.
-/
