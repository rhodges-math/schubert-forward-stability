import SchubertForwardStability.Permutations.Classes.Patterns.PatternRecords
import SchubertForwardStability.Permutations.Random.Uniform
import SchubertForwardStability.SchubertPolynomials.Products.Forward
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Conjectural stability asymptotics and recursive record equivalence

These propositions state the conjectures of Sections 7 and 8. They are stated and not
proved.
-/

namespace RecordStability

open FinitaryPerm PermutationPattern MeasureTheory Filter
open scoped Classical Topology

/-- The mean product stability of two independent uniform members of a finite family. -/
noncomputable def familyStabilityMean (W : Finset (FinitaryPerm ℕ+)) : ℝ :=
  ∫ p, (SchubertPolynomial.productForwardStability p.1 p.2 : ℝ) ∂pairLaw W

/-- The refined Boolean expectation has constant term three. -/
def BooleanRefined : Prop :=
  Tendsto (fun n : ℕ => familyStabilityMean (boolean n) - ((n : ℝ) + 3)) atTop (𝓝 0)

/-- CoGrassmannian expectation has the specified square-root correction and bounded error. -/
def CoGrassmannianAsymptotic : Prop :=
  Asymptotics.IsBigO atTop
    (fun n : ℕ => familyStabilityMean (coGrassmannian n) -
      ((n : ℝ) + Real.sqrt n / Real.sqrt Real.pi)) (fun _ => (1 : ℝ))

/-- The `321`-avoiding square-root coefficient lies in the specified interval. -/
def Avoiding321Asymptotic : Prop :=
  ∃ c : ℝ, (0.92 : ℝ) ≤ c ∧ c ≤ 0.94 ∧ Asymptotics.IsBigO atTop
    (fun n : ℕ => familyStabilityMean (avoiding n p321) - ((n : ℝ) + c * Real.sqrt n))
    (fun _ => (1 : ℝ))

/-- The smooth linear coefficient lies between `1.35` and `1.40`. -/
def SmoothAsymptotic : Prop :=
  ∃ c : ℝ, (1.35 : ℝ) ≤ c ∧ c ≤ 1.40 ∧ Asymptotics.IsLittleO atTop
    (fun n : ℕ => familyStabilityMean (smooth n) - c * n) (fun n : ℕ => (n : ℝ))

/-- The Levi-spherical mean has linear coefficient `5/4` and bounded error. -/
def LeviAsymptotic : Prop :=
  Asymptotics.IsBigO atTop
    (fun n : ℕ => familyStabilityMean (leviSpherical n) - (5 / 4 : ℝ) * n)
    (fun _ => (1 : ℝ))

/-- The `231`-avoiding mean is `2n-5+o(1)`. -/
def Avoiding231Asymptotic : Prop :=
  Tendsto (fun n : ℕ => familyStabilityMean (avoiding n p231) - (2 * (n : ℝ) - 5))
    atTop (𝓝 0)

/-- The `132`-avoiding mean is `2n-5+o(1)`. -/
def Avoiding132Asymptotic : Prop :=
  Tendsto (fun n : ℕ => familyStabilityMean (avoiding n p132) - (2 * (n : ℝ) - 5))
    atTop (𝓝 0)

/-- The fireworks mean has the stated logarithmic correction with its little-o error. -/
def FireworksAsymptotic : Prop :=
  Asymptotics.IsLittleO atTop
    (fun n : ℕ => familyStabilityMean (fireworks n) -
      (2 * (n : ℝ) - 2 * (n : ℝ) / (Real.log n - Real.log (Real.log n))))
    (fun n : ℕ => (n : ℝ) / Real.log n)

/-- The nonnegative vexillary deficit has square-root order bound. -/
def VexillaryAsymptotic : Prop :=
  (∀ᶠ n : ℕ in atTop, familyStabilityMean (vexillary n) ≤ 2 * (n : ℝ)) ∧
    Asymptotics.IsBigO atTop
      (fun n : ℕ => 2 * (n : ℝ) - familyStabilityMean (vexillary n))
      (fun n : ℕ => Real.sqrt n)

/-- The covexillary correction converges to a constant between six and nine. -/
def CovexillaryAsymptotic : Prop :=
  ∃ c : ℝ, 6 ≤ c ∧ c ≤ 9 ∧
    Tendsto (fun n : ℕ => familyStabilityMean (covexillary n) - (2 * (n : ℝ) - c))
      atTop (𝓝 0)

/-- The three record-dense conjectural expectation regimes. -/
def RecordDenseRegime : Prop :=
  BooleanRefined ∧ CoGrassmannianAsymptotic ∧ Avoiding321Asymptotic

/-- The two intermediate conjectural expectation regimes. -/
def RecordIntermediateRegime : Prop := SmoothAsymptotic ∧ LeviAsymptotic

/-- The five record-sparse conjectural expectation regimes. -/
def RecordSparseRegime : Prop :=
  Avoiding231Asymptotic ∧ Avoiding132Asymptotic ∧ FireworksAsymptotic ∧
    VexillaryAsymptotic ∧ CovexillaryAsymptotic

/-- The proposed recursive criterion for record equivalence of two nontrivial patterns. -/
def RecursiveRecordEquivalence : Prop :=
  ∀ k : ℕ, ∀ π σ : PermutationPattern (k + 2), RecordEquivalent π σ ↔
    records π = records σ ∧
    (∀ n : ℕ, k + 2 ≤ n → (avoiding n π).card = (avoiding n σ).card) ∧
    (maximumPosition π = maximumPosition σ → ∀ i : Fin (k + 2),
      i ≠ maximumPosition π → RecordEquivalent (deletionMinor π i) (deletionMinor σ i)) ∧
    (4 ≤ k + 2 → records π = positions (k + 1) → records σ = positions (k + 1) →
      (maximumPosition π).val = k → (maximumPosition σ).val = k →
      π (Fin.last (k + 1)) = σ (Fin.last (k + 1)))

end RecordStability
