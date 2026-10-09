import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Rounded terminal block lengths

For a positive small parameter `u`, the natural floor of `1/(4*u)` is a
positive block length. Its lower bound and small-parameter upper bound supply
the arithmetic needed for alternating-block log-Laplace estimates.
-/

namespace StrongMixing

/-- The short-block length obtained by taking the natural floor of `1/(4*u)`.
This definition is total, including zero or negative parameters; its quantitative
estimates are stated separately for positive small parameters. -/
noncomputable def terminalBlockLength (u : ℝ) : ℕ := ⌊1 / (4 * u)⌋₊

/-- For `0 < u <= 1/8`, the rounded block length is positive, is at least
`1/(8*u)`, and satisfies `2*u*len <= 1`. These bounds include the upper endpoint. -/
theorem terminalBlockLength_bounds {u : ℝ} (hu : 0 < u) (hsmall : u ≤ 1 / 8) :
    1 ≤ terminalBlockLength u ∧
      1 / (8 * u) ≤ (terminalBlockLength u : ℝ) ∧
        2 * u * terminalBlockLength u ≤ 1 := by
  have h4 : 0 < 4 * u := by positivity
  have h8 : 0 < 8 * u := by positivity
  have hf := Nat.floor_le (by positivity : 0 ≤ 1 / (4 * u))
  have hl := Nat.lt_floor_add_one (1 / (4 * u))
  change (terminalBlockLength u : ℝ) ≤ 1 / (4 * u) at hf
  change 1 / (4 * u) < (terminalBlockLength u : ℝ) + 1 at hl
  have hfu := (le_div_iff₀ h4).mp hf
  have hlu := (div_lt_iff₀ h4).mp hl
  have hp : 0 < terminalBlockLength u := Nat.floor_pos.mpr
    ((one_le_div h4).mpr (by linarith))
  refine ⟨by omega, ?_, ?_⟩
  · apply (div_le_iff₀ h8).mpr
    nlinarith
  · have hn : (0 : ℝ) ≤ terminalBlockLength u := Nat.cast_nonneg _
    nlinarith

end StrongMixing
