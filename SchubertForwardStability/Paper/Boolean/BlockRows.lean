import SchubertForwardStability.Paper.Boolean.BooleanCoefficients
import SchubertForwardStability.Paper.Boolean.Centered
import SchubertForwardStability.StrongMixing.Bernstein.FiniteTails

/-! # Integer extensions of finite centered Boolean rows

The constant extension keeps zero means, the bound two and geometric
mixing. Its sums over contiguous integer coordinates are the corresponding
positive-position centered increment blocks.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory StrongMixing
open scoped Classical BigOperators

/-- The zero extension of the centered Boolean row of ambient size N+1. -/
noncomputable def booleanCenteredRow (N : ℕ) :
    ℤ → FinitaryPerm ℕ+ × FinitaryPerm ℕ+ → ℝ :=
  constantExtension (fun j : Fin (N + 1) => centeredBooleanStep (N + 1) j.val.succPNat) 0

/-- The integer extension is measurable, centered and essentially bounded by two at each time. -/
theorem booleanCenteredRow_moments (N : ℕ) (i : ℤ) :
    AEMeasurable (booleanCenteredRow N i) (pairLaw (boolean (N + 1))) ∧
    (∫ p, booleanCenteredRow N i p ∂pairLaw (boolean (N + 1))) = 0 ∧
    (∀ᵐ p ∂pairLaw (boolean (N + 1)), |booleanCenteredRow N i p| ≤ 2) := by
  by_cases hi : 0 ≤ i ∧ i < (N + 1 : ℤ)
  · have he : booleanCenteredRow N i = centeredBooleanStep (N + 1) i.toNat.succPNat := by
      funext p
      dsimp only [booleanCenteredRow, constantExtension]
      rw [dite_eq_left hi]
    rw [he]
    exact ⟨(measurable_of_countable _).aemeasurable,
      integral_centeredBooleanStep _ _,
      Filter.Eventually.of_forall (abs_centeredBooleanStep_le _ _)⟩
  · have he : booleanCenteredRow N i = fun _ => 0 := by
      funext p
      dsimp only [booleanCenteredRow, constantExtension]
      rw [dite_eq_right hi]
    rw [he]
    exact ⟨aemeasurable_const, integral_zero _ _,
      Filter.Eventually.of_forall (fun _ => by norm_num)⟩

/-- The extended centered row has the geometric coefficient with rate log(6)/12. -/
theorem booleanCenteredRow_mixing (N h : ℕ) (hh : 1 ≤ h) :
    mixingCoeff (pairLaw (boolean (N + 1))) (booleanCenteredRow N) h ≤
      Real.exp (-2 * (Real.log 6 / 12) * h) := by
  have hm := booleanCentered_mixing N h hh
  rw [six_mixing_rate_eq] at hm
  exact hm

/-- A contiguous integer-coordinate sum equals the centered positive-position block. -/
theorem booleanCenteredRow_sum (N a k : ℕ) (ha : a + k ≤ N)
    (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) :
    (∑ i ∈ (Finset.range k).image (fun t : ℕ => ((a + t : ℕ) : ℤ)),
      booleanCenteredRow N i p) =
      ∑ t ∈ Finset.range k, centeredBooleanStep (N + 1) (a + t).succPNat p := by
  rw [Finset.sum_image (by
    intro t _ s _ h
    change ((a + t : ℕ) : ℤ) = ((a + s : ℕ) : ℤ) at h
    have hNat : a + t = a + s := by exact_mod_cast h
    omega)]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  have hi : 0 ≤ ((a + t : ℕ) : ℤ) ∧ ((a + t : ℕ) : ℤ) < (N + 1 : ℤ) := by
    constructor
    · exact Int.natCast_nonneg _
    · exact_mod_cast (show a + t < N + 1 by omega)
  simp only [booleanCenteredRow, constantExtension, dite_eq_left hi, Int.toNat_natCast]

/-- The concrete extended Boolean row satisfies the finite-set one-sided MPR lower tail. -/
theorem booleanCenteredRow_lower_tail (N : ℕ) (S : Finset ℤ) (hk : 4 ≤ S.card)
    {x : ℝ} (hx : 0 ≤ x) :
    (pairLaw (boolean (N + 1))).real {p | (∑ i ∈ S, booleanCenteredRow N i p) ≤ -x} ≤
      Real.exp (-mprTailConstant (Real.log 6 / 12) * x ^ 2 /
        ((S.card : ℝ) * 2 ^ 2 + 2 * x * Real.log S.card * Real.log (Real.log S.card))) :=
  mpr_finite_lower_tail _ _ (fun i => (booleanCenteredRow_moments N i).1)
    (fun i => (booleanCenteredRow_moments N i).2.1) (by norm_num)
    (div_pos (Real.log_pos (by norm_num)) (by norm_num))
    (fun i => (booleanCenteredRow_moments N i).2.2)
    (booleanCenteredRow_mixing N) S hk hx

end RecordStability
