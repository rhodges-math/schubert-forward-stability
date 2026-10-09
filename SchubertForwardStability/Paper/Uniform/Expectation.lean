import SchubertForwardStability.Paper.Uniform.PrefixWalk
import SchubertForwardStability.Paper.Uniform.MaximumGap
import SchubertForwardStability.Paper.Uniform.Means
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! # The additive expectation constant for uniform product stability

For independent uniform permutations `u, v` of `S_n`, the mean of `FS(u,v)` is
`2n - 2*log(n) - 2*γ + c + o(1)` for a constant `c` in `[1, π^2/6]`. The mean equals
`2n + 1 - 2*H_n`, plus the mean ambient overshoot, which increases to a limit in
`[0, π^2/6 - 1]`, minus the mean gap between the ambient and intrinsic walk maxima, which
tends to zero.

## Main results

* `RecordStability.uniform_product_expectation`: the expectation asymptotic.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Theorem 1.3 and Proposition 3.6.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

private theorem integral_pair_add (n : ℕ)
    (f g : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ → ℝ) :
    (∫ p, f p + g p ∂pairLaw (symmetricGroup n)) =
      (∫ p, f p ∂pairLaw (symmetricGroup n)) +
        ∫ p, g p ∂pairLaw (symmetricGroup n) :=
  integral_uniform_finset_add _ _ _

private theorem integral_pair_sub (n : ℕ)
    (f g : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ → ℝ) :
    (∫ p, f p - g p ∂pairLaw (symmetricGroup n)) =
      (∫ p, f p ∂pairLaw (symmetricGroup n)) -
        ∫ p, g p ∂pairLaw (symmetricGroup n) :=
  integral_uniform_finset_sub _ _ _

/-- Positive-size uniform ambient overshoots increase to a constant within the Basel tail. -/
theorem uniform_ambient_overshoot_limit :
    let a : ℕ → ℝ := fun n => ∫ p,
      ((recordWalkMaxAt n p.1 p.2 - recordWalk p.1 p.2 2 : ℤ) : ℝ)
        ∂pairLaw (symmetricGroup n)
    MonotoneOn a (Set.Ici 1) ∧
      (∀ n : ℕ, 1 ≤ n → a n ∈ Set.Icc (0 : ℝ) (Real.pi ^ 2 / 6 - 1)) ∧
      ∃ C ∈ Set.Icc (0 : ℝ) (Real.pi ^ 2 / 6 - 1), Tendsto a atTop (𝓝 C) := by
  dsimp only
  refine ⟨integral_uniform_ambient_monotone, fun _ hn => integral_uniform_ambient_bounds hn,
    ?_⟩
  let b : ℕ → ℝ := fun n => ∫ p,
    ((recordWalkMaxAt (n + 1) p.1 p.2 - recordWalk p.1 p.2 2 : ℤ) : ℝ)
      ∂pairLaw (symmetricGroup (n + 1))
  have hb : Monotone b := by
    intro m n hmn
    exact integral_uniform_ambient_monotone
      (by change 1 ≤ m + 1; omega) (by change 1 ≤ n + 1; omega) (by omega)
  have hB : BddAbove (Set.range b) := by
    refine ⟨Real.pi ^ 2 / 6 - 1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (integral_uniform_ambient_bounds (by omega : 1 ≤ n + 1)).2
  have hlo : 0 ≤ iSup b :=
    (integral_uniform_ambient_bounds (by omega : 1 ≤ 0 + 1)).1.trans (le_ciSup hB 0)
  have hhi : iSup b ≤ Real.pi ^ 2 / 6 - 1 := by
    apply ciSup_le
    intro n
    exact (integral_uniform_ambient_bounds (by omega : 1 ≤ n + 1)).2
  refine ⟨iSup b, ⟨hlo, hhi⟩, ?_⟩
  exact (tendsto_add_atTop_iff_nat 1).mp (tendsto_atTop_ciSup hb hB)

/-- Product expectation is the second walk mean plus ambient overshoot less the maximum gap. -/
theorem integral_uniform_product_decomposition {n : ℕ} (hn : 1 ≤ n) :
    (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (symmetricGroup n)) =
      2 * n + 1 - 2 * (harmonic n : ℝ) +
        (∫ p, ((recordWalkMaxAt n p.1 p.2 - recordWalk p.1 p.2 2 : ℤ) : ℝ)
          ∂pairLaw (symmetricGroup n)) -
        ∫ p, ((recordWalkMaxAt n p.1 p.2 - recordWalkMax p.1 p.2 : ℤ) : ℝ)
          ∂pairLaw (symmetricGroup n) := by
  have he : (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
      (productForwardStability p.1 p.2 : ℝ)) =
      (fun p => (recordWalk p.1 p.2 2 : ℝ) +
        ((recordWalkMaxAt n p.1 p.2 - recordWalk p.1 p.2 2 : ℤ) : ℝ) -
        ((recordWalkMaxAt n p.1 p.2 - recordWalkMax p.1 p.2 : ℤ) : ℝ)) := by
    funext p
    have hprod : (productForwardStability p.1 p.2 : ℝ) =
        (recordWalkMax p.1 p.2 : ℝ) := by
      rw [productForwardStability_eq_recordBound]
      rfl
    rw [hprod]
    push_cast
    ring
  rw [he, integral_pair_sub, integral_pair_add,
    integral_uniform_walk n 2 (by change 2 ≤ n + 1; omega)]
  norm_num [harmonic]
  ring

/-- Uniform product stability has an additive limiting constant between one and the Basel sum. -/
theorem uniform_product_expectation :
    ∃ c ∈ Set.Icc (1 : ℝ) (Real.pi ^ 2 / 6),
      Tendsto (fun n : ℕ =>
        (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (symmetricGroup n)) -
          (2 * n - 2 * Real.log n - 2 * Real.eulerMascheroniConstant + c)) atTop (𝓝 0) := by
  obtain ⟨_, _, C, hC, hlim⟩ := uniform_ambient_overshoot_limit
  refine ⟨1 + C, ⟨by linarith [hC.1], by linarith [hC.2]⟩, ?_⟩
  have hh := Real.tendsto_harmonic_sub_log.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.eulerMascheroniConstant)
      atTop (𝓝 Real.eulerMascheroniConstant))
  have ha := hlim.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C))
  have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (-2 : ℝ)) atTop (𝓝 (-2))).mul
    hh).add ha |>.sub tendsto_integral_uniform_maximum_gap
  simp only [sub_self, mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [integral_uniform_product_decomposition hn]
  ring

end RecordStability
