import SchubertForwardStability.Paper.Backward.Law
import SchubertForwardStability.Paper.Backward.ClippedUniform
import SchubertForwardStability.Paper.Backward.ClippedGrassmannian
import SchubertForwardStability.Paper.Backward.ClippedBoolean
import SchubertForwardStability.LimitTheorems.Convergence.IdentTransfer

/-! # Asymptotics of backward stability

For `n ≥ 1`, `BS(u,v) + n` has the law of `max(n, FS(u,v))` in each of the three families, and the
clipping at `n` is small: its mean is at most `1/n` for uniform permutations, exponentially small
for Grassmannian permutations, and at most `1/3` for Boolean permutations. The asymptotic results
for forward stability therefore give those for backward stability.

## Main results

* `uniform_backward_expectation`, `uniform_backward_gaussian`: for `u, v` uniform in `S_n`,
  `𝔼[BS] = n - 2 log n - 2γ + c + o(1)` with `c ∈ [1, π²/6]`, and
  `(BS - (n - 2 log n))/√(2 log n) → N(0,1)`.
* `grassmannian_backward_expectation`, `grassmannian_backward_gaussian`: for Grassmannian
  permutations, `𝔼[BS] = n/2 - √n/(2√π) - 2 + o(1)`, and `(BS - n/2)/√n → -½ max(Z₁, Z₂)`.
* `boolean_backward_expectation`: for Boolean permutations, `𝔼[BS] = O(1)`.
* `backward_asymptotics`: Corollary 6.4, the three families together, with the uniform constant
  shared with forward stability.

## References

A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
products*, arXiv:2604.02964 (2026), Section 6.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology

/-- For `n ≥ 1`, any measurable function of `BS + n` has the law of the same function of the
clipped forward stability. -/
theorem backward_identDistrib_comp {n : ℕ} (hn : 1 ≤ n) (W : Finset (FinitaryPerm ℕ+))
    (hW : W = symmetricGroup n ∨ W = grassmannian n ∨ W = boolean n) (g : ℝ → ℝ) :
    IdentDistrib (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
        g (max (n : ℝ) (productForwardStability p.1 p.2 : ℝ)))
      (fun p => g ((productBackStability p.1 p.2 : ℝ) + n)) (pairLaw W) (pairLaw W) := by
  have h := ((backward_identDistrib hn W hW).comp
    (measurable_of_countable (fun k : ℕ => g (k : ℝ)))).symm
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_max] using h

/-- The expected backward stability is the expected clipped forward stability minus `n`. -/
theorem integral_backward_eq {n : ℕ} (hn : 1 ≤ n) (W : Finset (FinitaryPerm ℕ+))
    (hW : W = symmetricGroup n ∨ W = grassmannian n ∨ W = boolean n) :
    ∫ p, (productBackStability p.1 p.2 : ℝ) ∂pairLaw W =
      (∫ p, max (n : ℝ) (productForwardStability p.1 p.2 : ℝ) ∂pairLaw W) - n := by
  have hne : W.Nonempty := by
    rcases hW with rfl | rfl | rfl
    · exact ⟨1, one_mem_symmetricGroup n⟩
    · exact ⟨1, one_mem_grassmannian n⟩
    · exact ⟨1, one_mem_boolean n⟩
  have := isProbabilityMeasure_pairLaw hne
  have h := (backward_identDistrib_comp hn W hW id).integral_eq
  simp only [id_eq] at h
  rw [h, integral_add (integrable_pairLaw W _) (integrable_pairLaw W _), integral_const,
    probReal_univ, smul_eq_mul, one_mul]
  ring

/-- For uniform permutations, `𝔼[BS(u,v)] = n - 2 log n - 2γ + c + o(1)` with
`c ∈ [1, π²/6]`. -/
theorem uniform_backward_expectation :
    ∃ c ∈ Set.Icc (1 : ℝ) (Real.pi ^ 2 / 6),
      Tendsto (fun n : ℕ =>
        (∫ p, (productBackStability p.1 p.2 : ℝ) ∂pairLaw (symmetricGroup n)) -
          (n - 2 * Real.log n - 2 * Real.eulerMascheroniConstant + c)) atTop (𝓝 0) := by
  obtain ⟨c, hc, -, h⟩ := uniform_clipped_expectation
  refine ⟨c, hc, h.congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [integral_backward_eq hn _ (Or.inl rfl)]
  ring

/-- For uniform permutations, `(BS(u,v) - (n - 2 log n))/√(2 log n)` converges in distribution
to the standard normal law. -/
theorem uniform_backward_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        ((productBackStability p.1 p.2 : ℝ) - (n - 2 * Real.log n)) /
          Real.sqrt (2 * Real.log n))
      atTop id (fun n => pairLaw (symmetricGroup n)) (gaussianReal 0 1) := by
  refine LimitTheorems.tendstoInDistribution_of_identDistrib' uniform_clipped_gaussian
    (fun _ => (measurable_of_countable _).aemeasurable) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h := backward_identDistrib_comp hn _ (Or.inl rfl)
    (fun x => (x - (2 * n - 2 * Real.log n)) / Real.sqrt (2 * Real.log n))
  convert h using 2 with p
  ring

/-- For Grassmannian permutations, `𝔼[BS(u,v)] = n/2 - √n/(2√π) - 2 + o(1)`. -/
theorem grassmannian_backward_expectation :
    Tendsto (fun n : ℕ =>
      (∫ p, (productBackStability p.1 p.2 : ℝ) ∂pairLaw (grassmannian n)) -
        ((1 : ℝ) / 2 * n - Real.sqrt n / (2 * Real.sqrt Real.pi) - 2)) atTop (𝓝 0) := by
  refine grassmannian_clipped_expectation.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [integral_backward_eq hn _ (Or.inr (Or.inl rfl))]
  ring

/-- For Grassmannian permutations, `(BS(u,v) - n/2)/√n` converges in distribution to
`-½ max(Z₁, Z₂)` for independent standard normal `Z₁, Z₂`. -/
theorem grassmannian_backward_gaussian :
    TendstoInDistribution
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        ((productBackStability p.1 p.2 : ℝ) - (1 : ℝ) / 2 * n) / Real.sqrt n)
      atTop (fun p : ℝ × ℝ => -(1 / 2 : ℝ) * max p.1 p.2)
      (fun n => pairLaw (grassmannian n)) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  refine LimitTheorems.tendstoInDistribution_of_identDistrib'
    grassmannian_clipped_gaussian (fun _ => (measurable_of_countable _).aemeasurable) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h := backward_identDistrib_comp hn _ (Or.inr (Or.inl rfl))
    (fun x => (x - (3 : ℝ) / 2 * n) / Real.sqrt n)
  convert h using 2 with p
  ring

/-- For Boolean permutations, `𝔼[BS(u,v)] = O(1)`. -/
theorem boolean_backward_expectation :
    IsBigO atTop (fun n : ℕ => ∫ p, (productBackStability p.1 p.2 : ℝ) ∂pairLaw (boolean n))
      (fun _ => (1 : ℝ)) := by
  refine boolean_clipped_expectation.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [integral_backward_eq hn _ (Or.inr (Or.inr rfl))]

/-- Corollary 6.4: the asymptotics of backward stability in the three families. For uniform
permutations the expansion of `𝔼[BS(u,v)]` has the same constant `c ∈ [1, π²/6]` as that of
`𝔼[FS(u,v)]`. -/
theorem backward_asymptotics :
    (∃ c ∈ Set.Icc (1 : ℝ) (Real.pi ^ 2 / 6),
      Tendsto (fun n : ℕ =>
        (∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (symmetricGroup n)) -
          (2 * n - 2 * Real.log n - 2 * Real.eulerMascheroniConstant + c)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        (∫ p, (productBackStability p.1 p.2 : ℝ) ∂pairLaw (symmetricGroup n)) -
          (n - 2 * Real.log n - 2 * Real.eulerMascheroniConstant + c)) atTop (𝓝 0)) ∧
    TendstoInDistribution
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        ((productBackStability p.1 p.2 : ℝ) - (n - 2 * Real.log n)) /
          Real.sqrt (2 * Real.log n))
      atTop id (fun n => pairLaw (symmetricGroup n)) (gaussianReal 0 1) ∧
    Tendsto (fun n : ℕ =>
      (∫ p, (productBackStability p.1 p.2 : ℝ) ∂pairLaw (grassmannian n)) -
        ((1 : ℝ) / 2 * n - Real.sqrt n / (2 * Real.sqrt Real.pi) - 2)) atTop (𝓝 0) ∧
    TendstoInDistribution
      (fun (n : ℕ) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) =>
        ((productBackStability p.1 p.2 : ℝ) - (1 : ℝ) / 2 * n) / Real.sqrt n)
      atTop (fun p : ℝ × ℝ => -(1 / 2 : ℝ) * max p.1 p.2)
      (fun n => pairLaw (grassmannian n)) ((gaussianReal 0 1).prod (gaussianReal 0 1)) ∧
    IsBigO atTop (fun n : ℕ => ∫ p, (productBackStability p.1 p.2 : ℝ) ∂pairLaw (boolean n))
      (fun _ => (1 : ℝ)) := by
  refine ⟨?_, uniform_backward_gaussian, grassmannian_backward_expectation,
    grassmannian_backward_gaussian, boolean_backward_expectation⟩
  obtain ⟨c, hc, hF, h⟩ := uniform_clipped_expectation
  refine ⟨c, hc, hF, h.congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [integral_backward_eq hn _ (Or.inl rfl)]
  ring

end RecordStability
