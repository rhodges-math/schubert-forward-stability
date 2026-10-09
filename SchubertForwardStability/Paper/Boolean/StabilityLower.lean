import SchubertForwardStability.Permutations.Random.BooleanForward
import SchubertForwardStability.Permutations.ForMathlib.NaturalTails
import SchubertForwardStability.SchubertPolynomials.Products.RecordBound
import Mathlib.Algebra.Field.GeomSum

/-! # Lower bound for Boolean product forward stability

The probability that two independent uniform Boolean permutations of size `n` are both
supported in `[1, n-k]` is at most `4^(-k)`, so the mean deficit of the larger support is
at most one third. By the record formula, product forward stability is at least the
support bound of each factor.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Lemma 5.30.
-/

namespace RecordStability

open FinitaryPerm SchubertPolynomial MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

private theorem quarter_sum_bound (N : ℕ) :
    ∑ t ∈ Finset.Icc 1 N, (1 / 4 : ℝ) ^ t ≤ 1 / 3 := by
  have hShift : (∑ t ∈ Finset.Icc 1 N, (1 / 4 : ℝ) ^ t) =
      ∑ k ∈ Finset.range N, (1 / 4 : ℝ) ^ (k + 1) := by
    symm
    apply Finset.sum_bij (fun k _ => k + 1)
    · intro k hk
      have h := Finset.mem_range.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k hk l hl he
      omega
    · intro t ht
      obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp ht
      exact ⟨t - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k _
      rfl
  rw [hShift]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul, geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
  have hP : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ N := by positivity
  norm_num [div_eq_mul_inv]
  nlinarith

/-- The expected deficit of the maximum independent Boolean support is at most one third. -/
theorem integral_boolean_pair_deficit_le (n : ℕ) (hn : 1 ≤ n) :
    (∫ p, ((n - max p.1.forwardStability p.2.forwardStability : ℕ) : ℝ)
      ∂pairLaw (boolean n)) ≤ 1 / 3 := by
  have hX : ∀ p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+,
      n - max p.1.forwardStability p.2.forwardStability ≤ n - 1 := by
    intro p
    have hp := p.1.one_le_forwardStability
    have hm := le_max_left p.1.forwardStability p.2.forwardStability
    omega
  have hTail := integral_uniform_nat_tails ((boolean n).product (boolean n))
    (fun p => n - max p.1.forwardStability p.2.forwardStability) (n - 1)
    (fun p _ => hX p)
  change (∫ p, ((n - max p.1.forwardStability p.2.forwardStability : ℕ) : ℝ)
    ∂pairLaw (boolean n)) = _ at hTail
  rw [hTail]
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 (n - 1), (1 / 4 : ℝ) ^ t := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp ht
      exact boolean_pair_deficit_le n t hl (by omega)
    _ ≤ _ := quarter_sum_bound (n - 1)

/-- The expected maximum independent Boolean support is at least size minus one third. -/
theorem integral_boolean_forward_max_lower (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) - (1 / 3 : ℝ) ≤
      ∫ p, ((max p.1.forwardStability p.2.forwardStability : ℕ) : ℝ)
        ∂pairLaw (boolean n) := by
  have hEqual :
      (∫ p, ((max p.1.forwardStability p.2.forwardStability : ℕ) : ℝ)
        ∂pairLaw (boolean n)) = (n : ℝ) -
      ∫ p, ((n - max p.1.forwardStability p.2.forwardStability : ℕ) : ℝ)
        ∂pairLaw (boolean n) := by
    calc
      _ = ∫ p, (n : ℝ) - ((n - max p.1.forwardStability p.2.forwardStability : ℕ) : ℝ)
          ∂pairLaw (boolean n) := by
        apply integral_uniform_finset_congr
        intro p hp
        obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
        have hu' := (forwardStability_le_iff p.1 hn).mpr ((mem_boolean n p.1).mp hu).1
        have hv' := (forwardStability_le_iff p.2 hn).mpr ((mem_boolean n p.2).mp hv).1
        rw [Nat.cast_sub (max_le hu' hv')]
        ring
      _ = (∫ _p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+, (n : ℝ) ∂pairLaw (boolean n)) -
          ∫ p, ((n - max p.1.forwardStability p.2.forwardStability : ℕ) : ℝ)
            ∂pairLaw (boolean n) := integral_uniform_finset_sub _ _ _
      _ = _ := by simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hDeficit := integral_boolean_pair_deficit_le n hn
  linarith

/-- Boolean Schubert product forward stability has expectation at least size minus one third. -/
theorem boolean_stability_lower (n : ℕ) :
    (n : ℝ) - (1 / 3 : ℝ) ≤
      ∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (boolean n) := by
  by_cases hZero : n = 0
  · subst n
    have h : (0 : ℝ) ≤
        ∫ p, (productForwardStability p.1 p.2 : ℝ) ∂pairLaw (boolean 0) :=
      integral_nonneg (fun p => Nat.cast_nonneg (productForwardStability p.1 p.2))
    norm_num
    linarith
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hZero
    apply (integral_boolean_forward_max_lower n hn).trans
    apply integral_uniform_finset_mono
    intro p _
    have h := max_forward_le_pairSuffixBound p.1 p.2
    rw [← productForwardStability_eq_suffixBound] at h
    exact_mod_cast h

end RecordStability
