import SchubertForwardStability.Paper.Walk.Basic
import SchubertForwardStability.Permutations.Statistics.RecordSums
import SchubertForwardStability.Permutations.Random.NonRecords
import SchubertForwardStability.Permutations.ForMathlib.UniformIntegrals
import Mathlib.NumberTheory.Harmonic.Defs

/-! # Harmonic means of uniform record walks

## Main results

The walk expectation is its exact harmonic expression. The terminal value equals
ambient size and reciprocal-complement non-record means give the backward recurrence.

## Implementation notes

Walk values are integers and all expectations are real. Positive positions correspond
to successors of zero-based natural indices in the downward induction. Size zero is
included wherever the position bound is nonempty.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Lemma 3.3.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

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

/-- The two uniform pair coordinates have equal reciprocal-complement non-record means. -/
theorem integral_uniform_pair_nonRecord (n : ℕ) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    (∫ p, (p.1.nonRecordIndicator i : ℝ) ∂pairLaw (symmetricGroup n)) =
        (((i : ℕ) : ℝ) - 1) / (i : ℕ) ∧
      (∫ p, (p.2.nonRecordIndicator i : ℝ) ∂pairLaw (symmetricGroup n)) =
        (((i : ℕ) : ℝ) - 1) / (i : ℕ) := by
  constructor
  · calc
      _ = ∫ w, (w.nonRecordIndicator i : ℝ) ∂unif (symmetricGroup n) :=
        ((identDistrib_pairLaw_fst ⟨1, one_mem_symmetricGroup n⟩).comp
          (measurable_of_countable (fun w : FinitaryPerm ℕ+ =>
            (w.nonRecordIndicator i : ℝ)))).integral_eq
      _ = _ := integral_uniform_nonRecord n i hi
  · calc
      _ = ∫ w, (w.nonRecordIndicator i : ℝ) ∂unif (symmetricGroup n) :=
        ((identDistrib_pairLaw_snd ⟨1, one_mem_symmetricGroup n⟩).comp
          (measurable_of_countable (fun w : FinitaryPerm ℕ+ =>
            (w.nonRecordIndicator i : ℝ)))).integral_eq
      _ = _ := integral_uniform_nonRecord n i hi

/-- At the final ambient position a uniform record walk has value equal to ambient size. -/
theorem integral_uniform_walk_terminal (n : ℕ) :
    (∫ p, (recordWalk p.1 p.2 n.succPNat : ℝ) ∂pairLaw (symmetricGroup n)) = n := by
  calc
    _ = ∫ _p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+, (n : ℝ)
        ∂pairLaw (symmetricGroup n) := by
      apply integral_uniform_finset_congr
      intro p hp
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
      rw [recordWalk, ((mem_symmetricGroup n p.1).mp hu).nonRecordsFrom_eq_zero
        n.succPNat (by change n < n + 1; omega),
        ((mem_symmetricGroup n p.2).mp hv).nonRecordsFrom_eq_zero
          n.succPNat (by change n < n + 1; omega)]
      simp only [Nat.cast_zero, zero_add, Int.cast_sub, Int.cast_natCast, Int.cast_one]
      change ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ)
      push_cast
      ring
    _ = _ := by simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- Uniform walk means satisfy the reciprocal-complement backward recurrence. -/
theorem integral_uniform_walk_recurrence (n : ℕ) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    (∫ p, (recordWalk p.1 p.2 i : ℝ) ∂pairLaw (symmetricGroup n)) =
      (∫ p, (recordWalk p.1 p.2 (i + 1) : ℝ) ∂pairLaw (symmetricGroup n)) - 1 +
        2 * ((((i : ℕ) : ℝ) - 1) / (i : ℕ)) := by
  have he : (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
      (recordWalk p.1 p.2 i : ℝ)) =
      (fun p => ((recordWalk p.1 p.2 (i + 1) : ℝ) - 1) +
        (p.1.nonRecordIndicator i : ℝ) + (p.2.nonRecordIndicator i : ℝ)) := by
    funext p
    have hs := recordWalkStep_eq p.1 p.2 i
    unfold recordWalkStep at hs
    have hc := congrArg (fun z : ℤ => (z : ℝ)) hs
    push_cast at hc
    linarith
  rw [he, integral_pair_add, integral_pair_add, integral_pair_sub]
  obtain ⟨hu, hv⟩ := integral_uniform_pair_nonRecord n i hi
  rw [hu, hv]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

private theorem uniform_walk_mean_nat (n k : ℕ) (hk : k ≤ n) :
    (∫ p, (recordWalk p.1 p.2 k.succPNat : ℝ) ∂pairLaw (symmetricGroup n)) =
      2 * n - k - 2 * (harmonic n : ℝ) + 2 * (harmonic k : ℝ) := by
  induction hk using Nat.decreasingInduction with
  | self => rw [integral_uniform_walk_terminal]; ring
  | of_succ k hk ih =>
    have hi : (k + 1).succPNat = k.succPNat + 1 := by apply PNat.eq; rfl
    rw [integral_uniform_walk_recurrence n k.succPNat (by change k + 1 ≤ n; omega),
      ← hi, ih]
    have hp : (k.succPNat : ℕ) = k + 1 := rfl
    rw [hp, harmonic_succ]
    push_cast
    have hn : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- The expected uniform walk value is its exact harmonic expression. -/
theorem integral_uniform_walk (n : ℕ) (i : ℕ+) (hi : (i : ℕ) ≤ n + 1) :
    (∫ p, (recordWalk p.1 p.2 i : ℝ) ∂pairLaw (symmetricGroup n)) =
      2 * n - (i : ℕ) + 1 - 2 * (harmonic n : ℝ) +
        2 * (harmonic ((i : ℕ) - 1) : ℝ) := by
  have hp := PNat.pos i
  have he : ((i : ℕ) - 1).succPNat = i := by
    apply PNat.eq
    change (i : ℕ) - 1 + 1 = (i : ℕ)
    omega
  have hh := uniform_walk_mean_nat n ((i : ℕ) - 1) (by omega)
  rw [he] at hh
  have hc : (((i : ℕ) - 1 : ℕ) : ℝ) = ((i : ℕ) : ℝ) - 1 := by
    have he := congrArg (fun a : ℕ => (a : ℝ))
      (Nat.sub_add_cancel (by omega : 1 ≤ (i : ℕ)))
    push_cast at he
    linarith
  rw [hh, hc]
  ring

end RecordStability
