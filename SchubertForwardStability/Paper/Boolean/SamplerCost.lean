import SchubertForwardStability.Permutations.Random.Tags.SamplerLaw

/-! # A linear-time uniform sampler for Boolean permutations

Remark 5.22: the block-tag encoding gives an exact uniform sampler for `B_n` that uses `O(n)`
operations. The sampler builds the table of completion counts `U_k(0), U_k(1)` by the recurrence of
Lemma 5.20, draws the block tags from left to right with probabilities proportional to the counts,
decodes the tags into a reduced word as in Lemma 5.4, and multiplies the word out.

## Cost model

A program is a probability distribution on pairs of a result and a number of steps (`Costed`).
Each of the following costs one step, whatever the size of the numbers involved: an arithmetic
operation, a read or write of a memory cell, adding a letter at either end of a word, a swap of two
adjacent entries of a one-line notation, and a random choice among at most three outcomes with
given integer weights.

## Main results

* `booleanSampler_law`: the sampler's output is uniform on `B_{m+1}`.
* `booleanSampler_steps_le`: every run uses at most `16 (m + 1)` steps.
* `boolean_sampler_linear`: Remark 5.22, the two together for `B_n`.

## References

A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
products*, arXiv:2604.02964 (2026), Remark 5.22.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory
open scoped Classical ENNReal

/-- A randomized program with a step counter: a probability distribution on the pairs of a
result and the number of steps used. -/
abbrev Costed (α : Type) := PMF (α × ℕ)

namespace Costed

variable {α β : Type}

/-- Return a value without any step. -/
noncomputable def ret (a : α) : Costed α := PMF.pure (a, 0)

/-- Run a program and then a program depending on its result, adding their steps. -/
noncomputable def chain (p : Costed α) (f : α → Costed β) : Costed β :=
  PMF.bind p fun x => PMF.map (fun y => (y.1, x.2 + y.2)) (f x.1)

/-- `k` deterministic steps. -/
noncomputable def tick (k : ℕ) : Costed Unit := PMF.pure ((), k)

/-- One random choice with law `q`, as a single step. -/
noncomputable def draw (q : PMF α) : Costed α := PMF.map (fun a => (a, 1)) q

/-- Two deterministic programs with equal results and equal steps agree. -/
theorem pure_congr {a b : α} {c d : ℕ} (hab : a = b) (hcd : c = d) :
    (PMF.pure (a, c) : Costed α) = PMF.pure (b, d) := by
  rw [hab, hcd]

/-- Sequencing after a deterministic program with a known result and number of steps. -/
theorem chain_pure (a : α) (c : ℕ) (f : α → Costed β) :
    chain (PMF.pure (a, c)) f = PMF.map (fun y => (y.1, c + y.2)) (f a) := by
  simp only [chain, PMF.pure_bind]

/-- The law of the result of a sequenced program. -/
theorem map_fst_chain (p : Costed α) (f : α → Costed β) :
    PMF.map Prod.fst (chain p f) =
      PMF.bind (PMF.map Prod.fst p) fun a => PMF.map Prod.fst (f a) := by
  rw [chain, PMF.map_bind, PMF.bind_map]
  refine congrArg (PMF.bind p) (funext fun x => ?_)
  show PMF.map Prod.fst (PMF.map (fun y => (y.1, x.2 + y.2)) (f x.1)) =
    PMF.map Prod.fst (f x.1)
  exact (PMF.map_comp _ _ _).trans rfl

/-- The result of a program that returns a value. -/
theorem map_fst_ret (a : α) : PMF.map Prod.fst (ret a) = PMF.pure a := by
  simp only [ret, PMF.pure_map]

/-- The result of deterministic steps. -/
theorem map_fst_tick (k : ℕ) : PMF.map Prod.fst (tick k) = PMF.pure () := by
  simp only [tick, PMF.pure_map]

/-- The result of a random choice has the law of the choice. -/
theorem map_fst_draw (q : PMF α) : PMF.map Prod.fst (draw q) = q := by
  rw [draw, PMF.map_comp]
  exact PMF.map_id q

/-- Every run of a deterministic program has its known result. -/
theorem fst_of_eq_pure {p : Costed α} {a : α} {c : ℕ} (h : p = PMF.pure (a, c)) :
    ∀ x ∈ p.support, x.1 = a := by
  intro x hx
  rw [h, PMF.support_pure, Set.mem_singleton_iff] at hx
  rw [hx]

/-- Every run of a deterministic program uses its known number of steps. -/
theorem steps_of_eq_pure {p : Costed α} {a : α} {c : ℕ} (h : p = PMF.pure (a, c)) :
    ∀ x ∈ p.support, x.2 ≤ c := by
  intro x hx
  rw [h, PMF.support_pure, Set.mem_singleton_iff] at hx
  subst hx
  exact le_rfl

/-- Returning a value uses no step. -/
theorem steps_ret (a : α) : ∀ x ∈ (ret a).support, x.2 ≤ 0 :=
  steps_of_eq_pure rfl

/-- `tick k` uses `k` steps. -/
theorem steps_tick (k : ℕ) : ∀ x ∈ (tick k).support, x.2 ≤ k :=
  steps_of_eq_pure rfl

/-- A random choice uses one step. -/
theorem steps_draw (q : PMF α) : ∀ x ∈ (draw q).support, x.2 ≤ 1 := by
  intro x hx
  rw [draw, PMF.mem_support_map_iff] at hx
  obtain ⟨a, _, rfl⟩ := hx
  exact le_rfl

/-- A step bound can be raised. -/
theorem steps_mono {p : Costed α} {a b : ℕ} (h : ∀ x ∈ p.support, x.2 ≤ a) (hab : a ≤ b) :
    ∀ x ∈ p.support, x.2 ≤ b :=
  fun x hx => (h x hx).trans hab

/-- A bound on the steps of a sequenced program, from a property of the first result and
bounds on the two parts. -/
theorem steps_le_chain {p : Costed α} {f : α → Costed β} {P : α → Prop} {a c : ℕ}
    (hP : ∀ x ∈ p.support, P x.1) (hp : ∀ x ∈ p.support, x.2 ≤ a)
    (hf : ∀ b, P b → ∀ y ∈ (f b).support, y.2 ≤ c) :
    ∀ z ∈ (chain p f).support, z.2 ≤ a + c := by
  intro z hz
  simp only [chain, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  exact Nat.add_le_add (hp x hx) (hf x.1 (hP x hx) y hy)

/-- A bound on the steps of a sequenced program, from bounds on the two parts. -/
theorem steps_le_chain' {p : Costed α} {f : α → Costed β} {a c : ℕ}
    (hp : ∀ x ∈ p.support, x.2 ≤ a) (hf : ∀ b, ∀ y ∈ (f b).support, y.2 ≤ c) :
    ∀ z ∈ (chain p f).support, z.2 ≤ a + c :=
  steps_le_chain (P := fun _ => True) (fun _ _ => trivial) hp fun b _ => hf b

end Costed

open Costed

/-! ### The table of completion counts -/

/-- The completion counts `(U_k(0), U_k(1))`, by the recurrence of Lemma 5.20. -/
def countPair : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 => ((countPair k).1 + (countPair k).2,
      (countPair k).1 + (countPair k).2 + (countPair k).2)

/-- The recurrence gives the completion counts. -/
theorem countPair_eq (k : ℕ) :
    countPair k = (extensionCount k false, extensionCount k true) := by
  induction k with
  | zero => simp [countPair, extensionCount_zero]
  | succ k ih =>
    rw [countPair, ih, extensionCount_false_succ, extensionCount_true_succ]
    exact Prod.ext rfl (by dsimp only; ring)

/-- The table `[U_k, …, U_0]`, newest entry first. -/
def countTable : ℕ → List (ℕ × ℕ)
  | 0 => [countPair 0]
  | k + 1 => countPair (k + 1) :: countTable k

/-- The newest entry of the table. -/
theorem countTable_headD (k : ℕ) : (countTable k).headD (1, 1) = countPair k := by
  cases k <;> rfl

/-- The entry for `U_r` sits at position `k - r` of the table, for `r ≤ k`. -/
theorem countTable_getD {k r : ℕ} (hr : r ≤ k) :
    (countTable k).getD (k - r) (0, 0) = countPair r := by
  induction k with
  | zero =>
    obtain rfl : r = 0 := by omega
    rfl
  | succ k ih =>
    rcases Nat.lt_or_ge r (k + 1) with hlt | hge
    · rw [show k + 1 - r = (k - r) + 1 by omega, countTable, List.getD_cons_succ,
        ih (by omega)]
    · obtain rfl : r = k + 1 := by omega
      rw [Nat.sub_self, countTable, List.getD_cons_zero]

/-- The table is built with two steps for its first entry and six steps (two reads, two
additions and two writes) for each further entry. -/
noncomputable def buildTable : ℕ → Costed (List (ℕ × ℕ))
  | 0 => chain (tick 2) fun _ => ret [(1, 1)]
  | k + 1 => chain (buildTable k) fun T => chain (tick 6) fun _ =>
      ret (let e := T.headD (1, 1); (e.1 + e.2, e.1 + e.2 + e.2) :: T)

/-- Building the table is deterministic, with `6k + 2` steps. -/
theorem buildTable_eq (k : ℕ) : buildTable k = PMF.pure (countTable k, 6 * k + 2) := by
  induction k with
  | zero =>
    simp only [buildTable, tick, ret, chain_pure, PMF.pure_map]
    exact pure_congr rfl (by omega)
  | succ k ih =>
    simp only [buildTable, ih, tick, ret, chain_pure, PMF.pure_map, countTable_headD]
    exact pure_congr rfl (by omega)

/-! ### Sampling the tags -/

/-- The weight of a candidate next tag, given the counts `(U_m(0), U_m(1))`. -/
def tagWeight (e : ℕ × ℕ) (present : Bool) : BlockTag → ℕ
  | .zero => e.1
  | .start => e.2
  | .cont => if present then e.2 else 0

/-- The next tag, drawn with probabilities proportional to its weight. -/
noncomputable def weightedTag (e : ℕ × ℕ) (present : Bool) : PMF BlockTag :=
  if h : 0 < ∑ t : BlockTag, tagWeight e present t then
    PMF.ofFintype (fun t => (tagWeight e present t : ℝ≥0∞) /
      ((∑ t : BlockTag, tagWeight e present t : ℕ) : ℝ≥0∞)) (by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, ← Nat.cast_sum]
        exact ENNReal.mul_inv_cancel (by exact_mod_cast h.ne') (by simp))
  else PMF.pure .zero

/-- With the counts of the recurrence, the weighted draw is the completion-weighted law. -/
theorem weightedTag_countPair (m : ℕ) (present : Bool) :
    weightedTag (countPair m) present = tagChoicePMF m present := by
  have hw : ∀ t, tagWeight (countPair m) present t = tagChoiceCount m present t := by
    intro t
    cases t <;> simp [tagWeight, tagChoiceCount, countPair_eq]
  have hpos : 0 < ∑ t : BlockTag, tagWeight (countPair m) present t := by
    simp only [hw]
    exact tagChoiceTotal_pos m present
  unfold weightedTag
  split_ifs
  ext t
  simp only [PMF.ofFintype_apply, tagChoicePMF, hw, tagChoiceTotal]

/-- Sample the remaining `m` tags with the table `T` of `U_M, …, U_0`. Each tag uses six steps:
the table position, two table reads, the weighted draw, the presence bit and the write of the
tag. -/
noncomputable def sampleTags (T : List (ℕ × ℕ)) (M : ℕ) : ℕ → Bool → Costed (List BlockTag)
  | 0, _ => ret []
  | m + 1, present =>
    chain (tick 3) fun _ =>
    chain (draw (weightedTag (T.getD (M - m) (0, 0)) present)) fun t =>
    chain (tick 2) fun _ =>
    chain (sampleTags T M m (decide (t ≠ .zero))) fun rest => ret (t :: rest)

/-- The sampled tags have the law of the completion-weighted sampler. -/
theorem map_fst_sampleTags {M m : ℕ} (hm : m ≤ M + 1) (present : Bool) :
    PMF.map Prod.fst (sampleTags (countTable M) M m present) = tagSuffixSampler m present := by
  induction m generalizing present with
  | zero => simp only [sampleTags, map_fst_ret, tagSuffixSampler]
  | succ m ih =>
    rw [sampleTags, tagSuffixSampler, countTable_getD (k := M) (r := m) (by omega),
      weightedTag_countPair]
    simp only [map_fst_chain, map_fst_tick, map_fst_draw, map_fst_ret, PMF.pure_bind,
      ih (by omega)]
    rfl

/-- Sampling `m` tags takes six steps per tag. -/
theorem sampleTags_steps (T : List (ℕ × ℕ)) (M m : ℕ) (present : Bool) :
    ∀ x ∈ (sampleTags T M m present).support, x.2 ≤ 6 * m := by
  induction m generalizing present with
  | zero => exact steps_ret _
  | succ m ih =>
    rw [sampleTags]
    exact steps_mono (steps_le_chain' (steps_tick 3) fun _ =>
      steps_le_chain' (steps_draw _) fun _ =>
      steps_le_chain' (steps_tick 2) fun _ =>
      steps_le_chain' (ih _) fun _ => steps_ret _) (by omega)

/-! ### Decoding and multiplying out -/

/-- Decode a tag vector into a word, one step per tag (a letter added at the end or the
beginning of the word, or none), following `tagRepresentative`. -/
noncomputable def decodeTags : {m : ℕ} → (Fin m → BlockTag) → Costed (List ℕ+)
  | 0, _ => ret []
  | m + 1, T => chain (decodeTags fun i : Fin m => T i.castSucc) fun word =>
      chain (tick 1) fun _ => ret (match T (Fin.last m) with
        | .zero => word
        | .start => word ++ [m.succPNat]
        | .cont => m.succPNat :: word)

/-- Decoding is deterministic, gives `tagRepresentative`, and takes one step per tag. -/
theorem decodeTags_eq {m : ℕ} (T : Fin m → BlockTag) :
    decodeTags T = PMF.pure (tagRepresentative T, m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [decodeTags, ih, tick, ret, chain_pure, PMF.pure_map]
    refine pure_congr ?_ (by omega)
    simp only [tagRepresentative]
    cases T (Fin.last m) <;> rfl

/-- A decoded word has at most one letter per tag. -/
theorem length_tagRepresentative_le {m : ℕ} (T : Fin m → BlockTag) :
    (tagRepresentative T).length ≤ m := by
  induction m with
  | zero => simp [tagRepresentative]
  | succ m ih =>
    have h := ih fun i : Fin m => T i.castSucc
    simp only [tagRepresentative]
    split <;> (try simp only [List.length_append, List.length_cons, List.length_nil]) <;> omega

/-- Multiply out a word from the right, one step per letter (a swap of two adjacent entries). -/
noncomputable def multiplyWord : List ℕ+ → FinitaryPerm ℕ+ → Costed (FinitaryPerm ℕ+)
  | [], w => ret w
  | k :: rest, w => chain (tick 1) fun _ => multiplyWord rest (w * simpleTransposition k)

/-- Multiplying out is deterministic and takes one step per letter. -/
theorem multiplyWord_eq (word : List ℕ+) (w : FinitaryPerm ℕ+) :
    multiplyWord word w = PMF.pure (w * wordProduct word, word.length) := by
  induction word generalizing w with
  | nil => simp [multiplyWord, ret, wordProduct]
  | cons k rest ih =>
    simp only [multiplyWord, tick, chain_pure, ih, PMF.pure_map]
    refine pure_congr ?_ ?_
    · rw [wordProduct_cons, mul_assoc]
    · simp only [List.length_cons]
      omega

/-! ### The sampler -/

/-- The sampler of Remark 5.22 for `B_{m+1}`: build the table of completion counts, sample the
`m` tags, read them into a vector, decode them into a reduced word, write the identity in one-line
notation, and multiply the word out. -/
noncomputable def booleanSampler (m : ℕ) : Costed (FinitaryPerm ℕ+) :=
  chain (buildTable m) fun T =>
  chain (sampleTags T m m false) fun L =>
  chain (tick m) fun _ =>
  chain (decodeTags (tagListVector m L)) fun word =>
  chain (tick (m + 1)) fun _ =>
  multiplyWord word 1

/-- The output law of the sampler: the decoded completion-weighted sampler. -/
theorem map_fst_booleanSampler (m : ℕ) :
    PMF.map Prod.fst (booleanSampler m) = PMF.map
      (fun L => wordProduct (tagRepresentative (tagListVector m L))) (tagSuffixSampler m false) := by
  simp only [booleanSampler, map_fst_chain, buildTable_eq, decodeTags_eq, multiplyWord_eq,
    map_fst_sampleTags (M := m) (m := m) (by omega), map_fst_tick, PMF.pure_map, PMF.pure_bind,
    one_mul]
  rfl

/-- The sampler's output is uniform on the Boolean permutations of size `m + 1`. -/
theorem booleanSampler_law (m : ℕ) :
    (PMF.map Prod.fst (booleanSampler m)).toMeasure = unif (boolean (m + 1)) := by
  rw [map_fst_booleanSampler, ← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  exact map_tagSuffixSampler_uniform m

/-- Every run of the sampler for `B_{m+1}` uses at most `16 (m + 1)` steps. -/
theorem booleanSampler_steps_le (m : ℕ) :
    ∀ x ∈ (booleanSampler m).support, x.2 ≤ 16 * (m + 1) := by
  unfold booleanSampler
  exact steps_mono (steps_le_chain' (steps_of_eq_pure (buildTable_eq m)) fun T =>
    steps_le_chain' (sampleTags_steps T m m false) fun L =>
    steps_le_chain' (steps_tick m) fun _ =>
    steps_le_chain (P := fun word => word.length ≤ m)
      (fun x hx => by
        rw [fst_of_eq_pure (decodeTags_eq _) x hx]
        exact length_tagRepresentative_le _)
      (steps_of_eq_pure (decodeTags_eq _)) fun word hword =>
    steps_le_chain' (steps_tick (m + 1)) fun _ =>
    steps_mono (steps_of_eq_pure (multiplyWord_eq word 1)) hword) (by omega)

/-- Remark 5.22: for `n ≥ 1`, the sampler produces a uniform Boolean permutation of size `n`,
and every run uses at most `16 n` steps. -/
theorem boolean_sampler_linear {n : ℕ} (hn : 1 ≤ n) :
    (PMF.map Prod.fst (booleanSampler (n - 1))).toMeasure = unif (boolean n) ∧
      ∀ x ∈ (booleanSampler (n - 1)).support, x.2 ≤ 16 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact ⟨booleanSampler_law m, booleanSampler_steps_le m⟩

end RecordStability
