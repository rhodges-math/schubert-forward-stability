import SchubertForwardStability.Permutations.Classes.NeighborProjection
import Mathlib.Data.List.Chain

/-! # Uniqueness of separated-inversion-free words

A distinct-generator word with no separated inversion is determined by its
generator support and the order of every pair of neighboring generators.
-/

namespace FinitaryPerm

/-- Bounding each neighboring drop by one excludes every separated inversion. -/
theorem not_hasInversion_of_chain (word : List ℕ+)
    (hc : word.IsChain fun a b => a ≤ b + 1) : ¬HasCommutingInversion word := by
  rintro ⟨pre, suf, i, j, heq, hgap⟩
  rw [heq] at hc
  have hLow := (List.isChain_cons_cons.mp (List.isChain_append.mp hc).2.1).1
  exact (not_lt_of_ge hLow) hgap

private theorem no_inversion_tail (i : ℕ+) (word : List ℕ+)
    (h : ¬HasCommutingInversion (i :: word)) : ¬HasCommutingInversion word := by
  rintro ⟨pre, suf, a, b, heq, hgap⟩
  exact h ⟨i :: pre, suf, a, b, by rw [heq]; rfl, hgap⟩

private theorem inversion_barrier (j i : ℕ+) (pre suf : List ℕ+)
    (hNo : ¬HasCommutingInversion (i :: pre ++ j :: suf))
    (hFar : ∀ k ∈ i :: pre, j + 1 ≠ k) (hGt : j + 1 < i) : False := by
  induction pre generalizing i with
  | nil => exact hNo ⟨[], suf, i, j, rfl, hGt⟩
  | cons k pre ih =>
    have hLow : i ≤ k + 1 := by
      by_contra hn
      exact hNo ⟨[], pre ++ j :: suf, i, k, rfl, lt_of_not_ge hn⟩
    have hNe : (j : ℕ) + 1 ≠ (k : ℕ) :=
      fun h => hFar k (by simp) (PNat.eq h)
    have hLowN : (i : ℕ) ≤ (k : ℕ) + 1 := hLow
    have hGtN : (j : ℕ) + 1 < (i : ℕ) := hGt
    have hNext : j + 1 < k := by change (j : ℕ) + 1 < (k : ℕ); omega
    exact ih k (no_inversion_tail i _ hNo) (fun a ha => hFar a (by simp [ha])) hNext

/-- A high prefix avoiding the immediate successor forces a separated inversion. -/
theorem hasInversion_of_high_prefix (j i : ℕ+) (pre suf : List ℕ+)
    (hFar : ∀ k ∈ i :: pre, j + 1 ≠ k) (hGt : j + 1 < i) :
    HasCommutingInversion (i :: pre ++ j :: suf) := by
  by_contra hNo
  exact inversion_barrier j i pre suf hNo hFar hGt

private theorem no_neighbor_prefix (j : ℕ+) (pre suf v : List ℕ+)
    (hj : j ∉ pre)
    (hp : ∀ a b : ℕ+, a + 1 = b ∨ b + 1 = a →
      neighborProjection a b (pre ++ j :: suf) = neighborProjection a b (j :: v)) :
    ∀ k ∈ pre, ¬(k + 1 = j ∨ j + 1 = k) := by
  intro k hk hNeighbor
  have heq : neighborProjection k j pre ++ j :: neighborProjection k j suf =
      j :: neighborProjection k j v := by
    simpa [neighborProjection] using hp k j hNeighbor
  cases hPre : neighborProjection k j pre with
  | nil =>
    have hkProj : k ∈ neighborProjection k j pre := by simp [neighborProjection, hk]
    rw [hPre] at hkProj
    exact List.not_mem_nil hkProj
  | cons d rest =>
    rw [hPre] at heq
    have hdj : d = j := (List.cons.inj heq).1
    have hd : d ∈ neighborProjection k j pre := by rw [hPre]; simp
    rw [hdj] at hd
    exact hj (List.mem_filter.mp hd).1

private theorem normal_head_le (i j : ℕ+) (u v : List ℕ+)
    (hNu : (i :: u).Nodup) (hNo : ¬HasCommutingInversion (i :: u))
    (hs : (i :: u).toFinset = (j :: v).toFinset)
    (hp : ∀ a b : ℕ+, a + 1 = b ∨ b + 1 = a →
      neighborProjection a b (i :: u) = neighborProjection a b (j :: v)) : i ≤ j := by
  by_contra hn
  have hi : j < i := lt_of_not_ge hn
  have hj : j ∈ i :: u := by
    have hm : j ∈ (j :: v).toFinset := by simp
    rw [← hs] at hm
    simpa using hm
  obtain ⟨pre, suf, hSplit⟩ := List.mem_iff_append.mp hj
  have hND : (pre ++ j :: suf).Nodup := hSplit ▸ hNu
  have hjPre : j ∉ pre := fun hm => List.disjoint_left.mp hND.disjoint hm (by simp)
  have hPrefix : ∀ k ∈ pre, ¬(k + 1 = j ∨ j + 1 = k) :=
    no_neighbor_prefix j pre suf v hjPre (by
      intro a b hab
      rw [← hSplit]
      exact hp a b hab)
  cases pre with
  | nil =>
    have hij : i = j := (List.cons.inj hSplit).1
    exact (ne_of_gt hi) hij
  | cons k pre =>
    have hik : i = k := (List.cons.inj hSplit).1
    have hFar : ∀ a ∈ k :: pre, j + 1 ≠ a :=
      fun a ha he => hPrefix a ha (Or.inr he)
    have hNe : (j : ℕ) + 1 ≠ (i : ℕ) := fun h =>
      hFar k (by simp) (hik ▸ PNat.eq h)
    have hiN : (j : ℕ) < (i : ℕ) := hi
    have hGt : j + 1 < k := by
      rw [← hik]
      change (j : ℕ) + 1 < (i : ℕ)
      omega
    exact inversion_barrier j k pre suf (by rw [← hSplit]; exact hNo) hFar hGt

/-- A normal distinct word is uniquely determined by support and neighboring orders. -/
theorem normalWord_eq_of_projections (u v : List ℕ+) (hNu : u.Nodup) (hNv : v.Nodup)
    (hNoU : ¬HasCommutingInversion u) (hNoV : ¬HasCommutingInversion v)
    (hs : u.toFinset = v.toFinset)
    (hp : ∀ a b : ℕ+, a + 1 = b ∨ b + 1 = a →
      neighborProjection a b u = neighborProjection a b v) : u = v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons j v =>
      have hm : j ∈ (j :: v).toFinset := by simp
      rw [← hs] at hm
      simp at hm
  | cons i u ih =>
    cases v with
    | nil =>
      have hm : i ∈ (i :: u).toFinset := by simp
      rw [hs] at hm
      simp at hm
    | cons j v =>
      have hij : i = j := le_antisymm (normal_head_le i j u v hNu hNoU hs hp)
        (normal_head_le j i v u hNv hNoV hs.symm (fun a b h => (hp a b h).symm))
      subst j
      have hTail : u.toFinset = v.toFinset := by
        have he := congrArg (fun s : Finset ℕ+ => s.erase i) hs
        simpa [(List.nodup_cons.mp hNu).1, (List.nodup_cons.mp hNv).1] using he
      congr 1
      apply ih v hNu.tail hNv.tail (no_inversion_tail i u hNoU)
        (no_inversion_tail i v hNoV) hTail
      intro a b hab
      have he := hp a b hab
      by_cases hi : i = a ∨ i = b <;> simpa [neighborProjection, hi] using he

end FinitaryPerm
