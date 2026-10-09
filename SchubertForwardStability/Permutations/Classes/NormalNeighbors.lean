import SchubertForwardStability.Permutations.Classes.NormalWords
import Mathlib.Data.List.Infix

/-! # Consecutive neighboring generators in normal words

The order of a neighboring pair can be read from its two-letter projection. In a
distinct word without separated inversions, a reversed neighboring pair is contiguous.
-/

namespace FinitaryPerm

/-- A two-letter projection supplies the corresponding ordered occurrence decomposition. -/
theorem neighborProjection_pair_decomp (i j : ℕ+) (word : List ℕ+)
    (h : neighborProjection i j word = [i, j]) :
    ∃ pre mid suf : List ℕ+, word = pre ++ i :: mid ++ j :: suf := by
  induction word with
  | nil => simp [neighborProjection] at h
  | cons k word ih =>
    by_cases hk : k = i ∨ k = j
    · have he : k :: neighborProjection i j word = [i, j] := by
        simpa [neighborProjection, hk] using h
      have hki := (List.cons.inj he).1
      have ht := (List.cons.inj he).2
      subst k
      have hjProj : j ∈ neighborProjection i j word := by rw [ht]; simp
      have hj : j ∈ word := (List.mem_filter.mp hjProj).1
      obtain ⟨mid, suf, hword⟩ := List.mem_iff_append.mp hj
      exact ⟨[], mid, suf, by rw [hword]; rfl⟩
    · have ht : neighborProjection i j word = [i, j] := by
        simpa [neighborProjection, hk] using h
      obtain ⟨pre, mid, suf, he⟩ := ih ht
      exact ⟨k :: pre, mid, suf, by rw [he]; rfl⟩

private theorem no_inversion_append_right (pre word : List ℕ+)
    (h : ¬HasCommutingInversion (pre ++ word)) : ¬HasCommutingInversion word := by
  rintro ⟨p, s, a, b, he, hgap⟩
  exact h ⟨pre ++ p, s, a, b, by rw [he]; simp only [List.append_assoc], hgap⟩

/-- No other letter lies between a reversed neighboring pair in a distinct normal word. -/
theorem normal_neighbors_contiguous (word : List ℕ+) (hN : word.Nodup)
    (hNo : ¬HasCommutingInversion word) (i j : ℕ+) (hji : j + 1 = i)
    (pre mid suf : List ℕ+) (he : word = pre ++ i :: mid ++ j :: suf) : mid = [] := by
  have hFull : word = pre ++ (i :: (mid ++ j :: suf)) := by
    simpa only [List.append_assoc, List.cons_append] using he
  have hN' := hN
  rw [hFull] at hN'
  have hND : (i :: mid ++ j :: suf).Nodup := hN'.of_append_right
  have hNo' : ¬HasCommutingInversion (i :: mid ++ j :: suf) :=
    no_inversion_append_right pre _ (by
      simpa only [he, List.append_assoc, List.cons_append] using hNo)
  cases mid with
  | nil => rfl
  | cons k mid =>
    have hiMem := (List.nodup_cons.mp hND).1
    have hkMem := (List.nodup_cons.mp hND.tail).1
    have hki : k ≠ i := by
      intro h
      exact hiMem (by simp [← h])
    have hkj : k ≠ j := by
      intro h
      exact hkMem (by simp [h])
    have hLow : i ≤ k + 1 := by
      by_contra hn
      exact hNo' ⟨[], mid ++ j :: suf, i, k, rfl, lt_of_not_ge hn⟩
    have hLowN : (i : ℕ) ≤ (k : ℕ) + 1 := hLow
    have hEqN := congrArg PNat.val hji
    change (j : ℕ) + 1 = (i : ℕ) at hEqN
    have hkiN : (k : ℕ) ≠ (i : ℕ) := fun h => hki (PNat.eq h)
    have hkjN : (k : ℕ) ≠ (j : ℕ) := fun h => hkj (PNat.eq h)
    have hGt : j + 1 < k := by change (j : ℕ) + 1 < (k : ℕ); omega
    have hFar : ∀ a ∈ k :: mid, j + 1 ≠ a := by
      intro a ha heq
      apply hiMem
      rw [hji.symm.trans heq]
      exact List.mem_append_left _ ha
    have hTail : ¬HasCommutingInversion (k :: mid ++ j :: suf) :=
      no_inversion_append_right [i] _ hNo'
    exact (hTail (hasInversion_of_high_prefix j k mid suf hFar hGt)).elim

private theorem projection_nil_of_absent (i j : ℕ+) (word : List ℕ+)
    (hi : i ∉ word) (hj : j ∉ word) : neighborProjection i j word = [] := by
  induction word with
  | nil => rfl
  | cons k word ih =>
    have hki : k ≠ i := fun h => hi (by simp [h])
    have hkj : k ≠ j := fun h => hj (by simp [h])
    have hit : i ∉ word := fun h => hi (by simp [h])
    have hjt : j ∉ word := fun h => hj (by simp [h])
    simpa [neighborProjection, hki, hkj] using ih hit hjt

/-- A contiguous pair exhausts its two-letter projection in a distinct word. -/
theorem neighborProjection_of_infix (word : List ℕ+) (hN : word.Nodup) (i j : ℕ+)
    (h : [i, j].IsInfix word) : neighborProjection i j word = [i, j] := by
  obtain ⟨pre, suf, he⟩ := h
  have hND : ((pre ++ [i, j]) ++ suf).Nodup := by
    rw [← he] at hN
    simpa only [List.append_assoc] using hN
  have hLeft : (pre ++ [i, j]).Nodup := hND.of_append_left
  have hiPre : i ∉ pre := fun hm => List.disjoint_left.mp hLeft.disjoint hm (by simp)
  have hjPre : j ∉ pre := fun hm => List.disjoint_left.mp hLeft.disjoint hm (by simp)
  have hiSuf : i ∉ suf := List.disjoint_left.mp hND.disjoint (by simp)
  have hjSuf : j ∉ suf := List.disjoint_left.mp hND.disjoint (by simp)
  have hp := projection_nil_of_absent i j pre hiPre hjPre
  have hs := projection_nil_of_absent i j suf hiSuf hjSuf
  simp only [neighborProjection] at hp hs
  have hf : (fun k : ℕ+ => decide (k = i ∨ k = j)) =
      (fun k : ℕ+ => decide (k = i) || decide (k = j)) := by
    funext k
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp [hi, hj]
  rw [hf] at hp hs
  rw [← he]
  simp [neighborProjection, hp, hs]

/-- A reversed neighboring projection is exactly a contiguous pair in a distinct normal word. -/
theorem normal_neighbors_projection_iff (word : List ℕ+) (hN : word.Nodup)
    (hNo : ¬HasCommutingInversion word) (i j : ℕ+) (hji : j + 1 = i) :
    neighborProjection i j word = [i, j] ↔ [i, j].IsInfix word := by
  constructor
  · intro h
    obtain ⟨pre, mid, suf, he⟩ := neighborProjection_pair_decomp i j word h
    have hm := normal_neighbors_contiguous word hN hNo i j hji pre mid suf he
    subst mid
    exact ⟨pre, suf, by
      simpa only [List.nil_append, List.append_assoc, List.cons_append] using he.symm⟩
  · exact neighborProjection_of_infix word hN i j

end FinitaryPerm
