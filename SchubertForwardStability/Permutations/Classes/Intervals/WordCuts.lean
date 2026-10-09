import SchubertForwardStability.Permutations.Classes.ReducedWords

/-! # Cuts of adjacent words

## Main definitions

* `wordCuts`: all prefix, letter and suffix decompositions of a positive-index word.

## Main results

The cuts enumerate exactly the displayed letters. Deleting the selected letter
decreases displayed length by one.
-/

namespace FinitaryPerm

/-- The list of prefix, letter and suffix triples obtained by selecting each letter once. -/
def wordCuts : List ℕ+ → List (List ℕ+ × ℕ+ × List ℕ+)
  | [] => []
  | i :: word => ([], i, word) ::
      (wordCuts word).map (fun c => (i :: c.1, c.2.1, c.2.2))

/-- There is one displayed cut for each letter of the word. -/
theorem wordCuts_length (word : List ℕ+) : (wordCuts word).length = word.length := by
  induction word with
  | nil => rfl
  | cons i word ih => simp only [wordCuts, List.length_cons, List.length_map, ih]

private theorem wordCuts_sound {word : List ℕ+} {c : List ℕ+ × ℕ+ × List ℕ+}
    (hc : c ∈ wordCuts word) : c.1 ++ c.2.1 :: c.2.2 = word := by
  induction word generalizing c with
  | nil => exact False.elim (List.not_mem_nil hc)
  | cons i word ih =>
    rcases List.mem_cons.mp hc with he | hm
    · cases he
      rfl
    · obtain ⟨d, hd, he⟩ := List.mem_map.mp hm
      subst c
      change (i :: d.1) ++ d.2.1 :: d.2.2 = i :: word
      rw [List.cons_append, ih hd]

private theorem wordCuts_complete (pre : List ℕ+) (i : ℕ+) (suf : List ℕ+) :
    (pre, i, suf) ∈ wordCuts (pre ++ i :: suf) := by
  induction pre with
  | nil => exact List.mem_cons_self
  | cons j pre ih =>
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨(pre, i, suf), ih, rfl⟩

/-- The enumerated cuts are exactly the decompositions around one letter. -/
theorem mem_wordCuts (word pre : List ℕ+) (i : ℕ+) (suf : List ℕ+) :
    (pre, i, suf) ∈ wordCuts word ↔ pre ++ i :: suf = word := by
  constructor
  · exact wordCuts_sound
  · intro he
    rw [← he]
    exact wordCuts_complete pre i suf

/-- Removing the selected letter decreases the displayed length by exactly one. -/
theorem wordCuts_deleted_length {word pre : List ℕ+} {i : ℕ+} {suf : List ℕ+}
    (hc : (pre, i, suf) ∈ wordCuts word) : (pre ++ suf).length + 1 = word.length := by
  have he := (mem_wordCuts word pre i suf).mp hc
  rw [← he, List.length_append, List.length_append, List.length_cons]
  omega

end FinitaryPerm
