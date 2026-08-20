import Mathlib

/-!
# Upper bound for the Ramsey number R(4,4)

This file develops, from scratch, the classical inductive bounds on two-colour Ramsey
numbers, culminating in `Math.ramsey_upper_4_4`: every graph on a vertex set of size at
least `18` contains a `4`-clique or an independent set of size `4`.
-/

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

open scoped Classical in
/-- The neighbours of `v` inside `s` (excluding `v` itself). -/

lemma redN_insert_of_not_adj (G : SimpleGraph V) {a v : V} {s : Finset V}
    (hadj : ¬ G.Adj v a) : redN G (insert a s) v = redN G s v := by
  ext w
  simp only [mem_redN, Finset.mem_insert]
  constructor
  · rintro ⟨⟨hw | hw, hwv⟩, hadj'⟩
    · exact absurd (hw ▸ hadj') hadj
    · exact ⟨⟨hw, hwv⟩, hadj'⟩
  · rintro ⟨⟨hw, hwv⟩, hadj'⟩
    exact ⟨⟨Or.inr hw, hwv⟩, hadj'⟩

/-- Handshake lemma, in the localised form we need. -/
