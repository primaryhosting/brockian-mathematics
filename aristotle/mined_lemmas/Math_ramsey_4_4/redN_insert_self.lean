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

lemma redN_insert_self (G : SimpleGraph V) {a : V} {s : Finset V} (ha : a ∉ s) :
    ∀ w, w ∈ redN G (insert a s) a ↔ w ∈ s ∧ G.Adj a w := by
  intro w
  rw [mem_redN]
  constructor
  · rintro ⟨⟨hw, hwa⟩, hadj⟩
    exact ⟨(Finset.mem_insert.1 hw).resolve_left hwa, hadj⟩
  · rintro ⟨hw, hadj⟩
    exact ⟨⟨Finset.mem_insert_of_mem hw, fun h => ha (h ▸ hw)⟩, hadj⟩

