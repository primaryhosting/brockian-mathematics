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

lemma exists_adj_of_isNClique_four {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {t : Finset V} (h : G.IsNClique 4 t) :
    ∃ a b c d : V, G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d := by
  obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, rfl⟩ := Finset.card_eq_four.1 h.2
  exact ⟨x, y, z, w,
    h.1 (by simp) (by simp) hxy, h.1 (by simp) (by simp) hxz, h.1 (by simp) (by simp) hxw,
    h.1 (by simp) (by simp) hyz, h.1 (by simp) (by simp) hyw, h.1 (by simp) (by simp) hzw⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
