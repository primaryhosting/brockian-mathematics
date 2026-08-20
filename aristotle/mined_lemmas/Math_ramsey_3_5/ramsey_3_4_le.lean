import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Cliques and independent sets inside a finite set of vertices -/

section General

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s t : Finset V} {n : ℕ} {v : V}

/-- `CliqueOn G s n` : the vertex set `s` contains a clique of `G` with `n` vertices. -/

lemma ramsey_3_4_le (hs : 9 ≤ s.card) : CliqueOn G s 3 ∨ IndepOn G s 4 := by
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hs
  rcases ramsey_3_4_le_of_card_eq (G := G) (s := t) htcard with h | h
  · exact Or.inl (h.mono hts)
  · exact Or.inr (h.mono hts)

