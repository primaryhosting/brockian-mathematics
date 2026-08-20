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

lemma G13_indep_free : ∀ B : Finset (Fin 13), ¬ G13.IsNIndepSet 5 B := by
  intro B hB
  obtain ⟨hind, hcard⟩ := hB
  obtain ⟨a, b, c, d, e, hab, hbc, hcd, hde, ha, hb, hc, hd, he⟩ := exists_sorted_five hcard
  have key : ∀ x y : Fin 13, x ∈ B → y ∈ B → x < y → ¬ adj13 x y := by
    intro x y hx hy hxy hadj
    exact hind (by exact_mod_cast hx) (by exact_mod_cast hy) (ne_of_lt hxy) hadj
  rcases adj13_no_indep5 a b c d e hab hbc hcd hde with
    h | h | h | h | h | h | h | h | h | h
  · exact key a b ha hb hab h
  · exact key a c ha hc (hab.trans hbc) h
  · exact key a d ha hd (hab.trans (hbc.trans hcd)) h
  · exact key a e ha he (hab.trans (hbc.trans (hcd.trans hde))) h
  · exact key b c hb hc hbc h
  · exact key b d hb hd (hbc.trans hcd) h
  · exact key b e hb he (hbc.trans (hcd.trans hde)) h
  · exact key c d hc hd hcd h
  · exact key c e hc he (hcd.trans hde) h
  · exact key d e hd he hde h

