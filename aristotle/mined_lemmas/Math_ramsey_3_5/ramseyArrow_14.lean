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

lemma ramseyArrow_14 : RamseyArrow 14 3 5 := by
  classical
  intro G
  rcases ramsey_3_5_le (G := G) (s := (Finset.univ : Finset (Fin 14))) (by simp) with h | h
  · obtain ⟨A, -, hcard, hcl⟩ := h
    exact Or.inl ⟨A, hcl, hcard⟩
  · obtain ⟨B, -, hcard, hind⟩ := h
    exact Or.inr ⟨B, hind, hcard⟩

/-- **The Ramsey number `R(3,5)` equals 14.** -/
