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

lemma RamseyArrow.mono {n m p q : ℕ} (hnm : n ≤ m) (h : RamseyArrow n p q) :
    RamseyArrow m p q := by
  intro G
  let f : Fin n ↪ Fin m := ⟨Fin.castLE hnm, Fin.castLE_injective hnm⟩
  rcases h (G.comap f) with ⟨A, hA⟩ | ⟨B, hB⟩
  · refine Or.inl ⟨A.map f, ⟨?_, ?_⟩⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hA.1 ha hb (fun h => hxy (by rw [h]))
    · rw [Finset.card_map, hA.2]
  · refine Or.inr ⟨B.map f, ⟨?_, ?_⟩⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hB.1 ha hb (fun h => hxy (by rw [h]))
    · rw [Finset.card_map, hB.2]

/-! ## The 13-vertex extremal graph -/

/-- Adjacency of the circulant graph `C₁₃(1,5)`. -/
