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

lemma exists_sorted_five {B : Finset (Fin 13)} (hcard : B.card = 5) :
    ∃ a b c d e : Fin 13, a < b ∧ b < c ∧ c < d ∧ d < e ∧
      a ∈ B ∧ b ∈ B ∧ c ∈ B ∧ d ∈ B ∧ e ∈ B := by
  have hlen : (B.sort (· ≤ ·)).length = 5 := by rw [Finset.length_sort, hcard]
  have hsorted : (B.sort (· ≤ ·)).Pairwise (· < ·) := B.sortedLT_sort.pairwise
  have hmem : ∀ x, x ∈ B.sort (· ≤ ·) → x ∈ B := fun x hx => (Finset.mem_sort _).mp hx
  rcases hs : B.sort (· ≤ ·) with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩⟩ <;>
    rw [hs] at hlen hsorted hmem <;> simp at hlen
  · subst hlen
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false] at hsorted
    refine ⟨a, b, c, d, e, ?_, ?_, ?_, ?_, hmem _ (by simp), hmem _ (by simp), hmem _ (by simp),
      hmem _ (by simp), hmem _ (by simp)⟩ <;> aesop

