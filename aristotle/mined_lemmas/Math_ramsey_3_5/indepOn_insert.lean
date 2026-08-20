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

lemma indepOn_insert {v : V} (hv : v ∈ s) {B : Finset V} (hB : B ⊆ nonnbrs G s v)
    (hind : G.IsIndepSet (B : Set V)) : IndepOn G s (B.card + 1) := by
  have hvB : v ∉ B := by
    intro h
    have := mem_nonnbrs.mp (hB h)
    exact this.1.2 rfl
  refine ⟨insert v B, ?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hv
    · exact nonnbrs_subset (hB hw)
  · rw [Finset.card_insert_of_notMem hvB]
  · intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact (mem_nonnbrs.mp (hB (by exact_mod_cast hb))).2
    · rcases hb with rfl | hb
      · exact fun h => (mem_nonnbrs.mp (hB (by exact_mod_cast ha))).2 h.symm
      · exact hind ha hb hab

end General

/-! ## Handshake parity -/

section Parity

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The sum of the degrees inside a finite vertex set is even. -/
