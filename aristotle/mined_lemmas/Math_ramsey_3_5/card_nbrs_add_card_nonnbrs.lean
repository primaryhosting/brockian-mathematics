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

lemma card_nbrs_add_card_nonnbrs {v : V} (hv : v ∈ s) :
    (nbrs G s v).card + (nonnbrs G s v).card = s.card - 1 := by
  have h1 : (s.erase v).filter (fun w => G.Adj v w) = nbrs G s v := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase, mem_nbrs]
    constructor
    · rintro ⟨⟨-, hw⟩, ha⟩; exact ⟨hw, ha⟩
    · rintro ⟨hw, ha⟩
      exact ⟨⟨fun h => G.irrefl (h ▸ ha), hw⟩, ha⟩
  have h2 := Finset.card_filter_add_card_filter_not
    (s := s.erase v) (p := fun w => G.Adj v w)
  rw [h1] at h2
  rw [show (nonnbrs G s v) = (s.erase v).filter (fun w => ¬ G.Adj v w) from rfl, h2,
    Finset.card_erase_of_mem hv]

/-- If `s` contains no triangle then the neighbourhood of `v` in `s` is independent. -/
