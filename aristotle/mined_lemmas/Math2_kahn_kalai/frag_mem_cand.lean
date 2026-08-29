import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma frag_mem_cand {H : Finset (Finset X)} {W S : Finset X} (hS : S ∈ H) :
    frag H W S ∈ cand H W S := by
  have h := cand_nonempty (H := H) (W := W) hS
  rw [frag, dif_pos h]
  exact (Finset.exists_min_image (cand H W S) Finset.card h).choose_spec.1

