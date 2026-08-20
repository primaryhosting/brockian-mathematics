/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset SimpleGraph

/-! ### Generic clique helpers -/

section Helpers
variable {V : Type*} {G : SimpleGraph V}

/-- A set with no internal `G`-edges is a clique of the complement. -/

private lemma card_nbrs_add_card_nonnbrs (v : V) :
    (nbrs G v).card + (nonnbrs G v).card + 1 = Fintype.card V := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v)
    (p := fun w => G.Adj v w)
  have h2 : (Finset.univ.erase v).card = Fintype.card V - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  have h3 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  simp only [nbrs, nonnbrs]
  omega

