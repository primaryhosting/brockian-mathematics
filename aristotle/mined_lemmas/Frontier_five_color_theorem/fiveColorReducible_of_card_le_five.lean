import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

variable {V : Type*} [DecidableEq V]

/-- The neighbours of `v` inside the vertex set `s`. -/

theorem fiveColorReducible_of_card_le_five (s : Finset V) (G : SimpleGraph V) (hs : s.card ≤ 5) :
    FiveColorReducible s G := by
  intro t H hred hne
  obtain ⟨v, hv⟩ := hne
  refine ⟨v, hv, Or.inl ?_⟩
  have h1 := Finset.card_le_card (nbrs_subset t H v)
  have h2 : (t.erase v).card = t.card - 1 := Finset.card_erase_of_mem hv
  have h3 : t.card ≤ 5 := le_trans (Finset.card_le_card hred.subset) hs
  have h4 : 1 ≤ t.card := Finset.card_pos.2 ⟨v, hv⟩
  omega

/-- The base case of the five colour theorem: every graph on at most five vertices is
`5`-colourable. -/
