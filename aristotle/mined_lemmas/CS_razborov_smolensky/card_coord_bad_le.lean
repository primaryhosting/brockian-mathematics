import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem card_coord_bad_le {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
    [Nonempty β] (i : ι) (Q : β → Prop) (t : ℕ)
    (hQ : (univ.filter Q).card * 2 ^ t ≤ Fintype.card β)
    (Bad : Finset (ι → β)) (hsub : Bad ⊆ univ.filter (fun ρ => Q (ρ i))) :
    Bad.card * 2 ^ t ≤ Fintype.card (ι → β) := by
  have hcb : 0 < Fintype.card β := Fintype.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hcb
  calc Bad.card * 2 ^ t * Fintype.card β
      = Bad.card * Fintype.card β * 2 ^ t := by ring
    _ ≤ (univ.filter (fun ρ : ι → β => Q (ρ i))).card * Fintype.card β * 2 ^ t :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Finset.card_le_card hsub))
    _ = ((univ.filter Q).card * 2 ^ t) * Fintype.card (ι → β) := by
        rw [card_filter_coord i Q]; ring
    _ ≤ Fintype.card β * Fintype.card (ι → β) := Nat.mul_le_mul_right _ hQ
    _ = Fintype.card (ι → β) * Fintype.card β := by ring

/-- At most half of the random subsets select a multiple of `q` many witnesses, provided at
least one witness exists.  Proved by the involution flipping the coordinate `up j₀`. -/
