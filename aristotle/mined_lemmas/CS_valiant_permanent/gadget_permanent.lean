import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

lemma gadget_permanent : (gadget A).permanent = A.permanent := by
  classical
  have hbij : Function.Bijective
      (fun p : (π : Equiv.Perm (Fin n)) × (∀ i, Fin (A i (π i))) =>
        (⟨toPermV A p.1 p.2, toPermV_valid A p.1 p.2⟩ :
          {σ : Equiv.Perm (Vert A) // ∀ v, gadget A v (σ v) = 1})) := by
    constructor
    · intro p q hpq
      exact toPermV_injective A (congrArg Subtype.val hpq)
    · rintro ⟨σ, hσ⟩
      obtain ⟨p, hp⟩ := toPermV_surjective A σ hσ
      exact ⟨p, Subtype.ext hp⟩
  rw [permanent_eq_card_perm (gadget A) (gadget_zeroOne A), ← Nat.card_eq_of_bijective _ hbij,
    Nat.card_eq_fintype_card, card_sigma_eq_permanent]

