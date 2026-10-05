/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring; the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The finite square-lattice Ising model on an `L × L` torus -/

/-- The cyclic shift `i ↦ i + 1` on `Fin L` (periodic boundary conditions). -/

lemma energy_one (σ : Config 1) : energy 1 σ = -2 := by
  obtain ⟨b, hb⟩ : ∃ b : Bool, ∀ x : Fin 1 × Fin 1, σ x = b :=
    ⟨σ (0, 0), fun x => by rw [Subsingleton.elim x ((0 : Fin 1), (0 : Fin 1))]⟩
  rw [energy]
  simp only [hb]
  cases b <;> norm_num [spin, Finset.card_univ]

/-- Exact partition function of the `1 × 1` torus. -/
