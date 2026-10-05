/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset
open scoped Classical

namespace Phys

variable {X : Type*} [Fintype X]

/-- State visited by a path at (natural-number) time `n`, clamped to the horizon `N`. -/

def Wfwd (E : ℕ → X → ℝ) (N : ℕ) (γ : Fin (N + 1) → X) : ℝ :=
  ∑ t ∈ range N, (E (t + 1) (st γ t) - E t (st γ t))

/-- Energies of the time-reversed protocol. -/
