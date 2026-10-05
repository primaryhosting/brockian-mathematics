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

def Wrev (E : ℕ → X → ℝ) (N : ℕ) (δ : Fin (N + 1) → X) : ℝ :=
  ∑ s ∈ range N, (Erev E N (s + 1) (st δ (s + 1)) - Erev E N s (st δ (s + 1)))

/-- Time reversal of a trajectory. -/
