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

noncomputable def Zpf (β : ℝ) (E : ℕ → X → ℝ) (t : ℕ) : ℝ :=
  ∑ x : X, Real.exp (-β * E t x)

/-- Probability of the forward trajectory `γ`: start in equilibrium w.r.t. `E 0`, then at each
step `t < N` the protocol changes `E t → E (t+1)` at fixed state (this is where work is done)
and afterwards the system relaxes with the transition kernel `p t`. -/
