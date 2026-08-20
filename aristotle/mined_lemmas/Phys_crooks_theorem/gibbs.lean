import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Statement: Crooks fluctuation theorem: P_F(W)/P_R(−W) = e^{β(W−ΔF)}.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Real
open scoped Classical

namespace Phys

variable {S : Type*} [Fintype S] [Nonempty S] {N : ℕ}

/-- `pt x k` is the state of the trajectory `x` (of length `N + 1`) at time `k`. -/

noncomputable def gibbs (k : ℕ) (s : S) : ℝ := Real.exp (-P.beta * P.E k s) / P.Z k

/-- Free energy difference between the final and the initial equilibrium states. -/
