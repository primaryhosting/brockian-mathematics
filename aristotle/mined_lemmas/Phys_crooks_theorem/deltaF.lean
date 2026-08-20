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

noncomputable def deltaF : ℝ := -(1 / P.beta) * Real.log (P.Z N / P.Z 0)

/-- Work performed on the system along a forward trajectory: at each step the Hamiltonian is
switched from `E k` to `E (k+1)` while the system sits in state `x k`. -/
