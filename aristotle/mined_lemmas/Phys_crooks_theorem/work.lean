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

def work (x : Fin (N + 1) → S) : ℝ :=
  ∑ k ∈ range N, (P.E (k + 1) (pt x k) - P.E k (pt x k))

/-- Work performed along a trajectory of the reverse process.  In the reverse process the
protocol is run backwards, `E N, E (N-1), …, E 0`, and each Hamiltonian switch happens *after*
the corresponding relaxation step. -/
