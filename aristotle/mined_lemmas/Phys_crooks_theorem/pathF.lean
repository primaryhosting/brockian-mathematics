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

noncomputable def pathF (x : Fin (N + 1) → S) : ℝ :=
  P.gibbs 0 (pt x 0) * ∏ k ∈ range N, P.K k (pt x k) (pt x (k + 1))

/-- Probability of a trajectory of the reverse process: it starts from the equilibrium state of
`E N` and uses the kernels in reversed order `K (N-1), K (N-2), …`. -/
