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

noncomputable def pathR (y : Fin (N + 1) → S) : ℝ :=
  P.gibbs N (pt y 0) * ∏ k ∈ range N, P.K (N - (k + 1)) (pt y k) (pt y (k + 1))

/-- Forward work distribution `P_F(w)`. -/
