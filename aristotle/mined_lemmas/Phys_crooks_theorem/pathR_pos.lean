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

lemma pathR_pos (y : Fin (N + 1) → S) : 0 < P.pathR y :=
  mul_pos (P.gibbs_pos _ _) (Finset.prod_pos fun _ _ => P.K_pos _ _ _)

omit [Nonempty S] in
