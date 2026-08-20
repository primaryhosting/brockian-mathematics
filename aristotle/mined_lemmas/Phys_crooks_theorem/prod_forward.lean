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

lemma prod_forward (x : Fin (N + 1) → S) :
    ∏ k ∈ range N, P.K k (pt x k) (pt x (k + 1))
      = Real.exp (P.beta * ∑ k ∈ range N,
          (P.E (k + 1) (pt x k) - P.E (k + 1) (pt x (k + 1))))
        * ∏ k ∈ range N, P.K k (pt x (k + 1)) (pt x k) := by
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => P.kernel_ratio k _ _

omit [Nonempty S] in
