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

lemma kernel_ratio (k : ℕ) (a b : S) :
    P.K k a b = Real.exp (P.beta * (P.E (k + 1) a - P.E (k + 1) b)) * P.K k b a := by
  apply mul_left_cancel₀ (Real.exp_ne_zero (-P.beta * P.E (k + 1) a))
  rw [← mul_assoc, ← Real.exp_add]
  have h : -P.beta * P.E (k + 1) a + P.beta * (P.E (k + 1) a - P.E (k + 1) b)
      = -P.beta * P.E (k + 1) b := by ring
  rw [h, P.detailed_balance k a b]

omit [Nonempty S] in
