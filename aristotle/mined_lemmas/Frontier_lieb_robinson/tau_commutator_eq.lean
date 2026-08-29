import Mathlib
/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

section Basic

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The inner derivation (adjoint action) `ad H x = H * x - x * H`. -/

lemma tau_commutator_eq [CompleteSpace A] (H : A) (t : ℝ) (a b : A) :
    tau H t a * b - b * tau H t a
      = ∑' n : ℕ, (t ^ n / (n ! : ℝ)) • ((ad H)^[n] a * b - b * (ad H)^[n] a) := by
  have hsum := summable_tau_series H t a
  rw [tau, ← hsum.tsum_mul_right b, ← hsum.tsum_mul_left b,
    ← (hsum.mul_right b).tsum_sub (hsum.mul_left b)]
  refine tsum_congr (fun n => ?_)
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]

end Basic

/-- Tail bound for the exponential series: `∑_{n ≥ d} xⁿ/n ! ≤ (x^d/d !) e^x`. -/
