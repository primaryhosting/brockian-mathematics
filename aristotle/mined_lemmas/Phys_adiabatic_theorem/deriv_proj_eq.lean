/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

namespace Phys

/-! ## The pure ring algebra behind Kato's construction -/

/-- The algebraic heart of the adiabatic theorem.  In a ring, let `p` be an idempotent,
`k` an element annihilating `p` on both sides (think of `k = H - E` with `p` the spectral
projection of the eigenvalue `E`), `d` the derivative of `p` (so that `d = d*p + p*d`), and `b`
a two-sided inverse of `k + p`.  Then the explicitly constructed element
`b*(1-p)*d*p - p*d*(1-p)*b` has commutator with `k` equal to `d`. -/

lemma deriv_proj_eq (hP_idem : ∀ s, P s * P s = P s) (hP : ContDiff ℝ 1 P) (s : ℝ) :
    deriv P s = deriv P s * P s + P s * deriv P s := by
  have hdP : HasDerivAt P (deriv P s) s := (hP.differentiable (by norm_num) s).hasDerivAt
  have h2 : HasDerivAt (fun t => P t * P t) (deriv P s * P s + P s * deriv P s) s := hdP.mul hdP
  have h3 : (fun t => P t * P t) = P := funext hP_idem
  rw [h3] at h2
  exact hdP.unique h2

/-- Kato's observable solves the commutator equation `[H, X] = -i P'`. -/
