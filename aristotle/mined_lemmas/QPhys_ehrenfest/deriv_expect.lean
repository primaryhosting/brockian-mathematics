/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Complex Matrix

namespace QPhys

variable {n : ℕ}

/-- The expectation value `⟨v, M v⟩` of the (matrix) observable `M` in the state `v`. -/

theorem deriv_expect (hbar : ℝ) (psi : ℝ → (Fin n → ℂ))
    (H : Matrix (Fin n) (Fin n) ℂ) (A dA : ℝ → Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hH : H.IsHermitian)
    (hsch : ∀ i, HasDerivAt (fun s => psi s i) (-(I / hbar) * (H *ᵥ psi t) i) t)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (dA t i j) t) :
    deriv (fun s => expect (A s) (psi s)) t
      = (I / hbar) * expect (H * A t - A t * H) (psi t) + expect (dA t) (psi t) :=
  (ehrenfest hbar psi H A dA t hH hsch hA).deriv

end QPhys

import Mathlib

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

