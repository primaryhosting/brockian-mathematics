import Mathlib

/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
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

set_option grind.warning false

namespace QPhys

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Hamiltonian `ℏω (a† a + ½)` of a one-dimensional quantum harmonic oscillator,
expressed through the annihilation operator `a` and the creation operator `ad = a†`. -/

lemma inner_iterate (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
    (hcomm : ∀ x : E, a (ad x) - ad (a x) = x)
    {psi0 : E} (ha0 : a psi0 = 0) (n : ℕ) :
    ⟪ad^[n] psi0, ad^[n] psi0⟫_ℂ = (n ! : ℂ) * ⟪psi0, psi0⟫_ℂ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : a (ad (ad^[n] psi0)) = ad (a (ad^[n] psi0)) + ad^[n] psi0 := by
        have := hcomm (ad^[n] psi0)
        linear_combination (norm := module) this
      rw [Function.iterate_succ_apply' (f := ⇑ad)]
      rw [inner_ad_left hadj, hstep, number_iterate hcomm ha0 n]
      rw [inner_add_right, inner_smul_right, ih]
      push_cast [Nat.factorial_succ]
      ring

/-- The excited states are nonzero. -/
