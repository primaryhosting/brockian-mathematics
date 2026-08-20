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

lemma iterate_ne_zero (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
    (hcomm : ∀ x : E, a (ad x) - ad (a x) = x)
    {psi0 : E} (hpsi0 : psi0 ≠ 0) (ha0 : a psi0 = 0) (n : ℕ) :
    ad^[n] psi0 ≠ 0 := by
  intro h
  have h0 : ⟪psi0, psi0⟫_ℂ ≠ 0 := by
    simpa [inner_self_eq_zero] using hpsi0
  have := inner_iterate hadj hcomm ha0 n
  rw [h] at this
  simp only [inner_zero_left] at this
  have hfac : (n ! : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  exact h0 (by
    rcases mul_eq_zero.mp this.symm with h1 | h1
    · exact absurd h1 hfac
    · exact h1)

/-- An eigenvalue of the number operator `a†a` is a nonnegative real. -/
