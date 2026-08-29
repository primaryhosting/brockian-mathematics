/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

/-- The state space of the quantum harmonic oscillator, in the occupation-number
(Fock) representation: a state is described by its sequence of coefficients in the
number basis. -/
abbrev Fock : Type := ℕ → ℂ

/-- The `n`-th number-basis state `|n⟩`. -/

lemma commutator_annihilation_creation :
    annihilation ∘ₗ creation - creation ∘ₗ annihilation = LinearMap.id := by
  ext v n
  have hac : annihilation (creation v) n = ((n : ℂ) + 1) * v n := by
    rw [annihilation_apply, creation_apply]
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [← mul_assoc, sqrt_mul_self_cast _ (by positivity)]
    push_cast
    ring
  have hca : creation (annihilation v) n = (n : ℂ) * v n := numberOp_apply v n
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, Pi.sub_apply]
  rw [hac, hca]
  ring

/-- Action of the lowering operator on a number state: `a |n+1⟩ = √(n+1) |n⟩`. -/
