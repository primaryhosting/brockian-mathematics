import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
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

namespace Phys

/-- Iterating a translation-eigenvalue relation: `ψ (x₀ + n a) = c ^ n * ψ x₀`. -/

theorem exists_const_translate (a : ℝ) (f : ℝ → ℂ) :
    (∃ c : ℂ, (fun x : ℝ => f (x + a)) = fun _ : ℝ => c) ↔ (∃ c : ℂ, f = fun _ : ℝ => c) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, funext fun x => ?_⟩
    have := congrFun hc (x - a)
    simpa using this
  · rintro ⟨c, hc⟩
    exact ⟨c, funext fun x => by rw [hc]⟩

/-- The hypotheses of `bloch_theorem` are not vacuous: they are satisfied by the
constant wavefunction `ψ = 1` for the Hamiltonian `constHamiltonian` with `E = 1`. -/
