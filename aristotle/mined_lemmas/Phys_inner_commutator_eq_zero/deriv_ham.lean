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

/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the header above is
-- the requested header, reproduced verbatim as a module docstring immediately after the import.)

import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-! ## The abstract (operator) virial theorem -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- In a stationary state, the expectation value of any commutator with the Hamiltonian
vanishes: `⟨ψ, [H, A] ψ⟩ = 0` whenever `H` is symmetric and `H ψ = E₀ ψ` with `E₀` real. -/

lemma deriv_ham {v ψ : ℝ → ℂ} (hv : Differentiable ℝ v) (hψ : ContDiff ℝ (3 : ℕ) ψ) (x : ℝ) :
    deriv (ham v ψ) x =
      -(1 / 2 : ℂ) * deriv (deriv (deriv ψ)) x + (deriv v x * ψ x + v x * deriv ψ x) :=
  (hasDerivAt_ham hv hψ x).deriv

/-- The Schrödinger commutator identity `[H, A] = 2T - W` in one dimension, where
`H = -½ d²/dx² + V` is the Schrödinger operator, `A = x d/dx + ½` generates dilations,
`T = -½ d²/dx²` and `W = x V'(x)`. -/
