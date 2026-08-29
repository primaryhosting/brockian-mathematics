/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter MeasureTheory Topology Complex

namespace Phys

/-- `‖z‖ ^ 2` in terms of the real and imaginary parts of `z`. -/

private lemma hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).im) f'.im x :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h

/--
**Quantum virial theorem** (one dimension, units `ħ = 2m = 1`).

Let `ψ` be a stationary state of energy `E` for the Hamiltonian `-d²/dx² + V`, i.e.
`-ψ'' + V ψ = E ψ`, where `dψ`, `ddψ` are the first and second derivatives of `ψ` and `dV` is
the derivative of `V`.  Assume the state is *bound*: the kinetic density `‖ψ'‖²`, the potential
density `(V - E)‖ψ‖²` and the virial density `x V'(x) ‖ψ‖²` are integrable, and the boundary
terms `‖ψ‖ ‖ψ'‖` and `x (‖ψ'‖² - (V - E)‖ψ‖²)` vanish at `±∞`.

Then twice the expected kinetic energy equals the expectation of the virial `x ∂ₓV`:
`2 ⟨T⟩ = ⟨x · ∇V⟩`.
-/
