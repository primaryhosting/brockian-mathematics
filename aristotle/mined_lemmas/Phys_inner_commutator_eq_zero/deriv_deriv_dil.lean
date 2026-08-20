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

lemma deriv_deriv_dil {ψ : ℝ → ℂ} (hψ : ContDiff ℝ (3 : ℕ) ψ) (x : ℝ) :
    deriv (deriv (dil ψ)) x =
      (5 / 2 : ℂ) * deriv (deriv ψ) x + x * deriv (deriv (deriv ψ)) x := by
  have hψ2 : ContDiff ℝ (2 : ℕ) ψ := hψ.of_le (by exact_mod_cast (by norm_num : (2:ℕ) ≤ 3))
  have hd1 : ContDiff ℝ (2 : ℕ) (deriv ψ) := by
    have := (contDiff_succ_iff_deriv (n := ((2:ℕ) : WithTop ℕ∞)) (f := ψ)).mp
      (by norm_num; exact hψ)
    simpa using this.2.2
  have h1 : HasDerivAt (deriv ψ) (deriv (deriv ψ) x) x :=
    (ContDiff.differentiable_deriv_two hψ2 x).hasDerivAt
  have h2 : HasDerivAt (deriv (deriv ψ)) (deriv (deriv (deriv ψ)) x) x :=
    (ContDiff.differentiable_deriv_two hd1 x).hasDerivAt
  rw [deriv_dil hψ2]
  have : HasDerivAt (fun y : ℝ => (3 / 2 : ℂ) * deriv ψ y + y * deriv (deriv ψ) y)
      ((5 / 2 : ℂ) * deriv (deriv ψ) x + x * deriv (deriv (deriv ψ)) x) x := by
    have := (h1.const_mul (3 / 2 : ℂ)).add ((hasDerivAt_coe x).mul h2)
    convert this using 1
    ring
  exact this.deriv

