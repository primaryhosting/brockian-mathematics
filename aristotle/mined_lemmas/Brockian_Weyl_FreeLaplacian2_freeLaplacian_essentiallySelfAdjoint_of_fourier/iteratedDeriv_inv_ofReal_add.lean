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

import Mathlib

/-!
# A basic criterion for essential self-adjointness

Let `T` be a densely defined symmetric operator on a complex Hilbert space `H`.
If the ranges of `T + i` and `T - i` are both dense, then the adjoint `T†` is
self-adjoint, i.e. `T` is essentially self-adjoint.

Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open LinearPMap MeasureTheory Filter Topology

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The range of `T + z` for a partially defined operator `T` and a scalar `z`. -/

theorem iteratedDeriv_inv_ofReal_add {z : ℂ} (hz : ∀ t : ℝ, ((t : ℂ) + z) ≠ 0) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => ((t : ℂ) + z)⁻¹)
      = fun t : ℝ => (-1) ^ n * (n ! : ℂ) / (((t : ℂ) + z) ^ (n + 1)) := by
  induction n with
  | zero => ext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    ext t
    have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ) + z)) 1 t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const z
    have h2 : HasDerivAt (fun t : ℝ => ((t : ℂ) + z) ^ (n + 1))
        (((n : ℂ) + 1) * ((t : ℂ) + z) ^ n * 1) t := by
      simpa using h1.pow (n + 1)
    have hne : ((t : ℂ) + z) ^ (n + 1) ≠ 0 := pow_ne_zero _ (hz t)
    have h3 : HasDerivAt (fun t : ℝ => ((-1 : ℂ) ^ n * (n ! : ℂ)) / (((t : ℂ) + z) ^ (n + 1)))
        ((0 * ((t : ℂ) + z) ^ (n + 1) -
            ((-1 : ℂ) ^ n * (n ! : ℂ)) * (((n : ℂ) + 1) * ((t : ℂ) + z) ^ n * 1))
          / (((t : ℂ) + z) ^ (n + 1)) ^ 2) t :=
      (hasDerivAt_const t ((-1 : ℂ) ^ n * (n ! : ℂ))).div h2 hne
    rw [h3.deriv]
    have hne0 := hz t
    field_simp
    push_cast [Nat.factorial_succ]
    ring

/-- For non-real `z`, the function `t ↦ (t + z)⁻¹` has temperate growth on `ℝ`. -/
