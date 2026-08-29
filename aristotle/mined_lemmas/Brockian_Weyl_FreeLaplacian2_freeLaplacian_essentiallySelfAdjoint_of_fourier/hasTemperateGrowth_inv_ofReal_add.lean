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

theorem hasTemperateGrowth_inv_ofReal_add {z : ℂ} (hz : z.im ≠ 0) :
    Function.HasTemperateGrowth (fun t : ℝ => ((t : ℂ) + z)⁻¹) := by
  have hne : ∀ t : ℝ, ((t : ℂ) + z) ≠ 0 := by
    intro t hc
    apply hz
    have := congrArg Complex.im hc
    rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.zero_im] at this
    exact this
  have hlb : ∀ t : ℝ, |z.im| ≤ ‖(t : ℂ) + z‖ := by
    intro t
    have himeq : ((t : ℂ) + z).im = z.im := by simp
    calc |z.im| = |((t : ℂ) + z).im| := by rw [himeq]
      _ ≤ ‖(t : ℂ) + z‖ := Complex.abs_im_le_norm _
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  refine hasTemperateGrowth_of_bounded_iteratedDeriv
    (ContDiff.inv (Complex.ofRealCLM.contDiff.add contDiff_const) hne) (fun n => ?_)
  refine ⟨(n ! : ℝ) / |z.im| ^ (n + 1), fun t => ?_⟩
  rw [iteratedDeriv_inv_ofReal_add hne n]
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [Complex.norm_natCast]
  gcongr
  exact hlb t

/-- **Solvability of the resolvent equation on Schwartz space.**  For every non-real `z` and every
Schwartz function `h`, there is a Schwartz function `u` with `-u'' + z u = h`. -/
