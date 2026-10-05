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

theorem norm_le_norm_add_I_smul {A : H →ₗ.[ℂ] H} (hsymm : A.IsFormalAdjoint A) (x : A.domain) :
    ‖(x : H)‖ ≤ ‖A x + Complex.I • (x : H)‖ := by
  have hre : (⟪A x, (x : H)⟫ : ℂ) = ⟪(x : H), A x⟫ := hsymm x x
  have h2 : (⟪A x, (x : H)⟫ : ℂ).im = 0 := by
    have h1 : (starRingEnd ℂ) (⟪A x, (x : H)⟫) = (⟪A x, (x : H)⟫ : ℂ) := by
      rw [inner_conj_symm]; exact hre.symm
    have := congrArg Complex.im h1
    simp only [Complex.conj_im] at this
    linarith
  have hzero : Complex.re (⟪A x, Complex.I • (x : H)⟫ : ℂ) = 0 := by
    rw [inner_smul_right]
    simp [Complex.mul_re, h2]
  have hsq : ‖A x + Complex.I • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
    rw [@norm_add_sq ℂ]
    simp only [hzero, norm_smul, Complex.norm_I, one_mul, RCLike.re_to_complex]
    ring
  have h1 : ‖(x : H)‖ ^ 2 ≤ ‖A x + Complex.I • (x : H)‖ ^ 2 := by
    rw [hsq]; nlinarith [sq_nonneg ‖A x‖]
  by_contra hcon
  push_neg at hcon
  nlinarith [norm_nonneg (A x + Complex.I • (x : H)), norm_nonneg ((x : H))]

/-- If `A` is closed, symmetric and the range of `A + i` is dense, then `A + i` is surjective. -/
