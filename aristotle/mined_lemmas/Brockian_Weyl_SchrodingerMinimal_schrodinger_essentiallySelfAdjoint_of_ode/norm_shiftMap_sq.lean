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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

The first part of this file develops the abstract von Neumann / Weyl deficiency criterion for
essential self-adjointness of a densely defined symmetric operator on a complex Hilbert space.

The second part constructs the minimal Schrödinger operator `-d²/dx² + V` on `L²(ℝ)`, with domain
the smooth compactly supported functions, and shows that it is essentially self-adjoint as soon as
the differential equation `-u'' + V u = ± i u` has no nonzero solution in `L²(ℝ)` (understood in
the distributional sense).
-/

namespace Brockian.Weyl

open LinearPMap Complex

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A partially defined operator `T` on a complex inner product space is *symmetric* if
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in its domain. -/

theorem norm_shiftMap_sq {A : E →ₗ.[ℂ] E} (hs : IsSymmetricPMap A) (c : ℝ) (x : A.domain) :
    ‖shiftMap A c x‖ ^ 2 = ‖A x‖ ^ 2 + c ^ 2 * ‖(x : E)‖ ^ 2 := by
  have h : ⟪A x, (x : E)⟫ = ⟪(x : E), A x⟫ := hs x x
  rw [shiftMap_apply]
  have h2 : (⟪A x, (x : E)⟫ : ℂ).im = 0 := by
    have h3 : (starRingEnd ℂ) (⟪A x, (x : E)⟫ : ℂ) = ⟪A x, (x : E)⟫ := by
      rw [inner_conj_symm, h]
    rw [Complex.conj_eq_iff_im] at h3
    exact h3
  have h1 : RCLike.re (⟪A x, ((c : ℂ) * Complex.I) • (x : E)⟫ : ℂ) = 0 := by
    rw [inner_smul_right]
    simp [h2]
  have h4 : ‖((c : ℂ) * Complex.I) • (x : E)‖ = |c| * ‖(x : E)‖ := by
    rw [norm_smul]; simp
  rw [@norm_add_sq ℂ, h1, h4, mul_pow, sq_abs]
  ring

end Basic

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

namespace IsSymmetricPMap

variable {T : E →ₗ.[ℂ] E}

