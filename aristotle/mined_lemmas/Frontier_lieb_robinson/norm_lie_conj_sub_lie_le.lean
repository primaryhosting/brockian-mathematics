/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

open NormedSpace

namespace Frontier

section

variable {A : Type*} [CStarAlgebra A]

/-- A `ℚ`-normed-algebra structure, obtained by restricting scalars from `ℂ`; it is needed
to talk about `NormedSpace.exp` in a C⋆-algebra. -/
noncomputable local instance normedAlgebraRatOfCStarAlgebra : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℂ A

/-- `exp (t • H)` commutes with `H`. -/

lemma norm_lie_conj_sub_lie_le {H : A} (hH : star H = -H) (a b : A) (t : ℝ) :
    ‖⁅a, exp ((-t) • H) * b * exp (t • H)⁆ - ⁅a, b⁆‖ ≤ 2 * ‖a‖ * ‖⁅b, H⁆‖ * |t| := by
  set f : ℝ → A := fun r : ℝ => ⁅a, exp ((-r) • H) * b * exp (r • H)⁆ with hf
  set f' : ℝ → A := fun r : ℝ => ⁅a, exp ((-r) • H) * ⁅b, H⁆ * exp (r • H)⁆ with hf'
  have hderiv : ∀ s : ℝ, HasDerivAt f (f' s) s := by
    intro s
    have h := hasDerivAt_conj H b s
    have h2 := (h.const_mul a).sub (h.mul_const a)
    simpa only [hf, hf', Ring.lie_def] using h2
  have hbound : ∀ s : ℝ, ‖f' s‖ ≤ 2 * ‖a‖ * ‖⁅b, H⁆‖ := by
    intro s
    have h1 : ‖f' s‖ ≤ 2 * ‖a‖ * ‖exp ((-s) • H) * ⁅b, H⁆ * exp (s • H)‖ :=
      norm_lie_le _ _
    rwa [norm_conj_exp' hH s ⁅b, H⁆] at h1
  have hmvt := (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (C := 2 * ‖a‖ * ‖⁅b, H⁆‖)
    (fun x _ => (hderiv x).hasDerivWithinAt) (fun x _ => hbound x)
    (Set.mem_univ 0) (Set.mem_univ t)
  have h0 : f 0 = ⁅a, b⁆ := by simp [hf]
  have hft : f t = ⁅a, exp ((-t) • H) * b * exp (t • H)⁆ := rfl
  rw [h0, hft] at hmvt
  simpa only [Real.norm_eq_abs, sub_zero] using hmvt

/-- **Lieb–Robinson bound (base case): an effective light cone for local dynamics.**

Let `A` be a unital C⋆-algebra and `H` an anti-self-adjoint element (`H = i·(Hamiltonian)`),
so that `U t = exp (t • H)` is the unitary time-evolution group.  For observables `a` and `b`,
the Heisenberg-evolved observable `a t = U t * a * U (-t)` satisfies

`‖⁅a t, b⁆‖ ≤ ‖⁅a, b⁆‖ + 2 ‖a‖ ‖⁅b, H⁆‖ |t|`.

Thus the commutator of `b` with the evolved observable can become nonzero only at a rate
governed by the interaction strength `‖⁅b, H⁆‖` felt by `b`: outside the resulting light cone
the dynamics is (approximately) local.  In particular, if `b` commutes both with `a` and with
the generator `H`, then `⁅a t, b⁆ = 0` for all times. -/
