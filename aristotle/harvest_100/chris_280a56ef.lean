/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Partial derivative `∂L/∂q` of a Lagrangian `L q v t` with respect to the position `q`. -/
noncomputable def dLdq (L : ℝ → ℝ → ℝ → ℝ) (q v t : ℝ) : ℝ := deriv (fun x => L x v t) q

/-- Partial derivative `∂L/∂v` of a Lagrangian `L q v t` with respect to the velocity `v`
(the canonical momentum). -/
noncomputable def dLdv (L : ℝ → ℝ → ℝ → ℝ) (q v t : ℝ) : ℝ := deriv (fun w => L q w t) v

/-- A Lagrangian is translation invariant if shifting the position coordinate by any
constant `s` leaves it unchanged. -/
def TranslationInvariant (L : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ s q v t, L (q + s) v t = L q v t

/-- The canonical momentum `p t = ∂L/∂v (q t, q̇ t, t)` along a path `q`. -/
noncomputable def momentum (L : ℝ → ℝ → ℝ → ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  dLdv L (q t) (deriv q t) t

/-- Translation invariance makes the Lagrangian independent of the position. -/
theorem dLdq_eq_zero_of_translationInvariant {L : ℝ → ℝ → ℝ → ℝ}
    (h : TranslationInvariant L) (q v t : ℝ) : dLdq L q v t = 0 := by
  have hconst : (fun x : ℝ => L x v t) = fun _ : ℝ => L 0 v t := by
    funext x
    simpa using h x 0 v t
  simp [dLdq, hconst]

/-- **Noether's theorem for spatial translations (1D).**

If a Lagrangian `L q v t` is invariant under translations of the position coordinate, then
along any path `q` satisfying the Euler–Lagrange equation
`d/dt (∂L/∂v (q t, q̇ t, t)) = ∂L/∂q (q t, q̇ t, t)`,
the canonical momentum `p t = ∂L/∂v (q t, q̇ t, t)` is conserved. -/
theorem noether_translation (L : ℝ → ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (hinv : TranslationInvariant L)
    (hEL : ∀ t : ℝ, HasDerivAt (momentum L q) (dLdq L (q t) (deriv q t) t) t)
    (t₁ t₂ : ℝ) : momentum L q t₁ = momentum L q t₂ := by
  have hEL0 : ∀ t : ℝ, HasDerivAt (momentum L q) 0 t := by
    intro t
    simpa [dLdq_eq_zero_of_translationInvariant hinv] using hEL t
  exact is_const_of_deriv_eq_zero (fun t => (hEL0 t).differentiableAt)
    (fun t => (hEL0 t).deriv) t₁ t₂

end QPhys

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

