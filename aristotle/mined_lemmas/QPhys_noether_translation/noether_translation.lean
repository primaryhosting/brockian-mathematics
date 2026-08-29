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

/-- If the Lagrangian is invariant under spatial translations, then its partial
derivative with respect to position vanishes identically. -/

theorem noether_translation
    (L Lq Lv : ℝ → ℝ → ℝ)
    (hinv : ∀ a q v, L (q + a) v = L q v)
    (hLq : ∀ q v, HasDerivAt (fun x => L x v) (Lq q v) q)
    (q v p : ℝ → ℝ)
    (hp : ∀ t, p t = Lv (q t) (v t))
    (hEL : ∀ t, HasDerivAt (fun s => Lv (q s) (v s)) (Lq (q t) (v t)) t) :
    ∀ t₁ t₂, p t₁ = p t₂ := by
  have hzero : ∀ x y, Lq x y = 0 :=
    lagrangian_translation_invariant_partial_pos_zero L Lq hinv hLq
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s => Lv (q s) (v s)) 0 t := by
    intro t
    have := hEL t
    rwa [hzero (q t) (v t)] at this
  have hdiff : Differentiable ℝ fun s => Lv (q s) (v s) := fun t =>
    (hderiv t).differentiableAt
  have hconst : ∀ t₁ t₂ : ℝ, Lv (q t₁) (v t₁) = Lv (q t₂) (v t₂) :=
    is_const_of_deriv_eq_zero hdiff fun t => (hderiv t).deriv
  intro t₁ t₂
  rw [hp t₁, hp t₂]
  exact hconst t₁ t₂

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

