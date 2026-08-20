/-
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

/-- **Hellmann–Feynman theorem.**

Let `H : ℝ → (V →L[ℂ] V)` be a family of operators on a complex inner product space,
depending on a parameter `t`, and let `ψ t` be a normalized eigenvector of `H t` with
(real) eigenvalue `E t`.  If `H` and `ψ` are differentiable at `l` and `H l` is
self-adjoint, then

`dE/dt (l) = ⟪ψ l, (dH/dt (l)) (ψ l)⟫`.

(The right-hand side is a real number: we take its real part, which is the whole of it
whenever `dH/dt` is self-adjoint.) -/

theorem hellmann_feynman_deriv
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (H : ℝ → V →L[ℂ] V) (ψ : ℝ → V) (E : ℝ → ℝ) (l : ℝ)
    (Hd : V →L[ℂ] V) (ψd : V)
    (hH : HasDerivAt H Hd l) (hψ : HasDerivAt ψ ψd l)
    (hnorm : ∀ t, inner ℂ (ψ t) (ψ t) = (1 : ℂ))
    (hEig : ∀ t, H t (ψ t) = (E t : ℂ) • ψ t)
    (hsa : ∀ x y, inner ℂ (H l x) y = inner ℂ x (H l y)) :
    deriv E l = (inner ℂ (ψ l) (Hd (ψ l))).re :=
  (hellmann_feynman H ψ E l Hd ψd hH hψ hnorm hEig hsa).deriv

end Phys

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

