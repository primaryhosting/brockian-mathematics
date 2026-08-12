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

/-- If a Lagrangian `L q v` is invariant under translations `q ↦ q + s` of the position
variable, then its partial derivative with respect to position vanishes. -/
theorem partial_pos_eq_zero_of_translation_invariant
    (L : ℝ → ℝ → ℝ) (Lq : ℝ → ℝ → ℝ)
    (hLq : ∀ q v, HasDerivAt (fun x => L x v) (Lq q v) q)
    (hinv : ∀ s q v, L (q + s) v = L q v) :
    ∀ q v, Lq q v = 0 := by
  intro q v
  have hconst : (fun x : ℝ => L x v) = fun _ : ℝ => L 0 v := by
    funext x
    have := hinv x 0 v
    simpa using this
  have h1 : HasDerivAt (fun x : ℝ => L x v) (Lq q v) q := hLq q v
  rw [hconst] at h1
  exact h1.unique (hasDerivAt_const q (L 0 v))

/-- **Noether's theorem for spatial translations (1D).**

Let `L : ℝ → ℝ → ℝ` be a Lagrangian, written `L q v` in terms of position `q` and velocity `v`,
with partial derivative `Lq` in the position variable.  Assume `L` is invariant under
translations of the position, `L (q + s) v = L q v`.

Let `q : ℝ → ℝ` be a trajectory with velocity `v`, and let `p : ℝ → ℝ` be the conjugate
momentum `p t = ∂L/∂v (q t, v t)` along it.  The Euler–Lagrange equation says that the
time derivative of `p` equals `∂L/∂q` evaluated along the trajectory.

Then the momentum `p` is conserved: it takes the same value at all times. -/
theorem noether_translation
    (L : ℝ → ℝ → ℝ) (Lq : ℝ → ℝ → ℝ)
    (hLq : ∀ q v, HasDerivAt (fun x => L x v) (Lq q v) q)
    (hinv : ∀ s q v, L (q + s) v = L q v)
    (q v p : ℝ → ℝ)
    (hEL : ∀ t, HasDerivAt p (Lq (q t) (v t)) t) :
    ∀ t₁ t₂, p t₁ = p t₂ := by
  have hzero : ∀ t, HasDerivAt p 0 t := by
    intro t
    have := hEL t
    rwa [partial_pos_eq_zero_of_translation_invariant L Lq hLq hinv (q t) (v t)] at this
  have hdiff : Differentiable ℝ p := fun t => (hzero t).differentiableAt
  have hderiv : ∀ t, deriv p t = 0 := fun t => (hzero t).deriv
  intro t₁ t₂
  exact is_const_of_deriv_eq_zero hdiff hderiv t₁ t₂

/-- **Noether's theorem for spatial translations (1D), with the momentum written out.**

Here the conjugate momentum is not an abstract function but literally `t ↦ ∂L/∂v (q t, v t)`,
where `Lv` is the partial derivative of `L` in the velocity variable, `q` is the trajectory
and `v` is its velocity.  The Euler–Lagrange equation is the hypothesis `hEL`.

Translation invariance of `L` then forces this momentum to be conserved.  (The relation
`v = q'` between the trajectory and its velocity is not needed for the conclusion, so it is
not assumed.) -/
theorem noether_translation_momentum
    (L : ℝ → ℝ → ℝ) (Lq Lv : ℝ → ℝ → ℝ)
    (hLq : ∀ q v, HasDerivAt (fun x => L x v) (Lq q v) q)
    (hinv : ∀ s q v, L (q + s) v = L q v)
    (q v : ℝ → ℝ)
    (hEL : ∀ t, HasDerivAt (fun s => Lv (q s) (v s)) (Lq (q t) (v t)) t) :
    ∀ t₁ t₂, Lv (q t₁) (v t₁) = Lv (q t₂) (v t₂) :=
  noether_translation L Lq hLq hinv q v (fun s => Lv (q s) (v s)) hEL

/-- Non-vacuity check: the free particle of mass `m`, with Lagrangian `L q v = m * v ^ 2 / 2`,
position-partial `∂L/∂q = 0`, velocity-partial `∂L/∂v = m * v`, and uniform-motion trajectory
`q t = q₀ + u * t` with velocity `v t = u`, satisfies every hypothesis of
`noether_translation_momentum`: the two partial-derivative hypotheses, translation invariance,
the relation `v = q'`, and the Euler–Lagrange equation. -/
theorem freeParticle_satisfies_noether_hypotheses (m q₀ u : ℝ) :
    (∀ x y : ℝ, HasDerivAt (fun _ : ℝ => m * y ^ 2 / 2) ((fun _ _ : ℝ => (0 : ℝ)) x y) x) ∧
      (∀ x y : ℝ, HasDerivAt (fun w : ℝ => m * w ^ 2 / 2) ((fun _ w : ℝ => m * w) x y) y) ∧
      (∀ _s _x y : ℝ, m * y ^ 2 / 2 = m * y ^ 2 / 2) ∧
      (∀ t : ℝ, HasDerivAt (fun t : ℝ => q₀ + u * t) u t) ∧
      (∀ t : ℝ, HasDerivAt (fun _ : ℝ => m * u) ((fun _ _ : ℝ => (0 : ℝ)) (q₀ + u * t) u) t) := by
  refine ⟨fun x y => by simpa using hasDerivAt_const x (m * y ^ 2 / 2), fun x y => ?_,
    fun _s _x _y => rfl, fun t => by simpa using ((hasDerivAt_id t).const_mul u).const_add q₀,
    fun t => by simpa using hasDerivAt_const t (m * u)⟩
  have h : HasDerivAt (fun w : ℝ => w ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y)
  have := (h.const_mul m).div_const 2
  convert this using 1
  ring

/-- Conservation of momentum for the free particle, obtained from `noether_translation_momentum`:
along uniform motion `q t = q₀ + u * t`, the momentum `m * u` is the same at all times. -/
theorem freeParticle_momentum_conserved (m q₀ u : ℝ) :
    ∀ t₁ t₂ : ℝ,
      (fun _ w : ℝ => m * w) (q₀ + u * t₁) ((fun _ : ℝ => u) t₁) =
        (fun _ w : ℝ => m * w) (q₀ + u * t₂) ((fun _ : ℝ => u) t₂) := by
  obtain ⟨h1, -, h3, -, h5⟩ := freeParticle_satisfies_noether_hypotheses m q₀ u
  exact noether_translation_momentum (fun _ y => m * y ^ 2 / 2) (fun _ _ => 0)
    (fun _ w => m * w) h1 h3 (fun t => q₀ + u * t) (fun _ => u) h5

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

