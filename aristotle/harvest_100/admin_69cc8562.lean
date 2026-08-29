/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QPhys

/-- If the Lagrangian `L q v` is invariant under translations `q ↦ q + s` of the
position variable, then its partial derivative with respect to position vanishes. -/
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

/--
**Noether's theorem for spatial translations (1D).**

Let `L : ℝ → ℝ → ℝ` be a Lagrangian `L q v` with partial derivatives `Lq` (in position)
and `Lv` (in velocity).  Assume `L` is invariant under translations of the position
variable, i.e. `L (q + s) v = L q v` for all `s`.  Let `q : ℝ → ℝ` be a trajectory with
velocity `v` (so `q' t = v t`) satisfying the Euler–Lagrange equation, expressed as:
the momentum `t ↦ Lv (q t) (v t)` is differentiable with derivative `Lq (q t) (v t)`.

Then the momentum `p t = Lv (q t) (v t)` is conserved: it takes the same value at all times.
-/
theorem noether_translation
    (L Lq Lv : ℝ → ℝ → ℝ)
    (hLq : ∀ q v, HasDerivAt (fun x => L x v) (Lq q v) q)
    (hinv : ∀ s q v, L (q + s) v = L q v)
    (q v : ℝ → ℝ)
    (hEL : ∀ t : ℝ, HasDerivAt (fun s => Lv (q s) (v s)) (Lq (q t) (v t)) t) :
    ∀ t₁ t₂ : ℝ, Lv (q t₁) (v t₁) = Lv (q t₂) (v t₂) := by
  intro t₁ t₂
  set p : ℝ → ℝ := fun t => Lv (q t) (v t) with hp
  have hzero : ∀ t : ℝ, HasDerivAt p 0 t := by
    intro t
    have := hEL t
    rwa [partial_pos_eq_zero_of_translation_invariant L Lq hLq hinv (q t) (v t)] at this
  have hdiff : Differentiable ℝ p := fun t => (hzero t).differentiableAt
  have hderiv : ∀ t : ℝ, deriv p t = 0 := fun t => (hzero t).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv t₁ t₂

/-- Sanity check (non-vacuity): for the free particle `L q v = v ^ 2 / 2`, the trajectory
`q t = c * t` with constant velocity `c` satisfies all hypotheses. -/
example (c : ℝ) :
    ∀ t₁ t₂ : ℝ, (fun _ v : ℝ => v) (c * t₁) c = (fun _ v : ℝ => v) (c * t₂) c := by
  refine noether_translation (fun _ v => v ^ 2 / 2) (fun _ _ => 0) (fun _ v => v)
    (fun q v => ?_) (fun s q v => rfl) (fun t => c * t) (fun _ => c) (fun t => ?_)
  · simpa using (hasDerivAt_const q (v ^ 2 / 2))
  · simpa using (hasDerivAt_const t c)

end QPhys

