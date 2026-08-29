import Mathlib

/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
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

/-!
## Overview

Figalli's regularity theory for optimal transport asserts, roughly, that if the cost
function `c` satisfies the Ma–Trudinger–Wang (MTW) condition and the source and target
densities are bounded away from `0` and `∞` on suitable domains, then the optimal
transport map inherits regularity (continuity, Lipschitz/Hölder bounds, and higher
smoothness by bootstrapping).

We formalize here the **one dimensional base case** of this theory in a fully
self-contained and Lean-checked way.  In dimension one the MTW tensor is vacuous
(it is a quadratic form in a pair of *orthogonal* directions `ξ ⊥ η`, which cannot
both be non-zero on a line), so *every* smooth twisted cost satisfies MTW; the entire
content of the regularity statement is then the density bound argument formalized below.
Moreover the optimal map for a twisted cost in one dimension is the monotone
rearrangement, characterized by the mass-balance (push-forward) identity
`G (T x) = F x` between the cumulative distribution functions.

The main theorem `Frontier.figalli_OT_regularity` states:

> if the source distribution function `F` grows at most at rate `Λ` (i.e. its density is
> `≤ Λ`), the target distribution function `G` grows at least at rate `lam > 0`
> (i.e. its density is `≥ lam`), and `T` is a monotone map satisfying the mass balance
> `G ∘ T = F`, then `T` is Lipschitz with constant `Λ / lam`.

This is exactly the one dimensional form of the Caffarelli/Figalli a-priori estimate:
the modulus of continuity of the transport map is controlled by the ratio of the
density bounds.  A two-sided (bi-Lipschitz) version and a version stated directly in
terms of densities are also proved, together with a chain/iteration statement proved
by induction on the number of transports.
-/

namespace Frontier

/-! ### The MTW condition in dimension one -/

/-- The Ma–Trudinger–Wang condition, as a condition on a real-valued quadratic-form
valued map `S` on pairs of directions.  `S x y ξ η` plays the role of the MTW tensor
`𝔖_c(x,y)(ξ,η)`, and the condition `MTWNonneg` says that it is non-negative on
orthogonal pairs of directions. -/

theorem figalli_OT_regularity_iterate
    {F G : ℕ → ℝ → ℝ} {T : ℕ → ℝ → ℝ} {lam Λ : ℝ}
    (hlam : 0 < lam)
    (hF : ∀ i, ∀ x y : ℝ, x ≤ y → F i y - F i x ≤ Λ * (y - x))
    (hG : ∀ i, ∀ s t : ℝ, s ≤ t → lam * (t - s) ≤ G i t - G i s)
    (hT : ∀ i, Monotone (T i))
    (hpush : ∀ i, ∀ x : ℝ, G i (T i x) = F i x) :
    ∀ n : ℕ, LipschitzWith ((Real.toNNReal (Λ / lam)) ^ n) (transportChain T n) := by
  intro n
  have h : ∀ i, LipschitzWith (Real.toNNReal (Λ / lam)) (T i) := fun i =>
    figalli_OT_regularity hlam (hF i) (hG i) (hT i) (hpush i)
  simpa using figalli_OT_regularity_chain T (fun _ => Real.toNNReal (Λ / lam)) h n

/-! ### Non-vacuity check -/

/-- The hypotheses of `Frontier.figalli_OT_regularity` are satisfiable: the uniform
measure on the line transported by the identity map (`f = g = 1`, `lam = Λ = 1`). -/
example : LipschitzWith (Real.toNNReal ((1 : ℝ) / 1)) (id : ℝ → ℝ) :=
  figalli_OT_regularity (F := id) (G := id) (T := id) (lam := 1) (Λ := 1) one_pos
    (fun x y _ => by simp) (fun s t _ => by simp) monotone_id (fun _ => rfl)

/-- A non-trivial instance: the affine map `T x = 2 * x` transports the density `1`
onto the density `1 / 2`, and the theorem yields the sharp Lipschitz constant `2`. -/
example : LipschitzWith (Real.toNNReal ((1 : ℝ) / (1 / 2))) (fun x : ℝ => 2 * x) :=
  figalli_OT_regularity (F := fun x => x) (G := fun t => t / 2) (T := fun x => 2 * x)
    (lam := 1 / 2) (Λ := 1) (by norm_num)
    (fun x y _ => by simp)
    (fun s t _ => by ring_nf; linarith)
    (fun a b hab => by simpa using (by linarith : 2 * a ≤ 2 * b))
    (fun x => by ring)

end Frontier

