import Mathlib

/-!
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
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

namespace Frontier

/--
**Noether's theorem, one-dimensional case.**

Setting: a Lagrangian `L : ℝ → ℝ → ℝ` in one degree of freedom, written `L q v`
(position `q`, velocity `v`), whose partial derivatives are `Lq` (with respect to
position) and `Lv` (with respect to velocity).

A smooth infinitesimal symmetry is a vector field `ξ : ℝ → ℝ` on configuration space,
with derivative `dξ`, generating `q ↦ q + s * ξ q + O(s²)`.  Invariance of the action
under this one-parameter family is, to first order, exactly the pointwise condition

`Lq q v * ξ q + Lv q v * (dξ q * v) = 0`  (`hinv`),

i.e. the derivative at `s = 0` of the transformed Lagrangian vanishes.

Along a trajectory `q : ℝ → ℝ` with velocity `v` (`hv`), obeying the Euler–Lagrange
equation `d/dt (Lv q v) = Lq q v` (`hEL`, where `p t = Lv (q t) (v t)` is the
canonical momentum, `hp`), the associated **Noether current**

`J t = p t * ξ (q t)`

is conserved: its time derivative vanishes identically, hence it is constant in time.
-/
theorem noether_conservation
    (Lq Lv : ℝ → ℝ → ℝ) (ξ dξ : ℝ → ℝ) (q v p : ℝ → ℝ)
    (hξ : ∀ x, HasDerivAt ξ (dξ x) x)
    (hinv : ∀ x w, Lq x w * ξ x + Lv x w * (dξ x * w) = 0)
    (hv : ∀ t, HasDerivAt q (v t) t)
    (hp : ∀ t, p t = Lv (q t) (v t))
    (hEL : ∀ t, HasDerivAt p (Lq (q t) (v t)) t) :
    (∀ t, HasDerivAt (fun s => p s * ξ (q s)) 0 t) ∧
      ∀ t₁ t₂ : ℝ, p t₁ * ξ (q t₁) = p t₂ * ξ (q t₂) := by
  have key : ∀ t : ℝ, HasDerivAt (fun s => p s * ξ (q s)) 0 t := by
    intro t
    have hchain : HasDerivAt (fun s => ξ (q s)) (dξ (q t) * v t) t :=
      (hξ (q t)).comp t (hv t)
    have hmul := (hEL t).mul hchain
    have hzero : Lq (q t) (v t) * ξ (q t) + p t * (dξ (q t) * v t) = 0 := by
      rw [hp t]; exact hinv (q t) (v t)
    rwa [hzero] at hmul
  refine ⟨key, ?_⟩
  intro t₁ t₂
  have hconst : ∀ t : ℝ, (fun s => p s * ξ (q s)) t = p 0 * ξ (q 0) := by
    intro t
    exact is_const_of_deriv_eq_zero (fun s => (key s).differentiableAt)
      (fun s => (key s).deriv) t 0
  simpa using (hconst t₁).trans (hconst t₂).symm

/--
Sanity check / illustration: the free particle `L q v = v ^ 2 / 2` with the translation
symmetry `ξ ≡ 1` (partials `Lq = 0`, `Lv q v = v`).  Along the free trajectory
`q t = a + b * t` the Noether current is the momentum `b`, which is indeed conserved.
-/
example (a b : ℝ) :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => (fun _ : ℝ => b) s * (1 : ℝ)) 0 t) ∧
      ∀ _ _ : ℝ, (b : ℝ) * 1 = b * 1 :=
  noether_conservation (fun _ _ => 0) (fun _ w => w) (fun _ => 1) (fun _ => 0)
    (fun t => a + b * t) (fun _ => b) (fun _ => b)
    (fun x => hasDerivAt_const x 1)
    (by intro x w; ring)
    (fun t => by simpa using ((hasDerivAt_id t).const_mul b).const_add a)
    (fun _ => rfl)
    (fun t => hasDerivAt_const t b)

#print axioms Frontier.noether_conservation

end Frontier

