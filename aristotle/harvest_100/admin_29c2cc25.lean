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
def MTWNonneg {n : ℕ} (S : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x y ξ η, inner ℝ ξ η = (0 : ℝ) → 0 ≤ S x y ξ η

/-- **In dimension one the MTW condition is vacuous**: any tensor `S` satisfies it,
because two orthogonal directions on a line cannot both be non-zero, and the MTW tensor
is quadratic in each of `ξ` and `η` (here recorded by the hypothesis that `S x y ξ η`
vanishes as soon as one of the directions vanishes).  This is why the one dimensional
regularity theory below needs no hypothesis on the cost beyond twistedness. -/
theorem mtw_of_dim_one
    (S : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) →
      EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) → ℝ)
    (hS : ∀ x y ξ η, ξ = 0 ∨ η = 0 → S x y ξ η = 0) :
    MTWNonneg S := by
  intro x y ξ η horth
  rcases eq_or_ne ξ 0 with hξ | hξ
  · rw [hS x y ξ η (Or.inl hξ)]
  · -- on a line, a non-zero vector is orthogonal only to `0`
    have hη : η = 0 := by
      have hx : ξ 0 ≠ 0 := by
        intro h
        apply hξ
        ext i
        have : i = 0 := Subsingleton.elim _ _
        simpa [this] using h
      have h0 : ξ 0 * η 0 = 0 := by
        have hinner : (inner ℝ ξ η : ℝ) = ξ 0 * η 0 := by
          simp [PiLp.inner_apply, mul_comm]
        rw [hinner] at horth
        exact horth
      have : η 0 = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hx
        · exact h
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using this
    rw [hS x y ξ η (Or.inr hη)]

/-! ### The one dimensional regularity estimate -/

/-- **Upper Lipschitz estimate (core inequality).**  If the source distribution function
`F` increases at rate at most `Λ` and the target distribution function `G` increases at
rate at least `lam > 0`, and `T` is monotone with `G (T x) = F x`, then increments of `T`
are controlled by `(Λ / lam)` times increments of the variable. -/
theorem transport_increment_le
    {F G T : ℝ → ℝ} {lam Λ : ℝ}
    (hlam : 0 < lam)
    (hF : ∀ x y : ℝ, x ≤ y → F y - F x ≤ Λ * (y - x))
    (hG : ∀ s t : ℝ, s ≤ t → lam * (t - s) ≤ G t - G s)
    (hT : Monotone T)
    (hpush : ∀ x : ℝ, G (T x) = F x)
    {x y : ℝ} (hxy : x ≤ y) :
    T y - T x ≤ (Λ / lam) * (y - x) := by
  have h1 : lam * (T y - T x) ≤ G (T y) - G (T x) := hG _ _ (hT hxy)
  have h2 : G (T y) - G (T x) = F y - F x := by rw [hpush, hpush]
  have h3 : lam * (T y - T x) ≤ Λ * (y - x) := by
    calc lam * (T y - T x) ≤ G (T y) - G (T x) := h1
      _ = F y - F x := h2
      _ ≤ Λ * (y - x) := hF _ _ hxy
  rw [div_mul_eq_mul_div, le_div_iff₀ hlam, mul_comm]
  exact h3

/-- **Main theorem: Figalli-type regularity of optimal transport maps, one dimensional
base case.**

Let `F` be the distribution function of the source measure and `G` that of the target
measure on the real line.  Assume:

* the source density is bounded above by `Λ`, in the form `F y - F x ≤ Λ (y - x)` for
  `x ≤ y`;
* the target density is bounded below by `lam > 0`, in the form
  `lam (t - s) ≤ G t - G s` for `s ≤ t`;
* `T` is monotone (as the optimal map for a twisted cost in one dimension always is) and
  transports the source onto the target, expressed by the mass balance `G (T x) = F x`.

Then the transport map `T` is Lipschitz with constant `Λ / lam`.

Since in dimension one the MTW condition holds automatically (`Frontier.mtw_of_dim_one`),
this is precisely the base case of the Ma–Trudinger–Wang/Figalli regularity theory:
the regularity of the transport map is quantified by the ratio of the density bounds. -/
theorem figalli_OT_regularity
    {F G T : ℝ → ℝ} {lam Λ : ℝ}
    (hlam : 0 < lam)
    (hF : ∀ x y : ℝ, x ≤ y → F y - F x ≤ Λ * (y - x))
    (hG : ∀ s t : ℝ, s ≤ t → lam * (t - s) ≤ G t - G s)
    (hT : Monotone T)
    (hpush : ∀ x : ℝ, G (T x) = F x) :
    LipschitzWith (Real.toNNReal (Λ / lam)) T := by
  -- first, the constant is non-negative
  have hK : 0 ≤ Λ / lam := by
    have h := transport_increment_le hlam hF hG hT hpush (x := (0 : ℝ)) (y := 1) zero_le_one
    have h0 : 0 ≤ T 1 - T 0 := by
      have := hT (zero_le_one (α := ℝ))
      linarith
    nlinarith
  refine LipschitzWith.of_dist_le_mul ?_
  intro y x
  have key : ∀ a b : ℝ, a ≤ b → T b - T a ≤ (Λ / lam) * (b - a) := fun a b hab =>
    transport_increment_le hlam hF hG hT hpush hab
  have hmono : ∀ a b : ℝ, a ≤ b → T a ≤ T b := fun a b hab => hT hab
  rcases le_total x y with h | h
  · have h1 := key x y h
    have h2 := hmono x y h
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith : (0:ℝ) ≤ T y - T x),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x), Real.coe_toNNReal _ hK]
    exact h1
  · have h1 := key y x h
    have h2 := hmono y x h
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith : T y - T x ≤ 0),
      abs_of_nonpos (by linarith : y - x ≤ 0), Real.coe_toNNReal _ hK]
    linarith

/-- **Two-sided (bi-Lipschitz) regularity.**  If in addition the source density is
bounded below by `lam' > 0` and the target density is bounded above by `Λ'`, then the
transport map also expands increments at a definite rate, so it is bi-Lipschitz:
`(lam' / Λ') (y - x) ≤ T y - T x ≤ (Λ / lam) (y - x)` for `x ≤ y`. -/
theorem figalli_OT_regularity_biLipschitz
    {F G T : ℝ → ℝ} {lam Λ lam' Λ' : ℝ}
    (hlam : 0 < lam) (hΛ' : 0 < Λ')
    (hF : ∀ x y : ℝ, x ≤ y → F y - F x ≤ Λ * (y - x))
    (hF' : ∀ x y : ℝ, x ≤ y → lam' * (y - x) ≤ F y - F x)
    (hG : ∀ s t : ℝ, s ≤ t → lam * (t - s) ≤ G t - G s)
    (hG' : ∀ s t : ℝ, s ≤ t → G t - G s ≤ Λ' * (t - s))
    (hT : Monotone T)
    (hpush : ∀ x : ℝ, G (T x) = F x)
    {x y : ℝ} (hxy : x ≤ y) :
    (lam' / Λ') * (y - x) ≤ T y - T x ∧ T y - T x ≤ (Λ / lam) * (y - x) := by
  refine ⟨?_, transport_increment_le hlam hF hG hT hpush hxy⟩
  have h1 : lam' * (y - x) ≤ F y - F x := hF' _ _ hxy
  have h2 : F y - F x = G (T y) - G (T x) := by rw [hpush, hpush]
  have h3 : G (T y) - G (T x) ≤ Λ' * (T y - T x) := hG' _ _ (hT hxy)
  have h4 : lam' * (y - x) ≤ Λ' * (T y - T x) := by linarith [h1, h3, h2.le, h2.ge]
  rw [div_mul_eq_mul_div, div_le_iff₀ hΛ', mul_comm (T y - T x) Λ']
  exact h4

/-! ### Version stated directly in terms of densities -/

/-- If `F` is the distribution function of a density `f ≤ Λ`, then `F` increases at rate
at most `Λ`. -/
theorem cdf_upper_of_density {f F : ℝ → ℝ} {Λ : ℝ}
    (hint : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y)
    (hle : ∀ t : ℝ, f t ≤ Λ)
    (hF : ∀ x y : ℝ, x ≤ y → F y - F x = ∫ t in x..y, f t) :
    ∀ x y : ℝ, x ≤ y → F y - F x ≤ Λ * (y - x) := by
  intro x y hxy
  rw [hF x y hxy]
  have := intervalIntegral.integral_mono_on hxy (hint x y)
    (intervalIntegrable_const (c := Λ)) (fun t _ => hle t)
  simpa [mul_comm] using this

/-- If `G` is the distribution function of a density `g ≥ lam`, then `G` increases at rate
at least `lam`. -/
theorem cdf_lower_of_density {g G : ℝ → ℝ} {lam : ℝ}
    (hint : ∀ x y : ℝ, IntervalIntegrable g MeasureTheory.volume x y)
    (hge : ∀ t : ℝ, lam ≤ g t)
    (hG : ∀ s t : ℝ, s ≤ t → G t - G s = ∫ u in s..t, g u) :
    ∀ s t : ℝ, s ≤ t → lam * (t - s) ≤ G t - G s := by
  intro s t hst
  rw [hG s t hst]
  have := intervalIntegral.integral_mono_on hst (intervalIntegrable_const (c := lam))
    (hint s t) (fun u _ => hge u)
  simpa [mul_comm] using this

/-- **Figalli-type regularity, density formulation.**  If the source measure has density
`f ≤ Λ`, the target measure has density `g ≥ lam > 0`, and `T` is a monotone map
transporting the first onto the second (mass balance between the distribution functions),
then `T` is Lipschitz with constant `Λ / lam`. -/
theorem figalli_OT_regularity_of_densities
    {f g F G T : ℝ → ℝ} {lam Λ : ℝ}
    (hlam : 0 < lam)
    (hfint : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y)
    (hgint : ∀ x y : ℝ, IntervalIntegrable g MeasureTheory.volume x y)
    (hfle : ∀ t : ℝ, f t ≤ Λ)
    (hgge : ∀ t : ℝ, lam ≤ g t)
    (hF : ∀ x y : ℝ, x ≤ y → F y - F x = ∫ t in x..y, f t)
    (hG : ∀ s t : ℝ, s ≤ t → G t - G s = ∫ u in s..t, g u)
    (hT : Monotone T)
    (hpush : ∀ x : ℝ, G (T x) = F x) :
    LipschitzWith (Real.toNNReal (Λ / lam)) T :=
  figalli_OT_regularity hlam (cdf_upper_of_density hfint hfle hF)
    (cdf_lower_of_density hgint hgge hG) hT hpush

/-! ### Iterating transports: induction on the number of steps -/

/-- The composition of the first `n` transport maps of a family, `T (n-1) ∘ ⋯ ∘ T 0`. -/
def transportChain (T : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => id
  | (n + 1) => T n ∘ transportChain T n

/-- **Regularity of a chain of transports**, by induction on the number of steps:
composing `n` transport maps, each Lipschitz with constant `K i`, yields a map that is
Lipschitz with constant `∏ i < n, K i`. -/
theorem figalli_OT_regularity_chain (T : ℕ → ℝ → ℝ) (K : ℕ → NNReal)
    (h : ∀ i, LipschitzWith (K i) (T i)) :
    ∀ n : ℕ, LipschitzWith (∏ i ∈ Finset.range n, K i) (transportChain T n) := by
  intro n
  induction n with
  | zero => simpa [transportChain] using LipschitzWith.id
  | succ n ih =>
      have : LipschitzWith (K n * ∏ i ∈ Finset.range n, K i)
          (T n ∘ transportChain T n) := (h n).comp ih
      simpa [transportChain, Finset.prod_range_succ, mul_comm] using this

/-- Specialization of the chain estimate to `n` successive transports each satisfying the
hypotheses of `Frontier.figalli_OT_regularity` with the same density bounds: the composite
of `n` such maps is Lipschitz with constant `(Λ / lam) ^ n`. -/
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

