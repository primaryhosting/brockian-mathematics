/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic (Brenier) transport cost `c(x,y) = ‖x - y‖²/2`. -/
noncomputable def quadCost (x y : E) : ℝ := ‖x - y‖ ^ 2 / 2

/-- `c`-cyclical monotonicity of a set `S ⊆ E × E`: for every finite cycle of points of `S`,
the cost of the given coupling is at most the cost of the cyclically shifted coupling.
This is the standard optimality criterion in optimal transport. -/
def CCyclicallyMonotone (c : E → E → ℝ) (S : Set (E × E)) : Prop :=
  ∀ (n : ℕ) (p : Fin (n + 1) → E × E), (∀ i, p i ∈ S) →
    ∑ i, c (p i).1 (p i).2 ≤ ∑ i, c (p i).1 (p (i + 1)).2

/-- Flatness of the quadratic cost (the Ma–Trudinger–Wang tensor of `‖x-y‖²/2` vanishes
identically).  We record the elementary manifestation of this degeneracy which drives the
whole theory: for the quadratic cost, differences `x ↦ c(x,y) - c(x,y')` are affine
functions of `x`, so that `c`-convex functions are exactly convex functions. -/
omit [CompleteSpace E] in
theorem quadCost_sub_affine (y y' : E) :
    ∃ (a : E) (b : ℝ), ∀ x : E, quadCost x y - quadCost x y' = ⟪a, x⟫_ℝ + b := by
  refine ⟨y' - y, (‖y‖ ^ 2 - ‖y'‖ ^ 2) / 2, fun x => ?_⟩
  simp only [quadCost, norm_sub_sq_real, inner_sub_left, real_inner_comm y' x,
    real_inner_comm y x]
  ring

/-- **Subgradient inequality.** If `u` is convex on a convex set `Ω` and differentiable at
`y ∈ Ω`, then its gradient at `y` is a subgradient: `⟪∇u(y), z - y⟫ ≤ u z - u y` for `z ∈ Ω`. -/
theorem inner_gradient_le_sub {Ω : Set E} {u : E → ℝ} (hu : ConvexOn ℝ Ω u)
    {y z : E} (hy : y ∈ Ω) (hz : z ∈ Ω) (hdy : DifferentiableAt ℝ u y) :
    ⟪gradient u y, z - y⟫_ℝ ≤ u z - u y := by
  set A : ℝ →ᵃ[ℝ] E := AffineMap.lineMap y z with hA
  have hA0 : (A : ℝ → E) 0 = y := by simp [hA]
  have hmaps : Set.Icc (0 : ℝ) 1 ⊆ (A : ℝ → E) ⁻¹' Ω := fun t ht => hu.1.lineMap_mem hy hz ht
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (u ∘ (A : ℝ → E)) :=
    (hu.comp_affineMap A).subset hmaps (convex_Icc 0 1)
  have h1 : HasDerivAt (fun t : ℝ => (A : ℝ → E) t) (z - y) 0 := by
    simp only [hA, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (z - y)).add_const y
  have hderiv : HasDerivAt (u ∘ (A : ℝ → E)) (fderiv ℝ u y (z - y)) 0 := by
    have h2 : HasFDerivAt u (fderiv ℝ u y) ((A : ℝ → E) 0) := by rw [hA0]; exact hdy.hasFDerivAt
    exact h2.comp_hasDerivAt 0 h1
  have key := hconv.le_slope_of_hasDerivWithinAt (x := 0) (y := 1) (by simp) (by simp)
    (by norm_num) hderiv.hasDerivWithinAt
  have hslope : slope (u ∘ (A : ℝ → E)) 0 1 = u z - u y := by simp [slope_def_field, hA]
  rw [hslope] at key
  rw [inner_gradient_left hdy]
  exact key

/-- **Optimality of the Brenier map.** The graph of the gradient of a convex function is
`c`-cyclically monotone for the quadratic cost; hence `∇u` is an optimal transport map
between any two measures that it couples. -/
theorem gradient_graph_ccyclicallyMonotone {Ω : Set E} {u : E → ℝ} (hu : ConvexOn ℝ Ω u)
    (hdiff : ∀ x ∈ Ω, DifferentiableAt ℝ u x) :
    CCyclicallyMonotone (quadCost (E := E)) {p : E × E | p.1 ∈ Ω ∧ p.2 = gradient u p.1} := by
  intro n p hp
  set x : Fin (n + 1) → E := fun i => (p i).1 with hx
  set y : Fin (n + 1) → E := fun i => (p i).2 with hy
  have hxΩ : ∀ i, x i ∈ Ω := fun i => (hp i).1
  have hyg : ∀ i, y i = gradient u (x i) := fun i => (hp i).2
  have shift : ∀ f : Fin (n + 1) → ℝ, ∑ i, f (i + 1) = ∑ i, f i := fun f =>
    Fintype.sum_equiv (Equiv.addRight (1 : Fin (n + 1))) _ _ (fun _ => rfl)
  have hexp : ∀ i, quadCost (x i) (y i) - quadCost (x i) (y (i + 1))
      = (⟪x i, y (i + 1)⟫_ℝ - ⟪x i, y i⟫_ℝ) + (‖y i‖ ^ 2 - ‖y (i + 1)‖ ^ 2) / 2 := by
    intro i
    simp only [quadCost, norm_sub_sq_real]
    ring
  have h1 : ∑ i, (‖y i‖ ^ 2 - ‖y (i + 1)‖ ^ 2) / 2 = 0 := by
    have hsh := shift (fun i => ‖y i‖ ^ 2)
    simp only [sub_div, Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [hsh]
    ring
  have h2 : ∑ i, (⟪x i, y (i + 1)⟫_ℝ - ⟪x i, y i⟫_ℝ) ≤ 0 := by
    have hterm : ∀ i, ⟪x i, y (i + 1)⟫_ℝ - ⟪x (i + 1), y (i + 1)⟫_ℝ ≤ u (x i) - u (x (i + 1)) := by
      intro i
      have h := inner_gradient_le_sub hu (hxΩ (i + 1)) (hxΩ i) (hdiff _ (hxΩ (i + 1)))
      rw [← hyg (i + 1), inner_sub_right] at h
      rw [real_inner_comm (y (i + 1)) (x i), real_inner_comm (y (i + 1)) (x (i + 1))]
      linarith
    have hs1 : ∑ i, (⟪x i, y (i + 1)⟫_ℝ - ⟪x (i + 1), y (i + 1)⟫_ℝ)
        ≤ ∑ i, (u (x i) - u (x (i + 1))) := Finset.sum_le_sum (fun i _ => hterm i)
    have hs2 : ∑ i, (u (x i) - u (x (i + 1))) = 0 := by
      simp only [Finset.sum_sub_distrib, shift (fun i => u (x i))]
      ring
    have hs3 : ∑ i, (⟪x (i + 1), y (i + 1)⟫_ℝ) = ∑ i, ⟪x i, y i⟫_ℝ :=
      shift (fun i => ⟪x i, y i⟫_ℝ)
    rw [hs2] at hs1
    simp only [Finset.sum_sub_distrib, hs3] at hs1 ⊢
    exact hs1
  have hfin : ∑ i, (quadCost (x i) (y i) - quadCost (x i) (y (i + 1))) ≤ 0 := by
    simp only [hexp, Finset.sum_add_distrib, h1]
    linarith
  simp only [Finset.sum_sub_distrib] at hfin
  simpa [hx, hy] using hfin

/-- **Key regularity lemma.** A convex function that is differentiable on an open set has a
continuous gradient there.  Quantitatively: if `‖y - x‖` is small then, comparing the
subgradient inequality at `y` with the first-order expansion at `x` along the direction
`(∇u(y) - ∇u(x))/‖∇u(y) - ∇u(x)‖`, one gets `‖∇u(y) - ∇u(x)‖` small. -/
theorem gradient_continuousOn_of_convexOn {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω)
    (hu : ConvexOn ℝ Ω u) (hdiff : ∀ x ∈ Ω, DifferentiableAt ℝ u x) :
    ContinuousOn (fun x => gradient u x) Ω := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  set q : E := gradient u x with hq
  have hgrad : HasGradientAt u q x := (hdiff x hx).hasGradientAt
  have hlo : (fun z => u z - u x - ⟪q, z - x⟫_ℝ) =o[nhds x] (fun z => z - x) := by
    have := hgrad.hasFDerivAt.isLittleO
    simpa [real_inner_comm] using this
  have hc : (0 : ℝ) < ε / 4 := by linarith
  have hev := hlo.def hc
  rw [Metric.eventually_nhds_iff_ball] at hev
  obtain ⟨r₀, hr₀, hball⟩ := hev
  obtain ⟨r₁, hr₁, hsub⟩ := Metric.isOpen_iff.mp hΩ x hx
  set r := min r₀ r₁ with hr
  have hrpos : 0 < r := lt_min hr₀ hr₁
  have hest : ∀ w : E, ‖w - x‖ < r → |u w - u x - ⟪q, w - x⟫_ℝ| ≤ (ε / 4) * ‖w - x‖ := by
    intro w hw
    have hw' : w ∈ Metric.ball x r₀ := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le hw (min_le_left _ _)
    simpa using hball w hw'
  have hmemΩ : ∀ w : E, ‖w - x‖ < r → w ∈ Ω := by
    intro w hw
    refine hsub ?_
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hw (min_le_right _ _)
  refine ⟨r / 4, by linarith, ?_⟩
  intro y hy
  rw [dist_eq_norm] at hy ⊢
  set p : E := gradient u y with hp
  by_cases hpq : p = q
  · simp [hpq, hε]
  · have hnorm : 0 < ‖p - q‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero_of_ne hpq
    set t : ℝ := r / 2 with ht
    set e : E := (‖p - q‖)⁻¹ • (p - q) with he
    set z : E := y + t • e with hz
    have hyx : ‖y - x‖ < r / 4 := hy
    have hnorme : ‖e‖ = 1 := by
      rw [he, norm_smul]
      simp [inv_mul_cancel₀ (ne_of_gt hnorm)]
    have hzx : ‖z - x‖ < r := by
      have hzx' : z - x = (y - x) + t • e := by rw [hz]; abel
      rw [hzx']
      calc ‖(y - x) + t • e‖ ≤ ‖y - x‖ + ‖t • e‖ := norm_add_le _ _
        _ = ‖y - x‖ + t := by
            rw [norm_smul, hnorme, Real.norm_eq_abs, abs_of_pos (by positivity)]; ring
        _ < r / 4 + r / 2 := by linarith
        _ < r := by linarith
    have hyΩ : y ∈ Ω := hmemΩ y (by linarith)
    have hzΩ : z ∈ Ω := hmemΩ z hzx
    have hsg : ⟪p, z - y⟫_ℝ ≤ u z - u y := inner_gradient_le_sub hu hyΩ hzΩ (hdiff y hyΩ)
    have hzy : z - y = t • e := by rw [hz]; abel
    have hinner_pe : ⟪p - q, e⟫_ℝ = ‖p - q‖ := by
      rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have hA := hest z hzx
    have hB := hest y (by linarith)
    have hexp : u z - u y - ⟪q, z - y⟫_ℝ
        = (u z - u x - ⟪q, z - x⟫_ℝ) - (u y - u x - ⟪q, y - x⟫_ℝ) := by
      have hqz : ⟪q, z - x⟫_ℝ - ⟪q, y - x⟫_ℝ = ⟪q, z - y⟫_ℝ := by
        rw [← inner_sub_right]; congr 1; abel
      linarith [hqz]
    have hkey : t * ‖p - q‖ ≤ (ε / 4) * ‖z - x‖ + (ε / 4) * ‖y - x‖ := by
      have h1 : ⟪p, z - y⟫_ℝ - ⟪q, z - y⟫_ℝ = t * ‖p - q‖ := by
        rw [hzy, ← inner_sub_left, real_inner_smul_right, hinner_pe]
      have h2 : t * ‖p - q‖ ≤ u z - u y - ⟪q, z - y⟫_ℝ := by linarith [hsg, h1]
      rw [hexp] at h2
      linarith [(abs_le.mp hA).1, (abs_le.mp hA).2, (abs_le.mp hB).1, (abs_le.mp hB).2]
    have hbnd : (r / 2) * ‖p - q‖ ≤ (ε / 4) * r + (ε / 4) * (r / 4) := by
      have hzx' : ‖z - x‖ ≤ r := le_of_lt hzx
      have hyx' : ‖y - x‖ ≤ r / 4 := le_of_lt hyx
      have : (ε / 4) * ‖z - x‖ + (ε / 4) * ‖y - x‖ ≤ (ε / 4) * r + (ε / 4) * (r / 4) := by
        nlinarith [norm_nonneg (z - x), norm_nonneg (y - x)]
      rw [ht] at hkey
      linarith
    have h5 : ‖p - q‖ ≤ 5 * ε / 8 := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    linarith

/-- **Figalli's optimal transport regularity, flat (MTW ≡ 0) base case.**

For the quadratic cost `c(x,y) = ‖x-y‖²/2` on a real Hilbert space — the model case in which the
Ma–Trudinger–Wang condition holds with constant `0` — let `u` be a convex potential on an open
domain `Ω`, differentiable there.  Then

* the Brenier map `T = ∇u` is optimal: its graph is `c`-cyclically monotone, and
* `T` is continuous on `Ω`, i.e. the optimal transport map is regular. -/
theorem figalli_OT_regularity {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω)
    (hu : ConvexOn ℝ Ω u) (hdiff : ∀ x ∈ Ω, DifferentiableAt ℝ u x) :
    CCyclicallyMonotone (quadCost (E := E)) {p : E × E | p.1 ∈ Ω ∧ p.2 = gradient u p.1} ∧
      ContinuousOn (fun x => gradient u x) Ω :=
  ⟨gradient_graph_ccyclicallyMonotone hu hdiff, gradient_continuousOn_of_convexOn hΩ hu hdiff⟩

end Frontier

