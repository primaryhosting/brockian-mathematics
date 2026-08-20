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
