/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Frontier

/-! ## The cost function and the Ma–Trudinger–Wang condition -/

/-- The quadratic (Brenier) transport cost `c(x,y) = ‖x - y‖² / 2` on a real inner product
space. -/

theorem quadCost_loeperMaximumPrinciple {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : LoeperMaximumPrinciple (quadCost (E := E)) := by
  intro x z y₀ y₁ t ht
  have key : ∀ y : E, quadCost x y - quadCost z y
      = (‖x‖ ^ 2 - ‖z‖ ^ 2) / 2 - inner ℝ (x - z) y := by
    intro y
    simp only [quadCost, inner_sub_left]
    rw [norm_sub_sq_real, norm_sub_sq_real]
    ring
  have hlin : inner ℝ (x - z) ((1 - t) • y₀ + t • y₁)
      = (1 - t) * inner ℝ (x - z) y₀ + t * inner ℝ (x - z) y₁ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [key, key, key, hlin]
  obtain ⟨ht0, ht1⟩ := ht
  rcases le_total ((‖x‖ ^ 2 - ‖z‖ ^ 2) / 2 - inner ℝ (x - z) y₀)
      ((‖x‖ ^ 2 - ‖z‖ ^ 2) / 2 - inner ℝ (x - z) y₁) with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

/-! ## The one-dimensional base case

Here `F` and `G` are the cumulative distribution functions of the source measure `μ` and
the target measure `ν`, and `T` is the monotone (optimal, for the quadratic cost) transport
map, characterised by `G ∘ T = F`.  The hypothesis `hFup` says that `μ` has density at most
`Lam`, and `hGlow` says that `ν` has density at least `lam > 0`.  The conclusion is the
Lipschitz regularity of `T` with the sharp constant `Lam / lam`. -/

/-- One-sided form of the one-dimensional regularity estimate. -/
