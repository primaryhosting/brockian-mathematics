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
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory Set

/-! ### The Ma–Trudinger–Wang condition (Loeper's form) -/

section MTW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic transport cost `c(x,y) = ‖x - y‖²/2`. -/

theorem preimage_Icc_subset {T : ℝ → ℝ} (hT : Monotone T) (x y : ℝ) :
    T ⁻¹' (Icc (T x) (T y)) ⊆ Icc x y ∪ (T ⁻¹' {T x} ∪ T ⁻¹' {T y}) := by
  intro t ht
  simp only [mem_preimage, mem_Icc] at ht
  rcases le_or_gt x t with h1 | h1
  · rcases le_or_gt t y with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inr (by simp [le_antisymm ht.2 (hT h2.le)]))
  · exact Or.inr (Or.inl (by simp [le_antisymm (hT h1.le) ht.1]))

/--
**Regularity of optimal transport maps (Figalli), model case.**

Let `T : ℝ → ℝ` be an optimal transport map for the quadratic cost `c(x,y) = ‖x-y‖²/2`
(which satisfies the Ma–Trudinger–Wang condition `MTW(0)`, see
`Frontier.quadCost_loeperMaxPrinciple`), pushing forward a measure with density `f ≤ Λ`
onto a measure with density `g ≥ λ > 0`.  Optimality is expressed through two-point
`c`-cyclical monotonicity of the graph of `T`, which is the Kantorovich optimality
criterion.  Then `T` is Lipschitz with constant `Λ/λ`; in particular the transport map is
regular, with a quantitative modulus depending only on the density bounds.
-/
