import Mathlib
/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open scoped ENNReal

/-! ## The Hilbert space `ℓ²(ℤ, ℝ)` -/

/-- The Hilbert space `ℓ²(ℤ)` (real scalars) on which the almost Mathieu operator acts. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℝ) 2

/-! ## Multiplication and shift operators on `ℓ²(ℤ)` -/


theorem amo_congr {lam₁ alpha₁ theta₁ lam₂ alpha₂ theta₂ : ℝ}
    (h : ∀ n : ℤ, amoPotential lam₁ alpha₁ theta₁ n = amoPotential lam₂ alpha₂ theta₂ n) :
    amo lam₁ alpha₁ theta₁ = amo lam₂ alpha₂ theta₂ := by
  ext f n
  simp only [amo_apply]
  have := h n
  simp only [amoPotential] at this
  rw [this]

/-- The almost Mathieu operator is bounded by `2 + 2|λ|`. -/
