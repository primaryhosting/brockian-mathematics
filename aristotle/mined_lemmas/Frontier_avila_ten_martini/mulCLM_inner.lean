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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The Hilbert space `ℓ²(ℤ; ℂ)` on which the almost Mathieu operator acts. -/
abbrev Ell2 := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial Ell2 := by
  refine ⟨lp.single 2 0 1, 0, ?_⟩
  intro h
  have := congrArg (fun f : Ell2 => (f : ℤ → ℂ) 0) h
  simp at this


theorem mulCLM_inner (v : ℤ → ℂ) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C)
    (hreal : ∀ i, (starRingEnd ℂ) (v i) = v i) (f g : Ell2) :
    inner ℂ (mulCLM v C hv f) g = inner ℂ f (mulCLM v C hv g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  simp only [mulCLM_apply, RCLike.inner_apply, map_mul, hreal i]
  ring

/-! ## The almost Mathieu operator -/

/-- The potential of the almost Mathieu operator with coupling `lam`, flux `alpha` and phase
`theta`: `v n = 2 * lam * cos (2 π (theta + n α))`. -/
