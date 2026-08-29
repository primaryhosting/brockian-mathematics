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
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The Hilbert space `ℓ²(ℤ)` on which the almost Mathieu operator acts. -/
abbrev HilbertZ : Type := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial HilbertZ := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have := congrArg (fun f : HilbertZ => (f : ℤ → ℂ) 0) h
  simp at this


noncomputable def mulFn (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : HilbertZ) : HilbertZ :=
  ⟨fun n => (v n : ℂ) * (f : ℤ → ℂ) n, memℓp_mul v C hv f⟩

