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


theorem amoSpectrum_subset_Icc (lam alpha theta : ℝ) :
    amoSpectrum lam alpha theta ⊆ Set.Icc (-(2 + 2 * |lam|)) (2 + 2 * |lam|) := by
  intro E hE
  have h1 : ‖(E : ℂ)‖ ≤ ‖amo lam alpha theta‖ := spectrum.norm_le_norm_of_mem hE
  have h2 : |E| ≤ 2 + 2 * |lam| :=
    le_trans (by simpa using h1) (amo_norm_le lam alpha theta)
  rw [abs_le] at h2
  exact ⟨h2.1, h2.2⟩

