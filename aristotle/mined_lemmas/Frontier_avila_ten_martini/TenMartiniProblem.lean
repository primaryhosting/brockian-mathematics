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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The Hilbert space `ℓ²(ℤ, ℂ)` on which the almost Mathieu operator acts. -/
abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial L2Z := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have h0 : ‖lp.single (E := fun _ : ℤ => ℂ) 2 (0 : ℤ) (1 : ℂ)‖ = 0 := by rw [h]; simp
  rw [lp.norm_single (by norm_num)] at h0
  simp at h0

/-! ## Shift operators -/


def TenMartiniProblem : Prop :=
  ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha → IsCantorSet (amoSpectrum lam alpha theta)

/-- **Lean-checked reduction of the Ten Martini Problem.**

The spectrum of the almost Mathieu operator is always nonempty and compact (proved here from
scratch, from the construction of the operator on `ℓ²(ℤ)` and its self-adjointness).  Hence the
Ten Martini Problem — Cantor spectrum for all nonzero couplings and all irrational fluxes —
reduces to the two remaining analytic inputs:

* *all spectral gaps are dense*, i.e. the spectrum has empty interior (this is the hard part
  proved by Avila and Jitomirskaya), and
* the spectrum has *no isolated points* (`Preperfect`).

Given those two inputs the full statement follows. -/
