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


theorem amo_apply (lam alpha theta : ℝ) (f : Ell2) (n : ℤ) :
    (amo lam alpha theta f : ℤ → ℂ) n
      = f (n + 1) + f (n - 1)
        + ((2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha)) : ℝ) : ℂ) * f n := by
  show (reindexCLM (Equiv.addRight (1 : ℤ)) f : ℤ → ℂ) n
      + (reindexCLM (Equiv.addRight (-1 : ℤ)) f : ℤ → ℂ) n
      + (mulCLM (amoPotential lam alpha theta) (2 * |lam|)
          (amoPotential_bound lam alpha theta) f : ℤ → ℂ) n = _
  simp only [reindexCLM_apply, mulCLM_apply, Equiv.coe_addRight, amoPotential]
  norm_num
  ring_nf

/-- The almost Mathieu operator is a self-adjoint bounded operator. -/
