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


theorem amo_isSelfAdjoint (lam alpha theta : ℝ) : IsSelfAdjoint (amo lam alpha theta) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  have e1 : (Equiv.addRight (1 : ℤ)).symm = Equiv.addRight (-1 : ℤ) := by
    ext i; simp [Equiv.addRight]
  have e2 : (Equiv.addRight (-1 : ℤ)).symm = Equiv.addRight (1 : ℤ) := by
    ext i; simp [Equiv.addRight]
  have h1 : inner ℂ (reindexCLM (Equiv.addRight (1 : ℤ)) f) g
      = inner ℂ f (reindexCLM (Equiv.addRight (-1 : ℤ)) g) := by
    rw [reindexCLM_inner, e1]
  have h2 : inner ℂ (reindexCLM (Equiv.addRight (-1 : ℤ)) f) g
      = inner ℂ f (reindexCLM (Equiv.addRight (1 : ℤ)) g) := by
    rw [reindexCLM_inner, e2]
  have h3 := mulCLM_inner (amoPotential lam alpha theta) (2 * |lam|)
    (amoPotential_bound lam alpha theta) (amoPotential_isReal lam alpha theta) f g
  show inner ℂ (amo lam alpha theta f) g = inner ℂ f (amo lam alpha theta g)
  simp only [amo, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right, h1, h2, h3]
  ring

/-- Norm bound for the almost Mathieu operator. -/
