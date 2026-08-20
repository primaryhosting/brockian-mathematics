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


theorem amo_norm_le (lam alpha theta : ℝ) : ‖amo lam alpha theta‖ ≤ 2 + 2 * |lam| := by
  have hb : ‖reindexCLM (Equiv.addRight (1 : ℤ))‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hb' : ‖reindexCLM (Equiv.addRight (-1 : ℤ))‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hm : ‖mulCLM (amoPotential lam alpha theta) (2 * |lam|)
      (amoPotential_bound lam alpha theta)‖ ≤ 2 * |lam| :=
    LinearMap.mkContinuous_norm_le _ (by positivity) _
  have := norm_add₃_le (a := reindexCLM (Equiv.addRight (1 : ℤ)))
    (b := reindexCLM (Equiv.addRight (-1 : ℤ)))
    (c := mulCLM (amoPotential lam alpha theta) (2 * |lam|) (amoPotential_bound lam alpha theta))
  calc ‖amo lam alpha theta‖ ≤ _ := this
    _ ≤ 1 + 1 + 2 * |lam| := by gcongr
    _ = 2 + 2 * |lam| := by ring

/-- The shift `(U f) n = f (n + 1)` as a unit of the algebra of bounded operators on `ℓ²(ℤ)`. -/
