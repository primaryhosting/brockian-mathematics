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


private theorem mulLM_norm (v : ℤ → ℂ) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) (f : Ell2) :
    ‖mulLM v C hv f‖ ≤ C * ‖f‖ := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hv 0)
  apply lp.norm_le_of_tsum_le (by norm_num) (by positivity)
  have hnorm := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ) (by norm_num) f
  simp only [ENNReal.toReal_ofNat, rpow2] at *
  have hle : ∀ i : ℤ, ‖(mulLM v C hv f) i‖ ^ 2 ≤ C ^ 2 * ‖f i‖ ^ 2 := by
    intro i
    have h1 : ‖(mulLM v C hv f) i‖ = ‖v i * f i‖ := rfl
    rw [h1, norm_mul, mul_pow]
    gcongr
    exact hv i
  have hs1 : Summable (fun i : ℤ => ‖(mulLM v C hv f) i‖ ^ 2) := by
    simpa [rpow2] using ((mulLM v C hv f).2.summable (p := 2) (by norm_num))
  calc ∑' i : ℤ, ‖(mulLM v C hv f) i‖ ^ 2
      ≤ ∑' i : ℤ, C ^ 2 * ‖f i‖ ^ 2 := hs1.tsum_le_tsum hle ((sq_summable f).mul_left _)
    _ = C ^ 2 * ‖f‖ ^ 2 := by rw [tsum_mul_left, ← hnorm]
    _ = (C * ‖f‖) ^ 2 := by ring

/-- Multiplication by a bounded sequence, as a bounded operator on `ℓ²(ℤ)`. -/
