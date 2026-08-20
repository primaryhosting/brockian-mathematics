import Mathlib

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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# The SSH model: quantization of the winding number

The Su–Schrieffer–Heeger (SSH) chain has Bloch Hamiltonian
`H(k) = Re h(k) σₓ + Im h(k) σ_y` with off-diagonal (chiral) component

  `h(k) = v + w e^{ik}`,

where `v` is the intracell and `w` the intercell hopping amplitude.  As long as the
spectrum is gapped (`h(k) ≠ 0` for all `k`, which happens exactly when `|v| ≠ |w|`) the
phase is classified by the winding number of the loop `k ↦ h(k)` around the origin,

  `W = (2πi)⁻¹ ∫₀^{2π} h'(k) / h(k) dk`.

We prove that `W` is an integer, equal to `1` in the topological regime `|v| < |w|` and to
`0` in the trivial regime `|w| < |v|`.
-/

namespace Frontier

open Complex Metric

/-- Off-diagonal (chiral) component `h(k) = v + w e^{i k}` of the SSH Bloch Hamiltonian. -/

theorem sshWinding_topological (v w : ℝ) (h : |v| < |w|) : sshWinding v w = 1 := by
  have hw : (w : ℂ) ≠ 0 := by
    have : w ≠ 0 := by
      intro h0; rw [h0] at h; simp at h; exact absurd h (not_lt.2 (abs_nonneg v))
    exact_mod_cast this
  have hpt : (-((v : ℂ) / (w : ℂ))) ∈ ball (0 : ℂ) 1 := by
    have hwn : ‖(w : ℂ)‖ ≠ 0 := by simpa using hw
    have : ‖(v : ℂ) / (w : ℂ)‖ < 1 := by
      rw [norm_div, div_lt_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hwn))]
      simpa [Complex.norm_real, Real.norm_eq_abs] using h
    simpa [Complex.dist_eq] using this
  have hint : (∮ z in C(0, 1), (w : ℂ) / ((v : ℂ) + (w : ℂ) * z))
      = 2 * (Real.pi : ℂ) * Complex.I := by
    have key : ∀ z : ℂ, (w : ℂ) / ((v : ℂ) + (w : ℂ) * z) = (z - (-((v : ℂ) / (w : ℂ))))⁻¹ := by
      intro z
      have hfac : (v : ℂ) + (w : ℂ) * z = (w : ℂ) * (z + (v : ℂ) / (w : ℂ)) := by
        field_simp; ring
      rw [sub_neg_eq_add, hfac, ← div_div, div_self hw, one_div]
    simp only [key]
    exact circleIntegral.integral_sub_inv_of_mem_ball hpt
  rw [sshWinding_eq_circleIntegral, hint]
  exact inv_mul_cancel₀ (by simp [Real.pi_ne_zero])

/-- **The SSH topological invariant.**  Whenever the SSH chain is gapped (`|v| ≠ |w|`), its
winding number `W = (2πi)⁻¹ ∫₀^{2π} h'(k)/h(k) dk`, with `h(k) = v + w e^{ik}`, is an integer:
it equals `1` in the topological regime `|v| < |w|` and `0` in the trivial regime `|w| < |v|`. -/
