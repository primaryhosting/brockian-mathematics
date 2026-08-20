/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

variable {n : ℕ}

/-- The standard symplectic vector space `ℝ^(2n+2)`, realised as the Euclidean space with
index set `Fin (n+1) ⊕ Fin (n+1)`: the `Sum.inl` coordinates are the positions `q₀,…,qₙ`
and the `Sum.inr` coordinates are the conjugate momenta `p₀,…,pₙ`. -/
abbrev SymplecticSpace (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1) ⊕ Fin (n + 1))

/-- The standard symplectic form `ω(x, y) = ∑ᵢ (x_{qᵢ} y_{pᵢ} - x_{pᵢ} y_{qᵢ})`. -/

lemma norm_le_of_omegaForm_bound {r R : ℝ} (hr : 0 < r) (p : SymplecticSpace n)
    (h : ∀ z : SymplecticSpace n, ‖z‖ < r → |omegaForm z p| < R) : r * ‖p‖ ≤ R := by
  have hR : 0 < R := by
    have := h 0 (by simpa using hr)
    simpa [omegaForm] using this
  rcases eq_or_ne p 0 with rfl | hp
  · simp
    positivity
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  by_contra hcon
  push_neg at hcon
  have h1 : R / ‖p‖ < r := by rw [div_lt_iff₀ hpn]; linarith
  set t := (R / ‖p‖ + r) / 2 with ht
  have hRp : 0 < R / ‖p‖ := by positivity
  have ht1 : t < r := by rw [ht]; linarith
  have ht0 : 0 < t := by rw [ht]; linarith
  have htR : R / ‖p‖ < t := by rw [ht]; linarith
  set z : SymplecticSpace n := (t / ‖p‖) • Jmap p with hz
  have hzn : ‖z‖ = t := by
    rw [hz, norm_smul, norm_Jmap, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hval : omegaForm z p = t * ‖p‖ := by
    rw [omegaForm_eq_inner, hz, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_Jmap]
    field_simp
  have hlt := h z (by rw [hzn]; exact ht1)
  rw [hval, abs_of_pos (by positivity)] at hlt
  have := (div_lt_iff₀ hpn).mp htR
  linarith

