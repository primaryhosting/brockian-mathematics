import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Phys

/-- `psi` is a (twice differentiable) solution of the time-independent one-dimensional
Schrödinger equation with potential `V` and energy `E`, in units where `ħ² / 2m = 1`:
`-ψ'' + V ψ = E ψ`, i.e. `ψ'' = (V - E) ψ`. -/
structure IsSchrodingerSolution (V : ℝ → ℂ) (E : ℂ) (psi : ℝ → ℂ) : Prop where
  differentiable : Differentiable ℝ psi
  differentiable_deriv : Differentiable ℝ (deriv psi)
  eqn : ∀ x : ℝ, deriv (deriv psi) x = (V x - E) * psi x

/-- If the potential is `a`-periodic, then translating a solution of the Schrödinger equation
by `a` gives again a solution with the same energy. -/

theorem const_of_deriv_deriv_eq_zero {phi : ℝ → ℂ} (h1 : Differentiable ℝ phi)
    (h2 : Differentiable ℝ (deriv phi)) (h3 : ∀ x, deriv (deriv phi) x = 0)
    {N : ℝ} (hb : ∀ x, ‖phi x‖ ≤ N) : ∀ x, phi x = phi 0 := by
  set c : ℂ := deriv phi 0 with hc
  have hderiv : ∀ x, deriv phi x = c := fun x => is_const_of_deriv_eq_zero h2 h3 x 0
  -- `phi x - c * x` has vanishing derivative, hence is constant
  have hofReal : ∀ x : ℝ, HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 x := by
    intro x
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have hg : ∀ x : ℝ, HasDerivAt (fun t : ℝ => phi t - c * (t : ℂ)) 0 x := by
    intro x
    have hp : HasDerivAt phi c x := by
      have := (h1 x).hasDerivAt
      rwa [hderiv x] at this
    have hl : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
      simpa using (hofReal x).const_mul c
    simpa using hp.sub hl
  have hgc : ∀ x : ℝ, phi x - c * (x : ℂ) = phi 0 - c * ((0 : ℝ) : ℂ) :=
    fun x => is_const_of_deriv_eq_zero (fun y => (hg y).differentiableAt)
      (fun y => (hg y).deriv) x 0
  have haffine : ∀ x : ℝ, phi x = phi 0 + c * (x : ℂ) := by
    intro x
    have := hgc x
    simp only [Complex.ofReal_zero, mul_zero, sub_zero] at this
    linear_combination this
  -- boundedness forces the slope `c` to vanish
  have hN : 0 ≤ N := le_trans (norm_nonneg _) (hb 0)
  have hc0 : c = 0 := by
    by_contra hcne
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
    set t : ℝ := (2 * N + 1) / ‖c‖ with ht
    have htnn : 0 ≤ t := by positivity
    have h1' : ‖c * (t : ℂ)‖ = 2 * N + 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htnn, ht]
      field_simp
    have h2' : ‖c * (t : ℂ)‖ ≤ 2 * N := by
      have : c * (t : ℂ) = phi t - phi 0 := by
        rw [haffine t]; ring
      rw [this]
      calc ‖phi t - phi 0‖ ≤ ‖phi t‖ + ‖phi 0‖ := norm_sub_le _ _
        _ ≤ N + N := add_le_add (hb t) (hb 0)
        _ = 2 * N := by ring
    linarith
  intro x
  rw [haffine x, hc0]
  ring

/-- The hypotheses of `bloch_theorem` are consistent: they hold for the free particle at zero
energy with the constant eigenstate, on any lattice of period `a = 1`. -/
