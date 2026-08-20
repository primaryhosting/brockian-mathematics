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

set_option grind.warning false

/-!
# TKNN: the integer quantum Hall conductance is a Chern number times `e² / h`

This file formalises the Thouless–Kohmoto–Nightingale–den Nijs (TKNN) statement in the
standard Bloch-bundle setting, in the gauge-invariant *spectral projector* formulation.

## Setting

A two-dimensional Bloch Hamiltonian gives, for each quasi-momentum `k = (k₁, k₂)` in the
Brillouin torus `[0, 2π]²`, the spectral projector `P k` onto the occupied bands.  Here `P`
is a matrix-valued function on the Brillouin zone,
`P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ`, which for a physical band structure satisfies
`(P k)ᴴ = P k` and `P k * P k = P k`.

* `Frontier.momDeriv₁`, `Frontier.momDeriv₂` are the entrywise partial derivatives of `P`
  with respect to `k₁` and `k₂`.
* `Frontier.berryCurvature P k = i · tr (P k · [∂₁P k, ∂₂P k])` is the (non-abelian) Berry
  curvature of the occupied bundle; it is a real number (`berryCurvature_isReal`).
* `Frontier.chernNumber P = (1 / 2π) ∫_{[0,2π]²} berryCurvature P` is the first Chern number
  of the occupied Bloch bundle.
* `Frontier.hallConductance e ħ P = (e² / ħ) · (2π)⁻² ∫_{[0,2π]²} berryCurvature P` is the
  Kubo linear-response formula for the transverse (Hall) conductance of the filled bands.
* `Frontier.planckOfReduced ħ = 2π ħ` is Planck's constant `h` in terms of `ħ`.

## Main results

* `Frontier.tknn_chern_hall` : `hallConductance e ħ P = chernNumber P * (e² / h)`, i.e. the
  Hall conductance equals the Chern number times the conductance quantum `e²/h`.
* `Frontier.tknn_chern_hall_integer` : the quantised form — if the Chern number is the
  integer `C`, then the Hall conductance is `C · e²/h`.
* `Frontier.berryCurvature_isReal` : the Berry curvature is real.
* `Frontier.berryCurvature_interband` : only interband matrix elements contribute,
  `Ω = i tr (P ∂₁P (1-P) ∂₂P - P ∂₂P (1-P) ∂₁P)` — the Kubo linear-response integrand.
* Base cases: for a band projector that is constant along one momentum direction (in
  particular for a `k`-independent one) the Berry curvature, the Chern number and the Hall
  conductance all vanish.

The topological quantisation itself — that `chernNumber P` is an integer for a smooth family
of projectors over the Brillouin torus — is *not* proved here; it enters
`tknn_chern_hall_integer` as the hypothesis `chernNumber P = C`.
-/

namespace Frontier

open Matrix

variable {n : ℕ}

/-- Planck's constant `h = 2π ħ` expressed through the reduced Planck constant `ħ`. -/

theorem momDeriv₂_idem (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) (k : ℝ × ℝ)
    (hidem : ∀ k, P k * P k = P k)
    (hdiff : ∀ i j, DifferentiableAt ℝ (fun t : ℝ => P (k.1, t) i j) k.2) :
    momDeriv₂ P k = P k * momDeriv₂ P k + momDeriv₂ P k * P k := by
  ext i j
  have hfun : (fun t : ℝ => P (k.1, t) i j)
      = fun t : ℝ => ∑ l, P (k.1, t) i l * P (k.1, t) l j := by
    funext t
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) (hidem (k.1, t))
    simpa [Matrix.mul_apply] using this.symm
  have hderiv : HasDerivAt (fun t : ℝ => ∑ l, P (k.1, t) i l * P (k.1, t) l j)
      (∑ l, (deriv (fun t : ℝ => P (k.1, t) i l) k.2 * P k l j
              + P k i l * deriv (fun t : ℝ => P (k.1, t) l j) k.2)) k.2 := by
    refine HasDerivAt.fun_sum fun l _ => ?_
    exact (hdiff i l).hasDerivAt.fun_mul (hdiff l j).hasDerivAt
  have hd : deriv (fun t : ℝ => P (k.1, t) i j) k.2
      = ∑ l, (deriv (fun t : ℝ => P (k.1, t) i l) k.2 * P k l j
              + P k i l * deriv (fun t : ℝ => P (k.1, t) l j) k.2) := by
    rw [hfun]; exact hderiv.deriv
  simp only [momDeriv₂, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [hd, Finset.sum_add_distrib, add_comm]

/-- **Interband (Kubo) form of the Berry curvature.**  For a differentiable family of band
projectors, the Berry curvature is given purely by interband matrix elements,
`Ω = i tr (P ∂₁P (1-P) ∂₂P - P ∂₂P (1-P) ∂₁P)`, which is the Kubo linear-response
integrand. -/
