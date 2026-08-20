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

theorem sandwich_eq_zero (P A : Matrix (Fin n) (Fin n) ℂ) (hP : P * P = P)
    (hA : A = P * A + A * P) : P * A * P = 0 := by
  have h : P * A * P = P * A * P + P * A * P := by
    conv_lhs => rw [hA]
    rw [mul_add, add_mul, ← mul_assoc, hP, ← mul_assoc P A P, mul_assoc (P * A) P P, hP]
  have h' : P * A * P + 0 = P * A * P + P * A * P := by simpa using h
  exact (add_left_cancel h').symm

/-- Algebraic interband decomposition: for an idempotent `P` and derivatives `A`, `B`
satisfying the differentiated idempotency relations, the commutator term of the Berry
curvature only involves interband matrix elements `P · (1 - P)`. -/
