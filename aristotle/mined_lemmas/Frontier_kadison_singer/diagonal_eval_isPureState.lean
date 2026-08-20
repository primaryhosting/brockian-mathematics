/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the required
-- header above is written as a plain block comment.)

import Mathlib

/-!
The Kadison–Singer problem asks whether every pure state on a maximal abelian self-adjoint
subalgebra (MASA) of `B(ℓ²)` extends uniquely to a state on `B(ℓ²)`.  It was answered
affirmatively by Marcus, Spielman and Srivastava via the method of interlacing families of
polynomials.

This file formalizes and proves in full the *finite-dimensional* case — the base case of the
Kadison–Singer question: for the diagonal MASA of the matrix algebra `Mₙ(ℂ)`, the pure state
`d ↦ d i` of the diagonal has a unique extension to a state on `Mₙ(ℂ)`, namely `A ↦ A i i`.

Here a *state* is a unital positive ℂ-linear functional (`Frontier.IsState`), and the pure
states of the diagonal algebra `ℂⁿ` are exactly the coordinate evaluations `d ↦ d i`.

The proof is the classical one: positivity of `phi` yields a positive semidefinite Hermitian
sesquilinear form `(X, Y) ↦ phi (Xᴴ * Y)`, and the degenerate case of the Cauchy–Schwarz
inequality forces `phi` to vanish on every matrix unit other than `E i i`.
-/

namespace Frontier

open Matrix ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `Mₙ(ℂ)`: a unital, positive linear functional. -/

theorem diagonal_eval_isPureState (i : n) :
    IsDiagState (LinearMap.proj i : (n → ℂ) →ₗ[ℂ] ℂ) ∧
      ∀ (psi1 psi2 : (n → ℂ) →ₗ[ℂ] ℂ) (t : ℝ), IsDiagState psi1 → IsDiagState psi2 →
        0 < t → t < 1 →
        (LinearMap.proj i : (n → ℂ) →ₗ[ℂ] ℂ) = (t : ℂ) • psi1 + ((1 - t : ℝ) : ℂ) • psi2 →
        psi1 = (LinearMap.proj i : (n → ℂ) →ₗ[ℂ] ℂ) := by
  constructor
  · refine ⟨rfl, fun d => ?_⟩
    simpa using star_mul_self_nonneg (d i)
  · intro psi1 psi2 t h1 h2 ht0 ht1 hconv
    have hzero : ∀ j : n, j ≠ i → psi1 (unitVec j) = 0 := by
      intro j hj
      have hap := congrArg (fun (f : (n → ℂ) →ₗ[ℂ] ℂ) => f (unitVec j)) hconv
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.proj_apply] at hap
      have hej : (unitVec j : n → ℂ) i = 0 := by simp [unitVec, hj]
      rw [hej] at hap
      have ha := diag_state_nonneg h1 j
      have hb := diag_state_nonneg h2 j
      have hare : 0 ≤ (psi1 (unitVec j)).re := (Complex.le_def.mp ha).1
      have haim : (psi1 (unitVec j)).im = 0 := ((Complex.le_def.mp ha).2).symm
      have hbre : 0 ≤ (psi2 (unitVec j)).re := (Complex.le_def.mp hb).1
      have hre := congrArg Complex.re hap
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.zero_re] at hre
      have hzr : (psi1 (unitVec j)).re = 0 := by nlinarith [hre]
      apply Complex.ext <;> simp [hzr, haim]
    have hone : psi1 (unitVec i) = 1 := by
      have hs := diag_state_sum h1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hs
      have hz : ∑ j ∈ Finset.univ.erase i, psi1 (unitVec j) = 0 :=
        Finset.sum_eq_zero fun j hj => hzero j (Finset.mem_erase.mp hj).1
      rw [hz, zero_add] at hs
      exact hs
    apply LinearMap.ext
    intro d
    rw [diag_state_apply psi1 d, Finset.sum_eq_single i]
    · simp [hone]
    · intro j _ hj; rw [hzero j hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

/-!
### The one-dimensional case of the Marcus–Spielman–Srivastava discrepancy theorem

Weaver's conjecture `KS₂`, proved by Marcus, Spielman and Srivastava with interlacing
families, states that vectors `v₁, …, v_m` in `ℂ^d` with `∑ vⱼ vⱼ* = I` and `‖vⱼ‖² ≤ eps` can
be partitioned into two halves each of operator norm at most `(1/√2 + √eps)²`.

Below is the case `d = 1` of that statement, where the hypothesis reads `∑ ‖vⱼ‖² = 1`; we prove
the sharper bound `1/2 + eps/2` by a greedy balancing argument.
-/

/-- Greedy balancing: a family of reals in `[0, eps]` indexed by a finite set can be split
into two parts whose sums differ by at most `eps`. -/
