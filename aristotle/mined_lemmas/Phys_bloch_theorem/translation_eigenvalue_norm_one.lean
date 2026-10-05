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

theorem translation_eigenvalue_norm_one {psi : ℝ → ℂ} {a : ℝ} {lam : ℂ} {M : ℝ} {x₀ : ℝ}
    (hlam : ∀ x, psi (x + a) = lam * psi x) (hbdd : ∀ x, ‖psi x‖ ≤ M)
    (hne : psi x₀ ≠ 0) : ‖lam‖ = 1 := by
  -- forward iteration of the translation
  have hfwd : ∀ n : ℕ, psi (x₀ + n * a) = lam ^ n * psi x₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep : psi (x₀ + (n : ℝ) * a + a) = lam * psi (x₀ + (n : ℝ) * a) :=
          hlam (x₀ + (n : ℝ) * a)
        have hx : x₀ + ((n : ℕ) + 1 : ℕ) * a = x₀ + (n : ℝ) * a + a := by
          push_cast; ring
        rw [hx, hstep, ih]
        ring
  -- backward iteration of the translation
  have hbwd : ∀ n : ℕ, psi x₀ = lam ^ n * psi (x₀ - n * a) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep :
            psi (x₀ - ((n : ℕ) + 1 : ℕ) * a + a) = lam * psi (x₀ - ((n : ℕ) + 1 : ℕ) * a) :=
          hlam _
        have hx : x₀ - ((n : ℕ) + 1 : ℕ) * a + a = x₀ - (n : ℝ) * a := by
          push_cast; ring
        rw [hx] at hstep
        rw [ih, hstep]
        push_cast
        ring
  have hpos : 0 < ‖psi x₀‖ := norm_pos_iff.mpr hne
  -- `‖lam‖ ≤ 1`, else `psi` blows up as `x → +∞`
  have hle : ‖lam‖ ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖psi x₀‖) hgt
    have h1 : ‖lam‖ ^ n * ‖psi x₀‖ ≤ M := by
      have := hbdd (x₀ + n * a)
      rwa [hfwd n, norm_mul, norm_pow] at this
    have h2 : M / ‖psi x₀‖ * ‖psi x₀‖ < ‖lam‖ ^ n * ‖psi x₀‖ := mul_lt_mul_of_pos_right hn hpos
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h2
    linarith
  -- `1 ≤ ‖lam‖`, else `psi` blows up as `x → -∞`
  have hge : 1 ≤ ‖lam‖ := by
    by_contra hlt
    push_neg at hlt
    have hnn : 0 ≤ ‖lam‖ := norm_nonneg _
    have htend : Filter.Tendsto (fun n : ℕ => ‖lam‖ ^ n * M) Filter.atTop (nhds (0 * M)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hnn hlt).mul_const M
    rw [zero_mul] at htend
    have hbound : ∀ n : ℕ, ‖psi x₀‖ ≤ ‖lam‖ ^ n * M := by
      intro n
      have h1 : ‖psi x₀‖ = ‖lam‖ ^ n * ‖psi (x₀ - n * a)‖ := by
        rw [hbwd n, norm_mul, norm_pow]
      rw [h1]
      exact mul_le_mul_of_nonneg_left (hbdd _) (pow_nonneg hnn n)
    have : ‖psi x₀‖ ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds htend hbound
    linarith
  linarith

/-- **Bloch form.** If `psi` is an eigenvector of the translation-by-`a` operator with an
eigenvalue of modulus one, then `psi x = e^{i k x} * u x` with `u` an `a`-periodic function. -/
