import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset SimpleGraph Matrix

/-- The Laplacian of the cycle graph `C n` (`n ≥ 3`) acts on a vector by
`(L v) i = 2 * v i - (v (i-1) + v (i+1))`. -/

theorem cycle_rec_eigenvalue_lower {n : ℕ} [NeZero n] (hn : 3 ≤ n) (μ : ℝ) (v : ZMod n → ℝ)
    (hv : v ≠ 0) (hsum : ∑ i, v i = 0)
    (hrec : ∀ i : ZMod n, 2 * v i - (v (i - 1) + v (i + 1)) = μ * v i) :
    2 - 2 * Real.cos (2 * Real.pi / n) ≤ μ := by
  classical
  set w : ZMod n → ℂ := fun i => ((v i : ℝ) : ℂ) with hw
  have hrecC : ∀ i : ZMod n, 2 * w i - (w (i - 1) + w (i + 1)) = (μ : ℂ) * w i := by
    intro i
    have h := hrec i
    simp only [hw]
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  have hwsum : ∑ i, w i = 0 := by
    simp only [hw]
    rw [← Complex.ofReal_sum, hsum, Complex.ofReal_zero]
  set B := AddChar.complexBasis (ZMod n) with hB
  set c := B.equivFun w with hc
  have hrepr : ∀ i : ZMod n, ∑ ψ : AddChar (ZMod n) ℂ, c ψ * ψ i = w i := by
    intro i
    have h := congrFun (B.sum_equivFun w) i
    simpa [hB, AddChar.coe_complexBasis] using h
  -- every character is an eigenvector of the recurrence
  have hpsi_rec : ∀ (ψ : AddChar (ZMod n) ℂ) (i : ZMod n),
      2 * ψ i - (ψ (i - 1) + ψ (i + 1)) = (2 - ψ 1 - (ψ 1)⁻¹) * ψ i := by
    intro ψ i
    have h1 : ψ (i + 1) = ψ i * ψ 1 := by rw [AddChar.map_add_eq_mul]
    have h2 : ψ (i - 1) = ψ i * (ψ 1)⁻¹ := by
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
    rw [h1, h2]; ring
  -- comparing coefficients in the character basis
  have hcoef : ∀ ψ : AddChar (ZMod n) ℂ, c ψ * (2 - ψ 1 - (ψ 1)⁻¹) = (μ : ℂ) * c ψ := by
    have hzero : ∑ ψ : AddChar (ZMod n) ℂ,
        (c ψ * (2 - ψ 1 - (ψ 1)⁻¹) - (μ : ℂ) * c ψ) • (ψ : ZMod n → ℂ) = 0 := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul]
      rw [Finset.sum_sub_distrib]
      have hA : ∑ ψ : AddChar (ZMod n) ℂ, c ψ * (2 - ψ 1 - (ψ 1)⁻¹) * ψ i
          = 2 * w i - (w (i - 1) + w (i + 1)) := by
        have step : ∀ ψ : AddChar (ZMod n) ℂ, c ψ * (2 - ψ 1 - (ψ 1)⁻¹) * ψ i
            = 2 * (c ψ * ψ i) - ((c ψ * ψ (i - 1)) + (c ψ * ψ (i + 1))) := by
          intro ψ
          have h := hpsi_rec ψ i
          rw [mul_assoc, ← h]; ring
        rw [Finset.sum_congr rfl (fun ψ _ => step ψ), Finset.sum_sub_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum, hrepr i, hrepr (i - 1), hrepr (i + 1)]
      have hBb : ∑ ψ : AddChar (ZMod n) ℂ, (μ : ℂ) * c ψ * ψ i = (μ : ℂ) * w i := by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, hrepr i]
      rw [hA, hBb, hrecC i, sub_self]
    intro ψ
    have h := Fintype.linearIndependent_iff.mp (AddChar.linearIndependent (ZMod n) ℂ) _ hzero ψ
    linear_combination h
  -- the trivial character does not occur, since `v` has zero sum
  have hc0 : c 0 = 0 := by
    have h1 : ∑ i : ZMod n, w i
        = ∑ ψ : AddChar (ZMod n) ℂ, c ψ * (∑ i : ZMod n, ψ i) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact (Finset.sum_congr rfl (fun i _ => hrepr i)).symm
    have h2 : ∀ ψ : AddChar (ZMod n) ℂ, (∑ i : ZMod n, ψ i)
        = if ψ = 0 then (Fintype.card (ZMod n) : ℂ) else 0 := fun ψ => AddChar.sum_eq_ite ψ
    rw [h1] at hwsum
    simp_rw [h2, mul_ite, mul_zero,
      Finset.sum_ite_eq' Finset.univ (0 : AddChar (ZMod n) ℂ)] at hwsum
    simp only [Finset.mem_univ, if_true, mul_eq_zero, Nat.cast_eq_zero] at hwsum
    rcases hwsum with h | h
    · exact h
    · exact absurd h (by simp [ZMod.card, NeZero.ne n])
  -- some character occurs with a nonzero coefficient
  have hwne : w ≠ 0 := by
    intro h
    exact hv (funext fun i => by
      have := congrFun h i
      simp only [hw, Pi.zero_apply, Complex.ofReal_eq_zero] at this
      simpa using this)
  obtain ⟨ψ, hcpsi⟩ : ∃ ψ : AddChar (ZMod n) ℂ, c ψ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hwne (funext fun i => by
      rw [← hrepr i]
      simp [hcon])
  have hpsine : ψ ≠ 0 := by
    intro h
    exact hcpsi (h ▸ hc0)
  set z : ℂ := ψ 1 with hzdef
  have hzpow : z ^ n = 1 := by
    rw [hzdef, ← AddChar.map_nsmul_eq_pow]
    simp [nsmul_eq_mul]
  have hz1 : z ≠ 1 := by
    intro h
    refine hpsine ?_
    ext i
    have hi : (i.val) • (1 : ZMod n) = i := by simp [nsmul_eq_mul]
    calc ψ i = ψ ((i.val) • (1 : ZMod n)) := by rw [hi]
      _ = (ψ 1) ^ i.val := AddChar.map_nsmul_eq_pow ψ _ _
      _ = 1 := by rw [← hzdef, h, one_pow]
  have hznorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hzpow (by omega)
  have hmu : (μ : ℂ) = 2 - ((2 * z.re : ℝ) : ℂ) := by
    have h2 : (2 - z - z⁻¹) = (μ : ℂ) :=
      mul_left_cancel₀ hcpsi (by linear_combination hcoef ψ)
    rw [← h2, Complex.inv_eq_conj hznorm, ← Complex.add_conj z]
    ring
  have hmure : μ = 2 - 2 * z.re := by
    have := congrArg Complex.re hmu
    simpa using this
  have hle : z.re ≤ Real.cos (2 * Real.pi / n) := root_of_unity_re_le hn hzpow hz1
  rw [hmure]
  linarith

/-- `2 - 2 cos (2π/n)` really is an eigenvalue, with a zero-sum eigenvector. -/
