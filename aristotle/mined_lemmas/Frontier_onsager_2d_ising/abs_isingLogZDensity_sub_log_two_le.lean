import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## The 2D Ising model on a periodic `m × n` lattice (a torus) -/

/-- Real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/

theorem abs_isingLogZDensity_sub_log_two_le (m n : ℕ) [NeZero m] [NeZero n] (J β : ℝ) :
    |isingLogZDensity m n J β - Real.log 2| ≤ 2 * |β| * |J| := by
  set C : ℝ := 2 * ((m : ℝ) * n) * |J| * |β| with hC
  have hcard : (Finset.univ : Finset (ZMod m × ZMod n → Bool)).card = 2 ^ (m * n) := by
    simp [Finset.card_univ, ZMod.card]
  have hterm : ∀ σ : ZMod m × ZMod n → Bool,
      Real.exp (-C) ≤ Real.exp (-β * isingEnergy m n J σ) ∧
      Real.exp (-β * isingEnergy m n J σ) ≤ Real.exp C := by
    intro σ
    have h1 : |(-β) * isingEnergy m n J σ| ≤ C := by
      rw [abs_mul, abs_neg, hC]
      calc |β| * |isingEnergy m n J σ| ≤ |β| * (2 * ((m : ℝ) * n) * |J|) :=
            mul_le_mul_of_nonneg_left (abs_isingEnergy_le m n J σ) (abs_nonneg β)
        _ = 2 * ((m : ℝ) * n) * |J| * |β| := by ring
    have h2 := abs_le.mp h1
    exact ⟨Real.exp_le_exp.mpr h2.1, Real.exp_le_exp.mpr h2.2⟩
  have hub : isingZ m n J β ≤ 2 ^ (m * n) * Real.exp C := by
    rw [isingZ]
    calc ∑ σ : ZMod m × ZMod n → Bool, Real.exp (-β * isingEnergy m n J σ)
        ≤ ∑ _σ : ZMod m × ZMod n → Bool, Real.exp C :=
          Finset.sum_le_sum (fun σ _ => (hterm σ).2)
      _ = 2 ^ (m * n) * Real.exp C := by rw [Finset.sum_const, hcard]; simp [nsmul_eq_mul]
  have hlb : (2 : ℝ) ^ (m * n) * Real.exp (-C) ≤ isingZ m n J β := by
    rw [isingZ]
    calc (2 : ℝ) ^ (m * n) * Real.exp (-C)
        = ∑ _σ : ZMod m × ZMod n → Bool, Real.exp (-C) := by
          rw [Finset.sum_const, hcard]; simp [nsmul_eq_mul]
      _ ≤ ∑ σ : ZMod m × ZMod n → Bool, Real.exp (-β * isingEnergy m n J σ) :=
          Finset.sum_le_sum (fun σ _ => (hterm σ).1)
  have hpos : 0 < isingZ m n J β := lt_of_lt_of_le (by positivity) hlb
  have hlogub : Real.log (isingZ m n J β) ≤ ((m * n : ℕ) : ℝ) * Real.log 2 + C := by
    have h := Real.log_le_log hpos hub
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at h
    exact_mod_cast h
  have hloglb : ((m * n : ℕ) : ℝ) * Real.log 2 - C ≤ Real.log (isingZ m n J β) := by
    have h := Real.log_le_log (by positivity) hlb
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at h
    push_cast at h ⊢
    linarith
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hmn : (0 : ℝ) < (m : ℝ) * n := mul_pos hm hn
  push_cast at hlogub hloglb
  have hinv : (0 : ℝ) ≤ 1 / ((m : ℝ) * n) := by positivity
  have e1 := mul_le_mul_of_nonneg_left hloglb hinv
  have e2 := mul_le_mul_of_nonneg_left hlogub hinv
  have hxa : 1 / ((m : ℝ) * n) * (((m : ℝ) * n) * Real.log 2) = Real.log 2 := by
    field_simp
  have hCval : 1 / ((m : ℝ) * n) * C = 2 * |β| * |J| := by
    rw [hC]; field_simp
  rw [mul_sub, hxa] at e1
  rw [mul_add, hxa] at e2
  rw [isingLogZDensity, abs_le]
  constructor <;> linarith

/-- Onsager's expression at infinite temperature. -/
