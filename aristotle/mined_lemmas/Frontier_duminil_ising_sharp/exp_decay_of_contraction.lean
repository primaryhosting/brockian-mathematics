import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

/-- Exponential decay from a strict contraction over a fixed scale `L`:
if `0 ≤ a n ≤ 1` and `a (n + L) ≤ c * a n` with `0 < c < 1`, then `a` decays exponentially. -/

theorem exp_decay_of_contraction {a : ℕ → ℝ} (hle : ∀ n : ℕ, a n ≤ 1)
    {L : ℕ} (hL : 0 < L) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hstep : ∀ n : ℕ, a (n + L) ≤ c * a n) :
    ∃ C > 0, ∃ γ > 0, ∀ n : ℕ, a n ≤ C * Real.exp (-γ * n) := by
  have key : ∀ k r : ℕ, a (k * L + r) ≤ c ^ k * a r := by
    intro k
    induction k with
    | zero => intro r; simp
    | succ k ih =>
      intro r
      have h1 : (k + 1) * L + r = (k * L + r) + L := by ring
      rw [h1]
      calc a ((k * L + r) + L) ≤ c * a (k * L + r) := hstep _
        _ ≤ c * (c ^ k * a r) := mul_le_mul_of_nonneg_left (ih r) hc0.le
        _ = c ^ (k + 1) * a r := by ring
  have hlogc : Real.log c < 0 := Real.log_neg hc0 hc1
  have hLpos : (0:ℝ) < L := by exact_mod_cast hL
  refine ⟨c⁻¹, by positivity, (-Real.log c) / L, div_pos (by linarith) hLpos, ?_⟩
  intro n
  have hnL : n = (n / L) * L + n % L := (Nat.div_add_mod' n L).symm
  have h1 : a n ≤ c ^ (n / L) := by
    calc a n = a ((n / L) * L + n % L) := by rw [← hnL]
      _ ≤ c ^ (n / L) * a (n % L) := key _ _
      _ ≤ c ^ (n / L) * 1 := mul_le_mul_of_nonneg_left (hle _) (by positivity)
      _ = c ^ (n / L) := by ring
  have hkr : ((n:ℝ) / L) - 1 ≤ ((n / L : ℕ) : ℝ) := by
    have hmod : n % L < L := Nat.mod_lt _ hL
    have h2 : (n : ℝ) < ((n / L : ℕ) : ℝ) * L + L := by
      have hn : n < (n / L) * L + L := by omega
      exact_mod_cast hn
    rw [sub_le_iff_le_add, div_le_iff₀ hLpos]
    nlinarith
  have h2 : (c : ℝ) ^ ((n / L : ℕ) : ℝ) ≤ c ^ (((n:ℝ) / L) - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hc0 hc1.le hkr
  rw [Real.rpow_natCast] at h2
  have hexp : -((-Real.log c) / L) * (n : ℝ) = Real.log c * ((n : ℝ) / L) := by
    field_simp
  have h4 : (c : ℝ) ^ (((n:ℝ) / L) - 1) = c⁻¹ * Real.exp (-((-Real.log c) / L) * n) := by
    rw [Real.rpow_sub hc0, Real.rpow_one, Real.rpow_def_of_pos hc0, hexp]
    ring
  calc a n ≤ c ^ (n / L) := h1
    _ ≤ (c : ℝ) ^ (((n:ℝ) / L) - 1) := h2
    _ = c⁻¹ * Real.exp (-((-Real.log c) / L) * n) := h4

/-- Grönwall-type lower bound: from the differential inequality `m' ≥ c₀ (1 - m)` above `b`
and `m b ≥ 0` one gets `m β ≥ 1 - exp (-c₀ (β - b))`. -/
