import Mathlib

/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
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

namespace QI

/-- The Hilbert space of a quantum query algorithm searching a database of `N` items:
the index register `Fin N` together with an arbitrary workspace register `K`. -/
abbrev HSpace (N : ℕ) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  PiLp 2 (fun _ : Fin N => K)

variable {N : ℕ} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The (phase) query operator for the database whose unique marked item is `x`:
it flips the sign of the component of the index register at `x`. -/

theorem grover_optimal (T : ℕ) (U : ℕ → (HSpace N K ≃ₗᵢ[ℂ] HSpace N K)) (psi0 : HSpace N K)
    (hpsi0 : ‖psi0‖ = 1)
    (hsucc : ∀ x : Fin N, (2 : ℝ) / 3 ≤ ‖(run U (phaseOracle x) psi0 T) x‖ ^ 2) :
    (Real.sqrt (2 * N / 3) - 1) / 2 ≤ (T : ℝ) := by
  set g := run U id psi0 with hg
  set f := fun x : Fin N => run U (phaseOracle x) psi0 with hfdef
  -- Upper bound on the total distinguishability.
  have hupper : ∑ x : Fin N, ‖f x T - g T‖ ≤ 2 * T * Real.sqrt N := by
    have step1 : ∑ x : Fin N, ‖f x T - g T‖
        ≤ ∑ x : Fin N, 2 * ∑ s ∈ Finset.range T, ‖(g s) x‖ :=
      Finset.sum_le_sum fun x _ => hybrid_bound U psi0 x T
    have step2 : ∑ x : Fin N, 2 * ∑ s ∈ Finset.range T, ‖(g s) x‖
        = 2 * ∑ s ∈ Finset.range T, ∑ x : Fin N, ‖(g s) x‖ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    have step3 : ∑ s ∈ Finset.range T, ∑ x : Fin N, ‖(g s) x‖ ≤ T * Real.sqrt N := by
      have : ∀ s ∈ Finset.range T, ∑ x : Fin N, ‖(g s) x‖ ≤ Real.sqrt N := by
        intro s _
        have := sum_norm_apply_le (g s)
        rwa [hg, norm_run_id U psi0 s, hpsi0, mul_one] at this
      calc ∑ s ∈ Finset.range T, ∑ x : Fin N, ‖(g s) x‖
          ≤ ∑ _s ∈ Finset.range T, Real.sqrt N := Finset.sum_le_sum this
        _ = T * Real.sqrt N := by simp
    linarith [step1, step2 ▸ step1, step3]
  -- Lower bound on the total distinguishability.
  have hlower : (N : ℝ) * Real.sqrt (2 / 3) - Real.sqrt N ≤ ∑ x : Fin N, ‖f x T - g T‖ := by
    have hpt : ∀ x : Fin N, Real.sqrt (2 / 3) - ‖(g T) x‖ ≤ ‖f x T - g T‖ := by
      intro x
      have hs : Real.sqrt (2 / 3) ≤ ‖(f x T) x‖ := by
        have := Real.sqrt_le_sqrt (hsucc x)
        rwa [Real.sqrt_sq (norm_nonneg _)] at this
      have hcomp : ‖(f x T) x - (g T) x‖ ≤ ‖f x T - g T‖ := by
        have := PiLp.norm_apply_le (f x T - g T) x
        simpa using this
      have := norm_sub_norm_le ((f x T) x) ((g T) x)
      linarith
    calc (N : ℝ) * Real.sqrt (2 / 3) - Real.sqrt N
        ≤ ∑ x : Fin N, (Real.sqrt (2 / 3) - ‖(g T) x‖) := by
          have hsum : ∑ x : Fin N, (Real.sqrt (2 / 3) - ‖(g T) x‖)
              = (N : ℝ) * Real.sqrt (2 / 3) - ∑ x : Fin N, ‖(g T) x‖ := by
            rw [Finset.sum_sub_distrib]
            simp
          have hle : ∑ x : Fin N, ‖(g T) x‖ ≤ Real.sqrt N := by
            have := sum_norm_apply_le (g T)
            rwa [hg, norm_run_id U psi0 T, hpsi0, mul_one] at this
          rw [hsum]; linarith
      _ ≤ ∑ x : Fin N, ‖f x T - g T‖ := Finset.sum_le_sum fun x _ => hpt x
  -- Combine.
  have hcomb : (N : ℝ) * Real.sqrt (2 / 3) - Real.sqrt N ≤ 2 * T * Real.sqrt N :=
    le_trans hlower hupper
  have hsN : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hprod : Real.sqrt (2 * N / 3) = Real.sqrt N * Real.sqrt (2 / 3) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg N)]
    ring_nf
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.sqrt_zero]
    have : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    linarith
  · have hpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    rw [hprod]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    have hkey : Real.sqrt N * (Real.sqrt N * Real.sqrt (2 / 3)) - Real.sqrt N
        ≤ Real.sqrt N * (2 * T) := by
      have : (N : ℝ) * Real.sqrt (2 / 3) = Real.sqrt N * (Real.sqrt N * Real.sqrt (2 / 3)) := by
        rw [← mul_assoc, ← sq, hsN]
      linarith [hcomb, this]
    have := le_of_mul_le_mul_left
      (by linarith [hkey] :
        Real.sqrt N * (Real.sqrt N * Real.sqrt (2 / 3) - 1) ≤ Real.sqrt N * (2 * T)) hpos
    linarith [this]

/-- A convenient `Ω(√N)` form of the BBBV bound: any bounded-error quantum search algorithm
for a database of `N` items uses `T ≥ √N / 3 - 1` queries. -/
