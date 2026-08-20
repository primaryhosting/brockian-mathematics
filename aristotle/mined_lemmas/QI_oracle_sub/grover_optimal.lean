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

namespace QI

variable {N M : ℕ}

/-- The state space of a quantum query algorithm searching a database of size `N`:
an index register `Fin N` together with an arbitrary finite workspace `Fin M`. -/
abbrev State (N M : ℕ) : Type := EuclideanSpace ℂ (Fin N × Fin M)

/-- The standard phase oracle marking the index `i`: it flips the sign of every
amplitude whose index register holds `i`, and does nothing otherwise. -/

theorem grover_optimal {N M T : ℕ} (U : ℕ → (State N M ≃ₗᵢ[ℂ] State N M))
    (psi0 : State N M) (hpsi0 : ‖psi0‖ = 1) (c : ℝ) (hc : 0 ≤ c)
    (hdist : ∀ i : Fin N, c ≤ ‖run U psi0 (oracle i) T - run U psi0 id T‖) :
    c / 2 * √N ≤ T := by
  set psi : ℕ → State N M := fun t => run U psi0 id t with hpsi
  set d : Fin N → ℕ → ℝ := fun i t => ‖oracle i (psi t) - psi t‖ with hd
  -- Step 1: each marked item is reached only through a large total disturbance.
  have step1 : ∀ i : Fin N, c ≤ ∑ t ∈ Finset.range T, d i t := fun i =>
    le_trans (hdist i) (hybrid U psi0 i T)
  -- Step 2: at each step the total disturbance over all indices is exactly `4`.
  have step2 : ∀ t : ℕ, ∑ i : Fin N, (d i t) ^ 2 = 4 := by
    intro t
    have : ∑ i : Fin N, (d i t) ^ 2 = 4 * ∑ i : Fin N, markSq i (psi t) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => norm_oracle_sub_self_sq i (psi t)
    rw [this, sum_markSq, hpsi, norm_run_id, hpsi0]
    norm_num
  -- Step 3: Cauchy-Schwarz plus the counting bound.
  have step3 : (N : ℝ) * c ^ 2 ≤ 4 * (T : ℝ) ^ 2 := by
    have h1 : (N : ℝ) * c ^ 2 ≤ ∑ i : Fin N, (∑ t ∈ Finset.range T, d i t) ^ 2 := by
      have : ∀ i : Fin N, c ^ 2 ≤ (∑ t ∈ Finset.range T, d i t) ^ 2 := fun i =>
        pow_le_pow_left₀ hc (step1 i) 2
      calc (N : ℝ) * c ^ 2 = ∑ _i : Fin N, c ^ 2 := by
            simp [Finset.sum_const]
        _ ≤ ∑ i : Fin N, (∑ t ∈ Finset.range T, d i t) ^ 2 :=
            Finset.sum_le_sum fun i _ => this i

    have h2 : ∀ i : Fin N, (∑ t ∈ Finset.range T, d i t) ^ 2
        ≤ (T : ℝ) * ∑ t ∈ Finset.range T, (d i t) ^ 2 := by
      intro i
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range T) (f := fun t => d i t)
    have h3 : ∑ i : Fin N, (∑ t ∈ Finset.range T, d i t) ^ 2
        ≤ ∑ i : Fin N, (T : ℝ) * ∑ t ∈ Finset.range T, (d i t) ^ 2 :=
      Finset.sum_le_sum fun i _ => h2 i
    have h4 : ∑ i : Fin N, (T : ℝ) * ∑ t ∈ Finset.range T, (d i t) ^ 2
        = (T : ℝ) * ∑ t ∈ Finset.range T, ∑ i : Fin N, (d i t) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    have h5 : ∑ t ∈ Finset.range T, ∑ i : Fin N, (d i t) ^ 2 = 4 * (T : ℝ) := by
      rw [Finset.sum_congr rfl fun t _ => step2 t]
      simp [mul_comm]
    calc (N : ℝ) * c ^ 2
        ≤ ∑ i : Fin N, (∑ t ∈ Finset.range T, d i t) ^ 2 := h1
      _ ≤ ∑ i : Fin N, (T : ℝ) * ∑ t ∈ Finset.range T, (d i t) ^ 2 := h3
      _ = (T : ℝ) * ∑ t ∈ Finset.range T, ∑ i : Fin N, (d i t) ^ 2 := h4
      _ = (T : ℝ) * (4 * (T : ℝ)) := by rw [h5]
      _ = 4 * (T : ℝ) ^ 2 := by ring
  -- Step 4: conclude.
  have hsq : (√N) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hs0 : (0 : ℝ) ≤ √N := Real.sqrt_nonneg _
  have hT : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  nlinarith [step3, hsq, hs0, hT, hc, sq_nonneg (c * √N - 2 * T)]

/-- Specialisation: an algorithm whose final states for the marked databases are at
distance at least `1` from the final state for the unmarked database must make at least
`√N / 2` queries. -/
