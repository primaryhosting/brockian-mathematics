/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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

namespace Frontier

open Complex Filter

/-!
## Elementary complex-analytic estimates
-/

/-- Geometric bound: `|1 - r ^ n| ≤ n |1 - r| max(1,r) ^ n` for real `r ≥ 0`. -/

theorem simultaneous_recurrence (s : Finset ℕ) (w : ℕ → ℂ) (hw : ∀ k ∈ s, ‖w k‖ = 1)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) : ∃ n, N ≤ n ∧ 1 ≤ n ∧ ∀ k ∈ s, ‖w k ^ n - 1‖ ≤ ε := by
  have key : ∀ δ : ℝ, 0 < δ → ∃ p, 1 ≤ p ∧ ∀ k ∈ s, ‖w k ^ p - 1‖ ≤ δ := by
    intro δ hδ
    set X : ℕ → (∀ i : {k // k ∈ s}, ℂ) := fun n i => (w i.1) ^ n with hX
    have hmem : ∀ n, X n ∈ Metric.closedBall (0 : ∀ i : {k // k ∈ s}, ℂ) 1 := by
      intro n
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
      rw [hX]
      simp only [norm_pow]
      rw [hw i.1 i.2, one_pow]
    obtain ⟨a, -, psi, hpsi, hlim⟩ :=
      (isCompact_closedBall (0 : ∀ i : {k // k ∈ s}, ℂ) 1).tendsto_subseq hmem
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨M, hM⟩ := hlim (δ / 2) (by linarith)
    have h1 := hM M le_rfl
    have h2 := hM (M + 1) (by omega)
    have hlt : psi M < psi (M + 1) := hpsi (Nat.lt_succ_self M)
    have hd : dist (X (psi M)) (X (psi (M + 1))) < δ := by
      calc dist (X (psi M)) (X (psi (M + 1))) ≤ dist (X (psi M)) a + dist a (X (psi (M + 1))) :=
            dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := by rw [dist_comm a]; exact add_lt_add h1 h2
      _ = δ := by ring
    refine ⟨psi (M + 1) - psi M, by omega, fun k hk => ?_⟩
    have hcoord : dist ((X (psi M)) ⟨k, hk⟩) ((X (psi (M + 1))) ⟨k, hk⟩)
        ≤ dist (X (psi M)) (X (psi (M + 1))) := dist_le_pi_dist _ _ _
    have heq : ‖w k ^ (psi M) - w k ^ (psi (M + 1))‖ = ‖w k ^ (psi (M + 1) - psi M) - 1‖ := by
      have e1 : w k ^ (psi (M + 1)) = w k ^ (psi M) * w k ^ (psi (M + 1) - psi M) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [e1]
      have e2 : w k ^ (psi M) - w k ^ (psi M) * w k ^ (psi (M + 1) - psi M)
           = w k ^ (psi M) * (1 - w k ^ (psi (M + 1) - psi M)) := by ring
      rw [e2, norm_mul, norm_pow, hw k hk, one_pow, one_mul, ← norm_neg]
      congr 1; ring
    rw [dist_eq_norm] at hcoord
    have h4 : ‖w k ^ (psi M) - w k ^ (psi (M + 1))‖ ≤ dist (X (psi M)) (X (psi (M + 1))) := hcoord
    rw [heq] at h4
    linarith
  obtain ⟨p, hp1, hp⟩ := key (ε / (N + 1)) (by positivity)
  refine ⟨(N + 1) * p, by nlinarith, by nlinarith, fun k hk => ?_⟩
  have h1 : ‖(w k ^ p) ^ (N + 1) - 1‖ ≤ (N + 1 : ℕ) * ‖w k ^ p - 1‖ := by
    apply norm_pow_sub_one_le
    rw [norm_pow, hw k hk, one_pow]
  rw [← pow_mul] at h1
  have hcomm : p * (N + 1) = (N + 1) * p := by ring
  rw [hcomm] at h1
  have h2 : ((N : ℝ) + 1) * ‖w k ^ p - 1‖ ≤ ((N : ℝ) + 1) * (ε / (N + 1)) :=
    mul_le_mul_of_nonneg_left (hp k hk) (by positivity)
  have h3 : ((N : ℝ) + 1) * (ε / (N + 1)) = ε := by field_simp
  push_cast at h1
  linarith

/-!
## The abstract positivity criterion

Given a family `z : ℕ → ℂ` we consider the "Li sums" `∑' k, Re (1 - (z k) ^ n)`.
Under natural summability hypotheses, all these sums are nonnegative if and only if
every `z k` lies in the closed unit disc.
-/

/-- The Li-type sum attached to a family of complex numbers. -/
