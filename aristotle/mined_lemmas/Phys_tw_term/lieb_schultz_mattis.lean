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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Part I: an abstract twist (flux insertion) estimate

We model a quantum system on a finite configuration space `α`: states are functions
`ψ : α → ℂ`, the (squared) norm is `∑ c, ‖ψ c‖^2`, and a Hamiltonian is a matrix
`H : α → α → ℂ`.  `qf H ψ` is the energy expectation `⟪ψ, H ψ⟫` (real part).
-/

section Abstract

variable {α : Type*} [Fintype α]

/-- The energy expectation value `⟪ψ, H ψ⟫` (real part). -/

theorem lieb_schultz_mattis (hn : Even n)
    (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ)
    (hherm : ∀ p q, b q p = (starRingEnd ℂ) (b p q))
    (hcons : ∀ p q, b p q ≠ 0 → w n p.1 + w n p.2 = w n q.1 + w n q.2)
    (B : ℝ) (hB : ∀ p, ∑ q, ‖b p q‖ ≤ B)
    (ψ : Conf n L → ℂ) (E0 : ℝ)
    (hunit : nrm2 ψ = 1)
    (hsector : ∀ c, ψ c ≠ 0 → M2 c = 0)
    (heig : ∀ c, ∑ c', Hchain b c c' * ψ c' = (E0 : ℂ) * ψ c)
    (hmin : ∀ φ : Conf n L → ℂ, nrm2 φ = 1 → E0 ≤ qf (Hchain b) φ) :
    (∃ φ : Conf n L → ℂ, nrm2 φ = 1 ∧ ip ψ φ = 0 ∧ qf (Hchain b) φ = E0) ∨
    (∃ φ : Conf n L → ℂ, nrm2 φ = 1 ∧ ip ψ φ = 0 ∧ E0 < qf (Hchain b) φ ∧
      qf (Hchain b) φ ≤ E0 + 2 * Real.pi ^ 2 * ((n : ℝ) - 1) ^ 2 * B / L) := by
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := lt_of_le_of_ne (Nat.cast_nonneg L) (Ne.symm hLne)
  set H := Hchain (L := L) b with hH
  set C : ℝ := 2 * Real.pi ^ 2 * ((n : ℝ) - 1) ^ 2 * B / L with hC
  -- the dichotomy, given a unit vector orthogonal to `ψ` with energy at most `E0 + C`
  have main : ∀ φ : Conf n L → ℂ, nrm2 φ = 1 → ip ψ φ = 0 → qf H φ ≤ E0 + C →
      (∃ φ : Conf n L → ℂ, nrm2 φ = 1 ∧ ip ψ φ = 0 ∧ qf H φ = E0) ∨
      (∃ φ : Conf n L → ℂ, nrm2 φ = 1 ∧ ip ψ φ = 0 ∧ E0 < qf H φ ∧ qf H φ ≤ E0 + C) := by
    intro φ h1 h2 h3
    rcases (hmin φ h1).eq_or_lt with h | h
    · exact Or.inl ⟨φ, h1, h2, h.symm⟩
    · exact Or.inr ⟨φ, h1, h2, h, h3⟩
  by_cases hprop : ∃ lam : ℂ, ∀ c, ψ (sh c) = lam * ψ c
  · -- the ground state is a translation eigenstate: insert a flux
    obtain ⟨lam, hlam⟩ := hprop
    have hlam1 : ‖lam‖ = 1 := by
      have h1 : nrm2 (fun c => ψ (sh c)) = ‖lam‖ ^ 2 * nrm2 ψ := by
        rw [nrm2, nrm2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by rw [hlam c, norm_mul, mul_pow]
      rw [nrm2_sh, hunit, mul_one] at h1
      nlinarith [norm_nonneg lam]
    have hunit' : ∑ c, ‖ψ c‖ ^ 2 = 1 := hunit
    have hE : qf H ψ = E0 := by rw [qf_of_eigen H ψ E0 heig, hunit, mul_one]
    -- the two twisted states
    have hodd : ∀ c, ψ c ≠ 0 → ∃ m : ℤ, theta (sh c) - theta c = Real.pi * (2 * m + 1) :=
      theta_odd_jump hn ψ hsector
    have hodd' : ∀ c, ψ c ≠ 0 → ∃ m : ℤ,
        (fun d => -theta d) (sh c) - (fun d => -theta d) c = Real.pi * (2 * m + 1) := by
      intro c hc
      obtain ⟨m, hm⟩ := hodd c hc
      exact ⟨-m - 1, by simp only []; push_cast; linarith [hm]⟩
    have horth : ip ψ (tw theta ψ) = 0 :=
      ip_eq_zero_of_shift ψ _ lam hlam1 hlam (tw_sh_of_odd ψ theta hodd lam hlam)
    have horth' : ip ψ (tw (fun d => -theta d) ψ) = 0 :=
      ip_eq_zero_of_shift ψ _ lam hlam1 hlam (tw_sh_of_odd ψ _ hodd' lam hlam)
    have hn1 : nrm2 (tw (theta (n := n) (L := L)) ψ) = 1 := by
      rw [nrm2]; simpa [norm_tw] using hunit'
    have hn1' : nrm2 (tw (fun d => -theta d) ψ) = 1 := by
      rw [nrm2]; simpa [norm_tw] using hunit'
    -- the twist estimate
    have hbd := qf_tw_add_le H theta ψ (2 * Real.pi * ((n : ℝ) - 1) / L) ((L : ℝ) * B)
      (Hchain_herm b hherm) (fun c c' h => theta_flux b hcons c c' h)
      (Hchain_rowsum b B hB)
    rw [hunit', hE, mul_one] at hbd
    have hCeq : (2 * Real.pi * ((n : ℝ) - 1) / L) ^ 2 * ((L : ℝ) * B) = 2 * C := by
      rw [hC]
      field_simp
    rw [hCeq] at hbd
    rcases le_or_gt (qf H (tw theta ψ)) (E0 + C) with h | h
    · exact main _ hn1 horth h
    · exact main _ hn1' horth' (by linarith)
  · -- the ground state is not a translation eigenstate: the ground level is degenerate
    push_neg at hprop
    set k : ℂ := ip ψ (fun d => ψ (sh d)) with hk
    set χ : Conf n L → ℂ := fun c => ψ (sh c) - k * ψ c with hχ
    have heigχ : ∀ c, ∑ c', H c c' * χ c' = (E0 : ℂ) * χ c := by
      intro c
      have hsplit : ∑ c', H c c' * χ c'
          = (∑ c', H c c' * ψ (sh c')) - k * ∑ c', H c c' * ψ c' := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c' _ => by rw [hχ]; ring
      rw [hsplit, eig_sh b ψ E0 heig c, heig c, hχ]
      ring
    have horthχ : ip ψ χ = 0 := by
      have : ip ψ χ = ip ψ (fun d => ψ (sh d)) - k * ip ψ ψ := by
        rw [ip, ip, ip, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => by rw [hχ]; ring
      rw [this, ip_self, hunit, ← hk]
      push_cast
      ring
    have hne : nrm2 χ ≠ 0 := by
      intro h0
      obtain ⟨c0, hc0⟩ := hprop k
      have hz : ‖χ c0‖ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg ‖χ c‖)).1 h0 c0
          (Finset.mem_univ c0)
      have hzz : χ c0 = 0 := by simpa using hz
      simp only [hχ, sub_eq_zero] at hzz
      exact hc0 hzz
    exact Or.inl (exists_unit_eigen H ψ χ E0 hne heigχ horthχ)

/-! ## Part IV: the hypotheses are not vacuous -/

/-- The spin-1/2 Heisenberg bond matrix, in the basis `0 = up`, `1 = down`:
`S·S = S^z⊗S^z + (S^+⊗S^- + S^-⊗S^+)/2`. -/
