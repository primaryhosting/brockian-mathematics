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

import Mathlib
import RequestProject.H10.Factorial

/-!
# The product `∏_{k=1}^{y} (a + b*k)` is Diophantine

This is the last of the classical auxiliary Diophantine functions needed for the
Davis–Putnam–Robinson elimination of bounded universal quantifiers.

The idea is that modulo a large `N` coprime to `b`, one has
`∏_{k=1}^{y} (a + b k) ≡ b^y ∏_{k=1}^{y} (m + k) = b^y y! binom(m+y, y)`
where `m` is the residue `a * b⁻¹ mod N`.
-/

namespace H10

open Nat Finset Dioph

/-- `prodAB a b y = (a + b) * (a + 2b) * ⋯ * (a + y b)`. -/

theorem dpr_of_exists {n m : ℕ} {P : (Fin2 (n + 1) ⊕ Fin2 m → ℕ) → ℤ} (hP : IsPoly P)
    {q : (Fin2 (n + 1) ⊕ Fin2 m → ℕ) → ℤ} (hqb : ∀ v, |P v| ≤ q v)
    (hqm : ∀ v w, (∀ i, v i ≤ w i) → q v ≤ q w)
    (N : ℕ) (x : Vector3 ℕ n)
    (c Q M K : ℕ) (Y : Vector3 ℕ m)
    (hQ : Q = ((q ((N :: x) ⊗ (fun _ => c))).natAbs + c + N)!)
    (hM : M = prodAB 1 Q N)
    (hK : M ∣ Q * K + Q + 1)
    (hY : ∀ j : Fin2 m, c ≤ Y j ∧ M ∣ (Y j).descFactorial (c + 1))
    (hPM : M ∣ (P ((K :: x) ⊗ Y)).natAbs) :
    ∀ k < N, ∃ t : Vector3 ℕ m, P ((k :: x) ⊗ t) = 0 := by
  intro k hk
  set W := (q ((N :: x) ⊗ (fun _ => c))).natAbs + c + N with hW
  have hQpos : 0 < Q := hQ ▸ Nat.factorial_pos _
  set mk := 1 + (k + 1) * Q with hmk
  have hmkM : mk ∣ M := by
    rw [hM, prodAB]
    have h : mk = 1 + Q * (k + 1) := by rw [hmk]; ring
    rw [h]
    exact Finset.dvd_prod_of_mem (fun i => 1 + Q * (i + 1)) (Finset.mem_range.2 hk)
  have hmk2 : mk ≠ 1 := by simp [hmk]; omega
  obtain ⟨p, hp, hpmk⟩ := Nat.exists_prime_and_dvd hmk2
  have hpW : W < p := prime_gt_of_dvd_modulus hp (by rw [← hQ]; exact hpmk)
  have hpM : p ∣ M := hpmk.trans hmkM
  have hpQ : ¬ (p ∣ Q) := by
    intro hd
    have h2 : p ∣ (k + 1) * Q := Dvd.dvd.mul_left hd _
    have : p ∣ 1 := (Nat.dvd_add_right h2).mp (by rw [hmk] at hpmk; rwa [Nat.add_comm] at hpmk)
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hKk : (K : ℤ) ≡ (k : ℤ) [ZMOD (p : ℤ)] := by
    have h1 : (p : ℤ) ∣ ((Q * K + Q + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 (hpM.trans hK)
    have h2 : (p : ℤ) ∣ ((1 + (k + 1) * Q : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 (by rw [← hmk]; exact hpmk)
    have h3 : (p : ℤ) ∣ (Q : ℤ) * ((K : ℤ) - (k : ℤ)) := by
      have h4 := dvd_sub h1 h2
      push_cast at h4 ⊢
      convert h4 using 1
      ring
    have h4 : ¬ ((p : ℤ) ∣ (Q : ℤ)) := fun h => hpQ (by exact_mod_cast h)
    rcases hpZ.dvd_mul.mp h3 with h | h
    · exact absurd h h4
    · exact Int.modEq_iff_dvd.2 (by have h5 := dvd_neg.2 h; rwa [neg_sub] at h5)
  have hYj : ∀ j : Fin2 m, ∃ i, i ≤ c ∧ ((Y j : ℤ) ≡ (i : ℤ) [ZMOD (p : ℤ)]) := by
    intro j
    obtain ⟨hcY, hdvd⟩ := hY j
    have hprod : p ∣ ∏ i ∈ range (c + 1), (Y j - i) := by
      rw [← Nat.descFactorial_eq_prod_range]; exact hpM.trans hdvd
    obtain ⟨i, hi, hpi⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hprod
    have hic : i ≤ c := by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.1 hi)
    refine ⟨i, hic, ?_⟩
    have hcast : ((Y j - i : ℕ) : ℤ) = (Y j : ℤ) - (i : ℤ) := by
      push_cast [Nat.cast_sub (le_trans hic hcY)]; ring
    have hd : (p : ℤ) ∣ (Y j : ℤ) - (i : ℤ) := by
      rw [← hcast]; exact_mod_cast hpi
    exact Int.modEq_iff_dvd.2 (by have h5 := dvd_neg.2 hd; rwa [neg_sub] at h5)
  choose ii hiic hiiY using hYj
  refine ⟨fun j => ii j, ?_⟩
  have hcong : ∀ z, ((((K :: x) ⊗ Y) z : ℕ) : ℤ) ≡ ((((k :: x) ⊗ (fun j => ii j)) z : ℕ) : ℤ)
      [ZMOD (p : ℤ)] := by
    rintro (a | j)
    · cases a with
      | fz => exact hKk
      | fs a => exact Int.ModEq.refl _
    · exact hiiY j
  have hmod := isPoly_modEq hP hcong
  have hdvd1 : (p : ℤ) ∣ P ((K :: x) ⊗ Y) := by
    have h6 : (p : ℤ) ∣ (((P ((K :: x) ⊗ Y)).natAbs : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 (hpM.trans hPM)
    exact Int.dvd_natAbs.mp h6
  have hdvd2 : (p : ℤ) ∣ P ((k :: x) ⊗ fun j => ii j) := by
    have h7 := (Int.modEq_zero_iff_dvd).2 hdvd1
    exact (Int.modEq_zero_iff_dvd).1 (hmod.symm.trans h7)
  have hbound : |P ((k :: x) ⊗ fun j => ii j)| < (p : ℤ) := by
    calc |P ((k :: x) ⊗ fun j => ii j)| ≤ q ((k :: x) ⊗ fun j => ii j) := hqb _
      _ ≤ q ((N :: x) ⊗ (fun _ => c)) := by
          refine hqm _ _ ?_
          rintro (a | j)
          · cases a with
            | fz => exact le_of_lt hk
            | fs a => exact le_refl _
          · exact hiic j
      _ ≤ (W : ℤ) := by
          rw [hW]
          push_cast
          linarith [le_abs_self (q ((N :: x) ⊗ (fun _ => c))), Int.natCast_nonneg c,
            Int.natCast_nonneg N]
      _ < (p : ℤ) := by exact_mod_cast hpW
  exact Int.eq_zero_of_abs_lt_dvd hdvd2 hbound

/-- Completeness of the Davis–Putnam–Robinson coding: witnesses for all `k < N` can be
packaged into the arithmetic conditions. -/
