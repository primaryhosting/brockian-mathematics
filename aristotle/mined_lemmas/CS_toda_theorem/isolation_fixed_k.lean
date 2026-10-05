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
Isolation (Valiant–Vazirani) lemma over `GF(2)`, in the counting form needed for
Toda's theorem.
-/
import Mathlib

namespace CS.Toda

open Finset

/-- Bit vectors of length `m`, as vectors over `GF(2)`. -/
abbrev Vec (m : ℕ) := Fin m → ZMod 2

/-- The standard `GF(2)`-bilinear form. -/

lemma isolation_fixed_k {m k : ℕ} (hk : k ≤ m+1) (A : Finset (Vec m))
    (h1 : 2 * A.card ≤ 2^k) (h2 : 2^k < 4 * A.card) :
    8 * ((univ : Finset (Hsp m)).filter
        (fun h => (A.filter (survives h k)).card = 1)).card ≥ (2^(m+1))^(m+1) := by
  classical
  set HC := (2^(m+1))^(m+1) with hHC
  set a := A.card with ha
  set D := fun (p : Vec m × Vec m) =>
    ((univ : Finset (Hsp m)).filter (fun h => survives h k p.1 ∧ survives h k p.2)).card with hD
  set N := fun (y : Vec m) => ((univ : Finset (Hsp m)).filter (fun h => survives h k y)).card with hN
  set S := ((univ : Finset (Hsp m)).filter (fun h => (A.filter (survives h k)).card = 1)).card with hS
  have hsum1 : ∑ h : Hsp m, (A.filter (survives h k)).card = ∑ y ∈ A, N y := by
    simp only [hN, Finset.card_filter]
    rw [Finset.sum_comm]
  have hsum2 : ∑ h : Hsp m, ((A.filter (survives h k)).card * ((A.filter (survives h k)).card - 1))
      = ∑ p ∈ A.offDiag, D p := by
    have hoff : ∀ h : Hsp m,
        (A.filter (survives h k)).card * ((A.filter (survives h k)).card - 1)
          = (A.offDiag.filter (fun p => survives h k p.1 ∧ survives h k p.2)).card := by
      intro h
      rw [← Finset.offDiag_card]
      congr 1
      ext p
      simp only [Finset.mem_offDiag, Finset.mem_filter]
      tauto
    simp only [hoff, hD, Finset.card_filter]
    rw [Finset.sum_comm]
  have hpoint : ∀ h : Hsp m,
      (A.filter (survives h k)).card
        ≤ (if (A.filter (survives h k)).card = 1 then 1 else 0)
        + (A.filter (survives h k)).card * ((A.filter (survives h k)).card - 1) := by
    intro h
    rcases Nat.lt_or_ge (A.filter (survives h k)).card 2 with hlt | hge
    · interval_cases hh : (A.filter (survives h k)).card <;> simp
    · have : (A.filter (survives h k)).card * 1
          ≤ (A.filter (survives h k)).card * ((A.filter (survives h k)).card - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  have hkey : ∑ y ∈ A, N y ≤ S + ∑ p ∈ A.offDiag, D p := by
    have hSsum : S = ∑ h : Hsp m, (if (A.filter (survives h k)).card = 1 then 1 else 0) := by
      rw [hS, Finset.card_filter]
    rw [hSsum, ← hsum1, ← hsum2, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun h _ => hpoint h)
  have hAne : A.Nonempty := by
    rcases Finset.eq_empty_or_nonempty A with rfl | h
    · simp at h2
    · exact h
  obtain ⟨y0, hy0⟩ := hAne
  have hDval : ∀ p ∈ A.offDiag, 4^k * D p = HC := by
    intro p hp
    simp only [Finset.mem_offDiag] at hp
    exact card_surv_double hk hp.2.2
  have hNval : ∀ y : Vec m, 2^k * N y = HC := fun y => card_surv_single hk y
  rcases Finset.eq_empty_or_nonempty A.offDiag with hoffE | hoffN
  · have hcard1 : a = 1 := by
      have hc := Finset.offDiag_card (s := A)
      rw [hoffE] at hc
      simp only [Finset.card_empty] at hc
      have h1' : 1 ≤ a := Finset.card_pos.mpr ⟨y0, hy0⟩
      nlinarith [hc]
    have hk1 : 2^k = 2 := by omega
    have hsum : ∑ y ∈ A, N y = N y0 := by
      rw [Finset.sum_eq_single y0]
      · intro b hb hbne
        exfalso
        have hmem : (b, y0) ∈ A.offDiag := by
          simp only [Finset.mem_offDiag]
          exact ⟨hb, hy0, hbne⟩
        rw [hoffE] at hmem
        simp at hmem
      · intro h; exact absurd hy0 h
    have hN0 : 2 * N y0 = HC := by rw [← hk1]; exact hNval y0
    rw [hoffE] at hkey
    simp only [Finset.sum_empty, add_zero, hsum] at hkey
    omega
  · obtain ⟨p0, hp0⟩ := hoffN
    have hDsum : ∑ p ∈ A.offDiag, D p = A.offDiag.card * D p0 := by
      rw [Finset.sum_congr rfl (fun p hp => ?_), Finset.sum_const, smul_eq_mul]
      have h1' := hDval p hp
      have h2' := hDval p0 hp0
      have hpow : (0:ℕ) < 4^k := by positivity
      exact Nat.eq_of_mul_eq_mul_left hpow (by omega)
    have hNsum : ∑ y ∈ A, N y = a * N y0 := by
      rw [Finset.sum_congr rfl (fun y hy => ?_), Finset.sum_const, smul_eq_mul, ha]
      have h1' := hNval y
      have h2' := hNval y0
      have hpow : (0:ℕ) < 2^k := by positivity
      exact Nat.eq_of_mul_eq_mul_left hpow (by omega)
    have hoffcard : A.offDiag.card = a * a - a := Finset.offDiag_card A
    have hNv : 2^k * N y0 = HC := hNval y0
    have hDv' : 4^k * D p0 = HC := hDval p0 hp0
    have h4 : (4:ℕ)^k = 2^k * 2^k := by
      rw [show (4:ℕ) = 2*2 by norm_num, mul_pow]
    have hND : N y0 = 2^k * D p0 := by
      have hpos : (0:ℕ) < 2^k := by positivity
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [hNv, ← hDv', h4, mul_assoc]
    have ha1 : 1 ≤ a := Finset.card_pos.mpr ⟨y0, hy0⟩
    obtain ⟨b, hb⟩ : ∃ b, a + b = 2^k := ⟨2^k - a, by omega⟩
    have hb2 : a + b ≤ 2 * b := by omega
    have hb3 : a + b + 1 ≤ 4 * a := by omega
    have haa : a * a - a + a = a * a := by
      have : a ≤ a * a := Nat.le_mul_of_pos_left a ha1
      omega
    have hstep : (a+b) * (a+b) + 8 * (a*a - a) ≤ 8 * (a * (a+b)) := by
      nlinarith [hb2, hb3, ha1, haa]
    have harith : 4^k * D p0 + 8 * ((a*a - a) * D p0) ≤ 8 * (a * (2^k * D p0)) := by
      rw [h4, ← hb]
      calc (a+b) * (a+b) * D p0 + 8 * ((a*a-a) * D p0)
          = ((a+b) * (a+b) + 8 * (a*a - a)) * D p0 := by ring
        _ ≤ (8 * (a * (a+b))) * D p0 := Nat.mul_le_mul_right _ hstep
        _ = 8 * (a * ((a+b) * D p0)) := by ring
    rw [hDsum, hNsum, hND, hoffcard] at hkey
    omega

/-- For every nonempty `A ⊆ GF(2)^m` there is a suitable number of hash rows. -/
