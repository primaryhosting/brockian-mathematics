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

theorem exists_of_dpr {n m : ℕ} {P : (Fin2 (n + 1) ⊕ Fin2 m → ℕ) → ℤ} (hP : IsPoly P)
    {q : (Fin2 (n + 1) ⊕ Fin2 m → ℕ) → ℤ}
    (N : ℕ) (x : Vector3 ℕ n)
    (H : ∀ k < N, ∃ t : Vector3 ℕ m, P ((k :: x) ⊗ t) = 0) :
    (∃ (c Q M K : ℕ) (Y : Vector3 ℕ m),
      Q = ((q ((N :: x) ⊗ (fun _ => c))).natAbs + c + N)! ∧
      M = prodAB 1 Q N ∧
      M ∣ Q * K + Q + 1 ∧
      (∀ j : Fin2 m, c ≤ Y j ∧ M ∣ (Y j).descFactorial (c + 1)) ∧
      M ∣ (P ((K :: x) ⊗ Y)).natAbs) := by
  classical
  choose! t ht using H
  set c := (range N).sup (fun k => Finset.univ.sup (t k)) with hc
  have htc : ∀ k, k < N → ∀ j, t k j ≤ c := by
    intro k hk j
    exact le_trans (Finset.le_sup (f := t k) (Finset.mem_univ j))
      (Finset.le_sup (f := fun k => Finset.univ.sup (t k)) (Finset.mem_range.2 hk))
  set W := (q ((N :: x) ⊗ (fun _ => c))).natAbs + c + N with hW
  set Q := W ! with hQ
  set M := prodAB 1 Q N with hM
  set mk : ℕ → ℕ := fun k => 1 + (k + 1) * Q with hmk
  have hMprod : M = ∏ k ∈ range N, mk k := by
    rw [hM, prodAB, hmk]
    exact Finset.prod_congr rfl (fun k _ => by ring)
  have hpair : ((range N : Finset ℕ) : Set ℕ).Pairwise (Function.onFun Nat.Coprime mk) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    exact coprime_moduli (by omega) (by omega) hab
  have hne0 : ∀ k ∈ range N, mk k ≠ 0 := by intro k _; simp [hmk]
  have hmkM : ∀ k ∈ range N, mk k ∣ M := by
    intro k hk; rw [hMprod]; exact Finset.dvd_prod_of_mem mk hk
  obtain ⟨K, hK⟩ := Nat.chineseRemainderOfFinset (fun k => k) mk (range N) hne0 hpair
  have hMpos : 0 < M := by
    rw [hMprod]; exact Finset.prod_pos (fun k _ => by simp [hmk])
  have hYex : ∀ j : Fin2 m, ∃ Y0 : ℕ, ∀ k ∈ range N, Y0 ≡ t k j [MOD mk k] := by
    intro j
    obtain ⟨Y0, hY0⟩ := Nat.chineseRemainderOfFinset (fun k => t k j) mk (range N) hne0 hpair
    exact ⟨Y0, hY0⟩
  choose Y0 hY0 using hYex
  set Y : Vector3 ℕ m := fun j => Y0 j + M * c with hY
  have hYcong : ∀ (j : Fin2 m) (k : ℕ), k < N → Y j ≡ t k j [MOD mk k] := by
    intro j k hk
    have h1 : M * c ≡ 0 [MOD mk k] :=
      (Nat.modEq_zero_iff_dvd).2 (Dvd.dvd.mul_right (hmkM k (Finset.mem_range.2 hk)) c)
    calc Y j = Y0 j + M * c := rfl
      _ ≡ Y0 j + 0 [MOD mk k] := Nat.ModEq.add_left _ h1
      _ = Y0 j := by ring
      _ ≡ t k j [MOD mk k] := hY0 j k (Finset.mem_range.2 hk)
  have hcY : ∀ j, c ≤ Y j := by
    intro j
    have : c ≤ M * c := Nat.le_mul_of_pos_left c hMpos
    simp only [hY]; omega
  refine ⟨c, Q, M, K, Y, rfl, rfl, ?_, ?_, ?_⟩
  · rw [hMprod]
    refine prod_dvd_of_pairwise_coprime hpair (fun k hk => ?_)
    have h1 : Q * K + Q + 1 ≡ Q * k + Q + 1 [MOD mk k] :=
      Nat.ModEq.add_right 1 (Nat.ModEq.add_right Q (Nat.ModEq.mul_left Q (hK k hk)))
    have h2 : Q * k + Q + 1 ≡ 0 [MOD mk k] := by
      refine (Nat.modEq_zero_iff_dvd).2 ?_
      have h3 : Q * k + Q + 1 = mk k := by simp [hmk]; ring
      rw [h3]
    exact (Nat.modEq_zero_iff_dvd).1 (h1.trans h2)
  · intro j
    refine ⟨hcY j, ?_⟩
    rw [hMprod]
    refine prod_dvd_of_pairwise_coprime hpair (fun k hk => ?_)
    rw [Nat.descFactorial_eq_prod_range]
    have hmem : t k j ∈ range (c + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le (htc k (Finset.mem_range.1 hk) j))
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun i => Y j - i) hmem)
    exact (Nat.modEq_iff_dvd' (le_trans (htc k (Finset.mem_range.1 hk) j) (hcY j))).mp
      (hYcong j k (Finset.mem_range.1 hk)).symm
  · rw [hMprod]
    refine prod_dvd_of_pairwise_coprime hpair (fun k hk => ?_)
    have hcong : ∀ z, ((((K :: x) ⊗ Y) z : ℕ) : ℤ) ≡ ((((k :: x) ⊗ t k) z : ℕ) : ℤ)
        [ZMOD ((mk k : ℕ) : ℤ)] := by
      rintro (a | j)
      · cases a with
        | fz => exact Int.natCast_modEq_iff.mpr (hK k hk)
        | fs a => exact Int.ModEq.refl _
      · exact Int.natCast_modEq_iff.mpr (hYcong j k (Finset.mem_range.1 hk))
    have hmod := isPoly_modEq hP hcong
    rw [ht k (Finset.mem_range.1 hk)] at hmod
    have hd : ((mk k : ℕ) : ℤ) ∣ P ((K :: x) ⊗ Y) := (Int.modEq_zero_iff_dvd).1 hmod
    exact Int.ofNat_dvd_left.mp hd

end H10

import Mathlib
import RequestProject.H10.Digits

/-!
# Binomial coefficients and factorials are Diophantine

Binomial coefficients are read off as base-`u` digits of `(u+1)^n` for large `u`
(so they are Diophantine, using Matiyasevic's theorem `Dioph.pow_dioph`), and the
factorial is obtained from `n ! = ⌊r ^ n / (r.choose n)⌋` for large `r`.
-/

namespace H10

open Nat Dioph

/-- Binomial coefficients are Diophantine. -/
