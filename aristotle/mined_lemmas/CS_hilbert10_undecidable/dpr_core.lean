/-
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Hilbert10.Basic
import RequestProject.Hilbert10.MRDP

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Overview

The development is organised as follows.

* `RequestProject.Hilbert10.Basic`: the halting set is r.e. but not computable, normalisation of
  Diophantine sets, and the passage from Mathlib's `Poly` to `MvPolynomial`.
* `RequestProject.Hilbert10.DiophTools`: pairing, unpairing and Gödel's `β` function are
  Diophantine.
* `RequestProject.Hilbert10.Choose`, `.Product`: binomial coefficients, factorials and products
  of arithmetic progressions are Diophantine.
* `RequestProject.Hilbert10.DPRTools`, `.DPRCore`, `.BddForall`: the Davis–Putnam–Robinson
  theorem, i.e. Diophantine relations are closed under bounded universal quantification.
* `RequestProject.Hilbert10.Primrec`: primitive recursive functions have Diophantine graphs.
* `RequestProject.Hilbert10.MRDP`: the MRDP theorem, every r.e. set of naturals is Diophantine.

This file combines these into the undecidability of Hilbert's tenth problem, over `ℕ`
(`CS.hilbert10_undecidable`) and over `ℤ` (`CS.hilbert10_undecidable_int`).
-/

namespace CS

/-- The reduction of Hilbert's tenth problem to the MRDP theorem: if every r.e. set of naturals
is Diophantine, then no algorithm decides solvability of a suitable Diophantine equation with a
natural number parameter.  (This implication is proved unconditionally; the MRDP hypothesis is
supplied by `CS.dioph_of_rePred`.) -/

theorem dpr_core (p : Poly (Fin2 (n + 1) ⊕ Fin m)) (C D : ℕ)
    (hCD : ∀ (u : (Fin2 (n + 1) ⊕ Fin m) → ℕ) (t : ℕ), (∀ i, u i ≤ t) →
      (p u).natAbs ≤ C * (t + 1) ^ D)
    (v : Vector3 ℕ n) (s : ℕ) (hs : ∀ a, v a ≤ s) (N : ℕ) :
    (∀ i < N, ∃ t : Fin m → ℕ, p (Sum.elim (Vector3.cons i v) t) = 0) ↔
    ∃ (c Y K : ℕ) (X : Fin m → ℕ),
      C * (N + Y + s + 1) ^ D + (N + Y + s) < c ∧
      prodLin 1 (Nat.factorial c) N ∣ Nat.factorial c * (K + 1) + 1 ∧
      (∀ j, Y < X j ∧ prodLin 1 (Nat.factorial c) N ∣
          Nat.factorial (Y + 1) * Nat.choose (X j) (Y + 1)) ∧
      prodLin 1 (Nat.factorial c) N ∣ (p (Sum.elim (Vector3.cons K v) X)).natAbs := by
  constructor
  · -- Construction of the code from the witnesses
    intro H
    classical
    have Hw : ∀ i : ℕ, ∃ t : Fin m → ℕ, i < N → p (Sum.elim (Vector3.cons i v) t) = 0 := by
      intro i
      by_cases hi : i < N
      · obtain ⟨t, ht⟩ := H i hi
        exact ⟨t, fun _ => ht⟩
      · exact ⟨fun _ => 0, fun h => absurd h hi⟩
    choose T hT using Hw
    set Y := Finset.sup (Finset.range N)
      (fun i => Finset.sup Finset.univ (fun j : Fin m => T i j)) with hYdef
    have hTY : ∀ i, i < N → ∀ j, T i j ≤ Y := by
      intro i hi j
      refine le_trans (Finset.le_sup (f := fun j : Fin m => T i j) (Finset.mem_univ j)) ?_
      exact Finset.le_sup (f := fun i => Finset.sup Finset.univ (fun j : Fin m => T i j))
        (Finset.mem_range.2 hi)
    set c := C * (N + Y + s + 1) ^ D + (N + Y + s) + 1 with hcdef
    set d := Nat.factorial c with hddef
    set M := prodLin 1 d N with hMdef
    have hNc : N ≤ c := by omega
    have hMprod : M = ∏ k ∈ Finset.Icc 1 N, (1 + d * k) := rfl
    have hdvdM : ∀ k ∈ Finset.Icc 1 N, (1 + d * k) ∣ M := fun k hk => by
      rw [hMprod]; exact Finset.dvd_prod_of_mem _ hk
    have hMpos : 0 < M := by
      rw [hMprod]
      exact Finset.prod_pos fun k _ => by positivity
    have hcop : ((Finset.Icc 1 N : Finset ℕ) : Set ℕ).Pairwise
        (Function.onFun Nat.Coprime (fun k => 1 + d * k)) := by
      intro k hk l hl hne
      simp only [Finset.coe_Icc, Set.mem_Icc] at hk hl
      exact moduli_coprime hk.1 hl.1 (by omega) (by omega) hne
    -- Chinese remaindering
    obtain ⟨K, hK⟩ := Nat.chineseRemainderOfFinset (fun k => k - 1) (fun k => 1 + d * k)
      (Finset.Icc 1 N) (fun k _ => by positivity) hcop
    have hXex : ∀ j : Fin m, ∃ x : ℕ, Y < x ∧
        ∀ k ∈ Finset.Icc 1 N, x ≡ T (k - 1) j [MOD 1 + d * k] := by
      intro j
      obtain ⟨x, hx⟩ := Nat.chineseRemainderOfFinset (fun k => T (k - 1) j) (fun k => 1 + d * k)
        (Finset.Icc 1 N) (fun k _ => by positivity) hcop
      refine ⟨x + M * (Y + 1), ?_, fun k hk => ?_⟩
      · have : Y + 1 ≤ M * (Y + 1) := Nat.le_mul_of_pos_left _ hMpos
        omega
      · exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
          (by simpa using Dvd.dvd.mul_right (hdvdM k hk) (Y + 1))).symm.trans (hx k hk)
    choose X hXY hXcong using hXex
    refine ⟨c, Y, K, X, by omega, ?_, ?_, ?_⟩
    · -- `M ∣ d * (K+1) + 1`
      rw [prodLin_eq_prod]
      refine nat_prod_dvd_of_coprime hcop fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
      have h1 : K + 1 ≡ k [MOD 1 + d * k] := by
        have := (hK k hk).add_right 1
        simpa [Nat.sub_add_cancel hk1] using this
      have h2 : d * (K + 1) + 1 ≡ d * k + 1 [MOD 1 + d * k] :=
        (Nat.ModEq.mul_left d h1).add_right 1
      have h3 : d * k + 1 ≡ 0 [MOD 1 + d * k] := by
        rw [Nat.modEq_zero_iff_dvd]
        exact ⟨1, by ring⟩
      exact (Nat.modEq_zero_iff_dvd).1 (h2.trans h3)
    · -- residues of `X j` are at most `Y`
      intro j
      refine ⟨hXY j, ?_⟩
      rw [← Nat.descFactorial_eq_factorial_mul_choose, descFactorial_eq_prod, prodLin_eq_prod]
      refine nat_prod_dvd_of_coprime hcop fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
      have hkN : k ≤ N := (Finset.mem_Icc.1 hk).2
      have hTle : T (k - 1) j ≤ Y := hTY (k - 1) (by omega) j
      have hmem : T (k - 1) j ∈ Finset.range (Y + 1) := Finset.mem_range.2 (by omega)
      have hdvd1 : (1 + d * k) ∣ (X j - T (k - 1) j) :=
        (Nat.modEq_iff_dvd' (by have := hXY j; omega)).1 (hXcong j k hk).symm
      exact hdvd1.trans (Finset.dvd_prod_of_mem (fun t => X j - t) hmem)
    · -- the polynomial congruence
      rw [prodLin_eq_prod]
      refine nat_prod_dvd_of_coprime hcop fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
      have hkN : k ≤ N := (Finset.mem_Icc.1 hk).2
      have hcong : (p (Sum.elim (Vector3.cons K v) X) : ℤ)
          ≡ p (Sum.elim (Vector3.cons (k - 1) v) (T (k - 1))) [ZMOD ((1 + d * k : ℕ) : ℤ)] := by
        refine poly_intModEq p ?_
        rintro (z | j)
        · cases z with
          | fz => simpa using Int.natCast_modEq_iff.mpr (hK k hk)
          | fs a => simp
        · simpa using Int.natCast_modEq_iff.mpr (hXcong j k hk)
      have hzero : p (Sum.elim (Vector3.cons (k - 1) v) (T (k - 1))) = 0 :=
        hT (k - 1) (by omega)
      rw [hzero] at hcong
      have : ((1 + d * k : ℕ) : ℤ) ∣ p (Sum.elim (Vector3.cons K v) X) :=
        Int.modEq_zero_iff_dvd.1 hcong
      exact Int.natCast_dvd.1 this
  · -- Recovering the witnesses from the code
    rintro ⟨c, Y, K, X, h1, h2, h3, h4⟩ i hi
    classical
    set d := Nat.factorial c with hddef
    set M := prodLin 1 d N with hMdef
    have hMprod : M = ∏ k ∈ Finset.Icc 1 N, (1 + d * k) := rfl
    have hmemi : (i + 1) ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hmi : (1 + d * (i + 1)) ∣ M := by
      rw [hMprod]; exact Finset.dvd_prod_of_mem _ hmemi
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero c)
    have hne1 : 1 + d * (i + 1) ≠ 1 := by
      have : 1 ≤ d * (i + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      omega
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne1
    have hqnd : ¬ q ∣ d := by
      intro h
      have h4' : q ∣ (1 + d * (i + 1)) - d * (i + 1) := Nat.dvd_sub hqdvd (h.mul_right (i + 1))
      simp at h4'
      exact hq.one_lt.ne' h4'
    have hqc : c < q := by
      by_contra hle
      push_neg at hle
      exact hqnd (Nat.dvd_factorial hq.pos hle)
    -- `K ≡ i` modulo `q`
    have hqM : q ∣ d * (K + 1) + 1 := hqdvd.trans (hmi.trans h2)
    have hqK : (K : ℤ) ≡ (i : ℤ) [ZMOD (q : ℤ)] := by
      have hA : (q : ℤ) ∣ ((d : ℤ) * (K + 1) + 1) := by exact_mod_cast Int.natCast_dvd_natCast.2 hqM
      have hB : (q : ℤ) ∣ (1 + (d : ℤ) * (i + 1)) := by
        exact_mod_cast Int.natCast_dvd_natCast.2 hqdvd
      have hC : (q : ℤ) ∣ (d : ℤ) * ((K : ℤ) - i) := by
        have := dvd_sub hA hB
        have he : ((d : ℤ) * (K + 1) + 1) - (1 + (d : ℤ) * (i + 1)) = (d : ℤ) * ((K : ℤ) - i) := by
          ring
        rwa [he] at this
      have hprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
      rcases hprime.dvd_mul.1 hC with h | h
      · exact absurd (Int.natCast_dvd_natCast.1 h) hqnd
      · exact (Int.modEq_iff_dvd.2 h).symm
    -- small residues of the `X j`
    have hres : ∀ j : Fin m, ∃ y, y ≤ Y ∧ (X j : ℤ) ≡ (y : ℤ) [ZMOD (q : ℤ)] := by
      intro j
      obtain ⟨hYX, hdvdX⟩ := h3 j
      have hq1 : q ∣ Nat.factorial (Y + 1) * Nat.choose (X j) (Y + 1) :=
        hqdvd.trans (hmi.trans hdvdX)
      rw [← Nat.descFactorial_eq_factorial_mul_choose, descFactorial_eq_prod] at hq1
      obtain ⟨y, hy, hyq⟩ := (Nat.Prime.prime hq).exists_mem_finset_dvd hq1
      have hyY : y ≤ Y := by simp at hy; omega
      refine ⟨y, hyY, ?_⟩
      have hdvdz : (q : ℤ) ∣ ((X j : ℤ) - y) := by
        have h := Int.natCast_dvd_natCast.2 hyq
        rwa [Nat.cast_sub (by omega)] at h
      exact (Int.modEq_iff_dvd.2 hdvdz).symm
    choose y hyY hycong using hres
    -- the polynomial vanishes at the recovered witnesses
    have hcong : (p (Sum.elim (Vector3.cons K v) X) : ℤ)
        ≡ p (Sum.elim (Vector3.cons i v) y) [ZMOD (q : ℤ)] := by
      refine poly_intModEq p ?_
      rintro (z | j)
      · cases z with
        | fz => simpa using hqK
        | fs a => simp
      · simpa using hycong j
    have hqdvdP : (q : ℤ) ∣ p (Sum.elim (Vector3.cons K v) X) := by
      have : q ∣ (p (Sum.elim (Vector3.cons K v) X)).natAbs := hqdvd.trans (hmi.trans h4)
      exact Int.natCast_dvd.2 this
    have hqz : (q : ℤ) ∣ p (Sum.elim (Vector3.cons i v) y) :=
      Int.modEq_zero_iff_dvd.1 (hcong.symm.trans (Int.modEq_zero_iff_dvd.2 hqdvdP))
    have hbound : (p (Sum.elim (Vector3.cons i v) y)).natAbs ≤ C * (N + Y + s + 1) ^ D := by
      refine hCD _ (N + Y + s) ?_
      rintro (z | j)
      · cases z with
        | fz => simp only [Sum.elim_inl, Vector3.cons_fz]; omega
        | fs a => simp only [Sum.elim_inl, Vector3.cons_fs]; have := hs a; omega
      · simp only [Sum.elim_inr]; have := hyY j; omega
    refine ⟨y, ?_⟩
    by_contra hne
    have hle : q ≤ (p (Sum.elim (Vector3.cons i v) y)).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.2 hne) (Int.natCast_dvd.1 hqz)
    omega

end CS

import Mathlib

/-!
# Diophantine functions: pairing, unpairing and Gödel's `β`

We extend Mathlib's toolkit of Diophantine functions (`Mathlib/NumberTheory/Dioph.lean`) with
Cantor pairing, its inverses, and Gödel's `β` function (`Nat.beta`), which is the sequence coding
device used in the arithmetisation of primitive recursion.
-/

namespace CS

open Dioph Nat Fin2 Vector3

/-- The graph of Cantor pairing is Diophantine. -/
