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
theorem hilbert10_undecidable_of_mrdp
    (mrdp : ∀ {S : ℕ → Prop}, REPred S → Dioph {v : Fin 1 → ℕ | S (v 0)}) :
    ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℤ),
      ¬ ComputablePred fun a : ℕ =>
        ∃ y : Fin n → ℕ, MvPolynomial.eval (fun i => ((Fin.cons a y : Fin (n + 1) → ℕ) i : ℤ)) P
          = 0 := by
  obtain ⟨n, p, hp⟩ := dioph_exists_finite_poly (mrdp haltSet_re)
  obtain ⟨P, hP⟩ := exists_mvPolynomial (p.map (Sum.elim (fun _ => (0 : Fin (n + 1))) Fin.succ))
  refine ⟨n, P, fun hcomp => haltSet_not_computable (hcomp.of_eq fun a => ?_)⟩
  have key : ∀ y : Fin n → ℕ,
      MvPolynomial.eval (fun i => ((Fin.cons a y : Fin (n + 1) → ℕ) i : ℤ)) P
        = p (Sum.elim (fun _ => a) y) := by
    intro y
    rw [hP, Poly.map_apply]
    congr 1
    funext s
    rcases s with i | j <;> simp
  simp only [key]
  exact (hp (fun _ => a)).symm

/-- **Hilbert's tenth problem is undecidable**: there is a polynomial `P` with integer
coefficients in `n + 1` variables such that no algorithm decides, given `a : ℕ`, whether the
equation `P (a, y₁, …, yₙ) = 0` has a solution in natural numbers. -/
theorem hilbert10_undecidable :
    ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℤ),
      ¬ ComputablePred fun a : ℕ =>
        ∃ y : Fin n → ℕ, MvPolynomial.eval (fun i => ((Fin.cons a y : Fin (n + 1) → ℕ) i : ℤ)) P
          = 0 :=
  hilbert10_undecidable_of_mrdp dioph_of_rePred

/-- Replacing each unknown by a sum of four squares turns the natural-number version of
Hilbert's tenth problem into the integer version. -/
theorem exists_int_poly {n : ℕ} (P₀ : MvPolynomial (Fin (n + 1)) ℤ) :
    ∃ P : MvPolynomial (Fin (n * 4 + 1)) ℤ, ∀ a : ℕ,
      (∃ y : Fin n → ℕ,
          MvPolynomial.eval (fun i => ((Fin.cons a y : Fin (n + 1) → ℕ) i : ℤ)) P₀ = 0)
        ↔ (∃ z : Fin (n * 4) → ℤ, MvPolynomial.eval (Fin.cons (a : ℤ) z) P = 0) := by
  classical
  set sub : Fin (n + 1) → MvPolynomial (Fin (n * 4 + 1)) ℤ :=
    Fin.cases (MvPolynomial.X 0)
      (fun j => ∑ s : Fin 4, (MvPolynomial.X (Fin.succ (finProdFinEquiv (j, s)))) ^ 2) with hsub
  refine ⟨MvPolynomial.bind₁ sub P₀, fun a => ?_⟩
  have hval : ∀ z : Fin (n * 4) → ℤ,
      MvPolynomial.eval (Fin.cons (a : ℤ) z) (MvPolynomial.bind₁ sub P₀)
        = MvPolynomial.eval (fun i => MvPolynomial.eval (Fin.cons (a : ℤ) z) (sub i)) P₀ := by
    intro z; exact MvPolynomial.eval₂Hom_bind₁ _ _ _ _
  have hzero : ∀ z : Fin (n * 4) → ℤ,
      MvPolynomial.eval (Fin.cons (a : ℤ) z) (sub 0) = (a : ℤ) := by
    intro z; simp [hsub]
  have hsucc : ∀ (z : Fin (n * 4) → ℤ) (j : Fin n),
      MvPolynomial.eval (Fin.cons (a : ℤ) z) (sub j.succ)
        = ∑ s : Fin 4, (z (finProdFinEquiv (j, s))) ^ 2 := by
    intro z j; simp [hsub]
  constructor
  · rintro ⟨y, hy⟩
    have hfour : ∀ j : Fin n, ∃ f : Fin 4 → ℕ, ∑ s, (f s) ^ 2 = y j := by
      intro j
      obtain ⟨w, x, u, v, h⟩ := Nat.sum_four_squares (y j)
      exact ⟨![w, x, u, v], by simpa [Fin.sum_univ_four] using h⟩
    choose f hf using hfour
    refine ⟨fun i => ((f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 : ℕ) : ℤ), ?_⟩
    rw [hval]
    rw [show (fun i => MvPolynomial.eval
        (Fin.cons (a : ℤ)
          fun i => ((f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 : ℕ) : ℤ))
        (sub i)) = fun i => ((Fin.cons a y : Fin (n + 1) → ℕ) i : ℤ) from ?_]
    · exact hy
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [hzero]
    · intro j
      rw [hsucc]
      simp only [Equiv.symm_apply_apply, Fin.cons_succ]
      rw [← hf j]
      push_cast
      ring_nf
  · rintro ⟨z, hz⟩
    refine ⟨fun j => (∑ s : Fin 4, (z (finProdFinEquiv (j, s))) ^ 2).toNat, ?_⟩
    rw [hval] at hz
    rw [show (fun i => ((Fin.cons a (fun j => (∑ s : Fin 4, (z (finProdFinEquiv (j, s))) ^ 2).toNat)
        : Fin (n + 1) → ℕ) i : ℤ))
        = fun i => MvPolynomial.eval (Fin.cons (a : ℤ) z) (sub i) from ?_]
    · exact hz
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [hzero]
    · intro j
      rw [hsucc]
      simp only [Fin.cons_succ]
      rw [Int.toNat_of_nonneg (by positivity)]

/-- **Hilbert's tenth problem is undecidable, integer version**: there is a polynomial `P` with
integer coefficients in `m + 1` variables such that no algorithm decides, given `a : ℕ`, whether
the equation `P (a, y₁, …, y_m) = 0` has a solution in integers. -/
theorem hilbert10_undecidable_int :
    ∃ (m : ℕ) (P : MvPolynomial (Fin (m + 1)) ℤ),
      ¬ ComputablePred fun a : ℕ =>
        ∃ y : Fin m → ℤ, MvPolynomial.eval (Fin.cons (a : ℤ) y) P = 0 := by
  obtain ⟨n, P₀, h⟩ := hilbert10_undecidable
  obtain ⟨P, hP⟩ := exists_int_poly P₀
  exact ⟨n * 4, P, fun hcomp => h (hcomp.of_eq fun a => (hP a).symm)⟩

end CS

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

import RequestProject.Hilbert10.BddForall

/-!
# Primitive recursive functions are Diophantine

Using Gödel's `β` function to code the computation sequence of a primitive recursion, every
primitive recursive function `ℕ → ℕ` has a Diophantine graph.  The other ingredient is the
Davis–Putnam–Robinson theorem `CS.bddForall_dioph`: Diophantine relations are closed under
bounded universal quantification.
-/

namespace CS

open Dioph Nat Fin2 Vector3

/-- The value of a primitive recursion is characterised by the existence of a `β`-code for the
sequence of intermediate values. -/
theorem prec_graph {f g : ℕ → ℕ} (z n w : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) (f z) (fun y IH => g (Nat.pair z (Nat.pair y IH))) n) = w ↔
      ∃ c, Nat.beta c 0 = f z ∧
        (∀ i < n, Nat.beta c (i + 1) = g (Nat.pair z (Nat.pair i (Nat.beta c i)))) ∧
        Nat.beta c n = w := by
  let H : ℕ → ℕ := fun n => Nat.rec (motive := fun _ => ℕ) (f z)
    (fun y IH => g (Nat.pair z (Nat.pair y IH))) n
  have hH0 : H 0 = f z := rfl
  have hHs : ∀ y, H (y + 1) = g (Nat.pair z (Nat.pair y (H y))) := fun _ => rfl
  show H n = w ↔ _
  constructor
  · rintro rfl
    let l : List ℕ := (List.range (n + 1)).map H
    have hget : ∀ i : ℕ, i < n + 1 → Nat.beta (Nat.unbeta l) i = H i := by
      intro i hi
      have := Nat.beta_unbeta_coe l ⟨i, by simp [l]; omega⟩
      simpa [l] using this
    refine ⟨Nat.unbeta l, ?_, ?_, ?_⟩
    · rw [hget 0 (by omega), hH0]
    · intro i hi
      rw [hget (i + 1) (by omega), hget i (by omega), hHs i]
    · rw [hget n (by omega)]
  · rintro ⟨c, h0, hstep, hend⟩
    have key : ∀ i ≤ n, Nat.beta c i = H i := by
      intro i
      induction i with
      | zero => intro _; rw [h0, hH0]
      | succ j ih =>
        intro hj
        rw [hstep j (by omega), ih (by omega), hHs j]
    rw [← key n le_rfl, hend]

/-- Every primitive recursive function has a Diophantine graph. -/
theorem dioph_of_primrec {F : ℕ → ℕ} (hF : Nat.Primrec F) :
    DiophFn fun v : Vector3 ℕ 1 => F (v &0) := by
  induction hF with
  | zero => exact D.0
  | succ => exact (D&0) D+ (D.1)
  | left => exact unpair1_diophFn
  | right => exact unpair2_diophFn
  | pair _ _ ihf ihg => exact pairFn_dioph ihf ihg
  | comp _ _ ihf ihg => exact comp1_dioph ihf ihg
  | @prec f g _ _ ihf ihg =>
    refine (diophFn_vec _).2 ?_
    have c1 : Dioph fun w : Vector3 ℕ 3 => Nat.beta (w &0) 0 = f ((w &2).unpair.1) :=
      (beta_dioph (D&0) (D.0)) D= (comp1_dioph ihf (unpair1_dioph (D&2)))
    have c3 : Dioph fun w : Vector3 ℕ 3 => Nat.beta (w &0) ((w &2).unpair.2) = w &1 :=
      (beta_dioph (D&0) (unpair2_dioph (D&2))) D= (D&1)
    have c2 : Dioph fun w : Vector3 ℕ 3 => ∀ i < (w &2).unpair.2,
        Nat.beta (w &0) (i + 1)
          = g (Nat.pair ((w &2).unpair.1) (Nat.pair i (Nat.beta (w &0) i))) := by
      refine bddForall_dioph (R := fun i w => Nat.beta (w &0) (i + 1)
        = g (Nat.pair ((w &2).unpair.1) (Nat.pair i (Nat.beta (w &0) i)))) ?_ (unpair2_dioph (D&2))
      have h : Dioph fun u : Vector3 ℕ 4 => Nat.beta (u &1) (u &0 + 1)
          = g (Nat.pair ((u &3).unpair.1) (Nat.pair (u &0) (Nat.beta (u &1) (u &0)))) :=
        (beta_dioph (D&1) ((D&0) D+ (D.1))) D=
          (comp1_dioph ihg (pairFn_dioph (unpair1_dioph (D&3))
            (pairFn_dioph (D&0) (beta_dioph (D&1) (D&0)))))
      exact h
    refine Dioph.ext ((D∃) 2 (c1 D∧ c2 D∧ c3)) fun v => ?_
    show (∃ c, Nat.beta c 0 = f ((v &1).unpair.1) ∧
        (∀ i < (v &1).unpair.2, Nat.beta c (i + 1)
          = g (Nat.pair ((v &1).unpair.1) (Nat.pair i (Nat.beta c i)))) ∧
        Nat.beta c ((v &1).unpair.2) = v &0) ↔ _
    exact (prec_graph ((v &1).unpair.1) ((v &1).unpair.2) (v &0)).symm

end CS

import RequestProject.Hilbert10.Product

/-!
# Tools for the Davis–Putnam–Robinson theorem

Auxiliary results used in the elimination of bounded universal quantifiers:

* growth and congruence properties of Mathlib's `Poly`;
* the descending factorial as a product;
* divisibility by a product of pairwise coprime numbers;
* coprimality of the Gödel moduli `1 + c ! * k`;
* closure of Diophantine sets under finite conjunctions and of Diophantine functions under
  finite sums.
-/

namespace CS

open Finset Dioph

/-! ## Polynomials -/

/-- Every `Poly` is bounded by `C * (t+1) ^ D` on arguments bounded by `t`. -/
theorem poly_bound {α : Type} (p : Poly α) :
    ∃ C D : ℕ, ∀ (u : α → ℕ) (t : ℕ), (∀ i, u i ≤ t) → (p u).natAbs ≤ C * (t + 1) ^ D := by
  induction p using Poly.induction with
  | H1 i =>
    refine ⟨1, 1, fun u t ht => ?_⟩
    simp only [Poly.proj_apply]
    calc (u i : ℤ).natAbs = u i := by simp
      _ ≤ t := ht i
      _ ≤ 1 * (t + 1) ^ 1 := by simp
  | H2 n => exact ⟨n.natAbs, 0, fun u t _ => by simp [Poly.const_apply]⟩
  | H3 f g hf hg =>
    obtain ⟨C₁, D₁, h₁⟩ := hf
    obtain ⟨C₂, D₂, h₂⟩ := hg
    refine ⟨C₁ + C₂, max D₁ D₂, fun u t ht => ?_⟩
    have e1 := h₁ u t ht
    have e2 := h₂ u t ht
    have hle1 : C₁ * (t + 1) ^ D₁ ≤ C₁ * (t + 1) ^ (max D₁ D₂) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
    have hle2 : C₂ * (t + 1) ^ D₂ ≤ C₂ * (t + 1) ^ (max D₁ D₂) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
    calc ((f - g) u).natAbs ≤ (f u).natAbs + (g u).natAbs := by
          rw [Poly.sub_apply]; exact Int.natAbs_sub_le _ _
      _ ≤ C₁ * (t + 1) ^ (max D₁ D₂) + C₂ * (t + 1) ^ (max D₁ D₂) := by omega
      _ = (C₁ + C₂) * (t + 1) ^ (max D₁ D₂) := by ring
  | H4 f g hf hg =>
    obtain ⟨C₁, D₁, h₁⟩ := hf
    obtain ⟨C₂, D₂, h₂⟩ := hg
    refine ⟨C₁ * C₂, D₁ + D₂, fun u t ht => ?_⟩
    rw [Poly.mul_apply, Int.natAbs_mul]
    calc (f u).natAbs * (g u).natAbs ≤ (C₁ * (t + 1) ^ D₁) * (C₂ * (t + 1) ^ D₂) :=
          Nat.mul_le_mul (h₁ u t ht) (h₂ u t ht)
      _ = C₁ * C₂ * (t + 1) ^ (D₁ + D₂) := by ring

/-- Polynomials respect congruences. -/
theorem poly_intModEq {α : Type} (p : Poly α) {q : ℕ} {u u' : α → ℕ}
    (h : ∀ i, (u i : ℤ) ≡ (u' i : ℤ) [ZMOD (q : ℤ)]) : (p u : ℤ) ≡ p u' [ZMOD (q : ℤ)] := by
  induction p using Poly.induction with
  | H1 i => simpa using h i
  | H2 n => simp [Poly.const_apply]
  | H3 f g hf hg => simpa [Poly.sub_apply] using hf.sub hg
  | H4 f g hf hg => simpa [Poly.mul_apply] using hf.mul hg

/-! ## Elementary number theory -/

/-- The descending factorial as a product. -/
theorem descFactorial_eq_prod (X : ℕ) : ∀ k, X.descFactorial k = ∏ s ∈ range k, (X - s) := by
  intro k
  induction k with
  | zero => simp
  | succ n ih => rw [Nat.descFactorial_succ, Finset.prod_range_succ, ih]; ring

/-- A product of pairwise coprime numbers, each dividing `z`, divides `z`. -/
theorem nat_prod_dvd_of_coprime {ι : Type*} {s : Finset ι} {f : ι → ℕ} {z : ℕ}
    (hcop : (s : Set ι).Pairwise (Function.onFun Nat.Coprime f)) (hdvd : ∀ i ∈ s, f i ∣ z) :
    (∏ i ∈ s, f i) ∣ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcs : (s : Set ι).Pairwise (Function.onFun Nat.Coprime f) :=
      hcop.mono (by simp [Finset.coe_insert, Set.subset_insert])
    have h1 : f a ∣ z := hdvd a (by simp)
    have h2 : (∏ i ∈ s, f i) ∣ z := ih hcs fun i hi => hdvd i (by simp [hi])
    have h3 : Nat.Coprime (f a) (∏ i ∈ s, f i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop (by simp) (by simp [hi]) (by rintro rfl; exact ha hi)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h3 h1 h2

/-- Gödel's moduli `1 + c ! * k` are pairwise coprime for `1 ≤ k ≤ c`. -/
theorem moduli_coprime_lt {c k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hlc : l ≤ c) :
    Nat.Coprime (1 + Nat.factorial c * k) (1 + Nat.factorial c * l) := by
  set d := Nat.factorial c with hd
  by_contra hcop
  obtain ⟨q, hq, hdvd⟩ := Nat.exists_prime_and_dvd hcop
  have h1 : q ∣ 1 + d * k := hdvd.trans (Nat.gcd_dvd_left _ _)
  have h2 : q ∣ 1 + d * l := hdvd.trans (Nat.gcd_dvd_right _ _)
  have hqd : ¬ (q ∣ d) := by
    intro h
    have h4 : q ∣ (1 + d * k) - d * k := Nat.dvd_sub h1 (h.mul_right k)
    simp at h4
    exact hq.one_lt.ne' h4
  have h3 : q ∣ d * (l - k) := by
    have h5 := Nat.dvd_sub h2 h1
    have h6 : (1 + d * l) - (1 + d * k) = d * (l - k) := by rw [Nat.mul_sub]; omega
    rwa [h6] at h5
  rcases (Nat.Prime.dvd_mul hq).1 h3 with h | h
  · exact hqd h
  · have hle : q ≤ l - k := Nat.le_of_dvd (by omega) h
    exact hqd (Nat.dvd_factorial hq.pos (by omega))

/-- Symmetric version of `moduli_coprime_lt`. -/
theorem moduli_coprime {c k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hkc : k ≤ c) (hlc : l ≤ c)
    (hne : k ≠ l) : Nat.Coprime (1 + Nat.factorial c * k) (1 + Nat.factorial c * l) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact moduli_coprime_lt hk h hlc
  · exact (moduli_coprime_lt hl h hkc).symm

/-! ## Diophantine closure properties -/

/-- Diophantine sets are closed under finite conjunctions. -/
theorem dioph_forall_fin {α : Type} : ∀ {m : ℕ} {S : Fin m → Set (α → ℕ)},
    (∀ j, Dioph (S j)) → Dioph {v | ∀ j, v ∈ S j} := by
  intro m
  induction m with
  | zero =>
    intro S _
    exact Dioph.of_no_dummies _ 0 fun _ => ⟨fun _ => rfl, fun _ j => j.elim0⟩
  | succ n ih =>
    intro S hS
    have h1 : Dioph (S 0) := hS 0
    have h2 : Dioph {v | ∀ j : Fin n, v ∈ S j.succ} := ih fun j => hS j.succ
    refine (h1.inter h2).ext fun v => ?_
    constructor
    · rintro ⟨hz, hrest⟩ j
      refine Fin.cases ?_ ?_ j
      · exact hz
      · intro i; exact hrest i
    · intro h
      exact ⟨h 0, fun j => h j.succ⟩

/-- Diophantine functions are closed under finite sums. -/
theorem finsum_dioph {α ι : Type} {s : Finset ι} {f : ι → (α → ℕ) → ℕ}
    (hf : ∀ i ∈ s, DiophFn (f i)) : DiophFn fun v => ∑ i ∈ s, f i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const_dioph (α := α) 0
  | insert a s ha ih =>
    have h1 : DiophFn (f a) := hf a (by simp)
    have h2 : DiophFn fun v => ∑ i ∈ s, f i v := ih fun i hi => hf i (by simp [hi])
    simpa [Finset.sum_insert ha] using h1 D+ h2

end CS

import RequestProject.Hilbert10.Choose

/-!
# Products of arithmetic progressions are Diophantine

Following Davis, the product `∏_{k=1}^{N} (a + b k)` is Diophantine: modulo a suitable modulus
`M` it equals `b ^ N * N ! * (q + N).choose N`, where `q` is an inverse-type solution of
`b q ≡ a [MOD M]`, and the product itself is smaller than `M`.

This is the ingredient that allows the modulus `∏_{k=1}^{N} (1 + k d)` of the Chinese remainder
coding used in the Davis–Putnam–Robinson theorem to be described Diophantinely.
-/

namespace CS

open Finset

/-- The product of an arithmetic progression, `∏_{k=1}^{N} (a + b k)`. -/
def prodLin (a b N : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 N, (a + b * k)

theorem prodLin_eq_prod (a b N : ℕ) : prodLin a b N = ∏ k ∈ Finset.Icc 1 N, (a + b * k) := rfl

theorem prod_modEq {ι : Type*} {s : Finset ι} {f g : ι → ℕ} {M : ℕ}
    (h : ∀ i ∈ s, f i ≡ g i [MOD M]) : (∏ i ∈ s, f i) ≡ ∏ i ∈ s, g i [MOD M] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Nat.ModEq.refl]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))

theorem prod_Icc_add (q : ℕ) : ∀ N, ∏ k ∈ Finset.Icc 1 N, (q + k) = (q + 1).ascFactorial N := by
  intro N
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.ascFactorial_succ]; ring

theorem prodLin_zero (a N : ℕ) : prodLin a 0 N = a ^ N := by
  simp [prodLin, Finset.prod_const, Nat.card_Icc]

/-- Davis' congruence for the product of an arithmetic progression. -/
theorem prodLin_modEq {a b N q M : ℕ} (h : b * q ≡ a [MOD M]) :
    prodLin a b N ≡ b ^ N * (Nat.factorial N * Nat.choose (q + N) N) [MOD M] := by
  have h1 : prodLin a b N ≡ ∏ k ∈ Finset.Icc 1 N, (b * (q + k)) [MOD M] := by
    refine prod_modEq fun k _ => ?_
    have hb : b * q + b * k = b * (q + k) := by ring
    rw [← hb]
    exact (h.add_right (b * k)).symm
  have h2 : ∏ k ∈ Finset.Icc 1 N, (b * (q + k)) = b ^ N * ∏ k ∈ Finset.Icc 1 N, (q + k) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]; simp
  have h3 : ∏ k ∈ Finset.Icc 1 N, (q + k) = Nat.factorial N * Nat.choose (q + N) N := by
    rw [prod_Icc_add, Nat.ascFactorial_eq_factorial_mul_choose]
  rw [← h3, ← h2]
  exact h1

theorem prodLin_lt {a b N : ℕ} (hb : 0 < b) : prodLin a b N < 1 + b * (a + b * N + 1) ^ N := by
  have h1 : prodLin a b N ≤ (a + b * N) ^ N := by
    calc prodLin a b N ≤ ∏ _k ∈ Finset.Icc 1 N, (a + b * N) := by
          refine Finset.prod_le_prod' fun k hk => ?_
          simp at hk
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hk.2) _
      _ = (a + b * N) ^ N := by rw [Finset.prod_const, Nat.card_Icc]; simp
  have h2 : (a + b * N) ^ N ≤ (a + b * N + 1) ^ N := Nat.pow_le_pow_left (by omega) N
  have h3 : (a + b * N + 1) ^ N ≤ b * (a + b * N + 1) ^ N := Nat.le_mul_of_pos_left _ hb
  omega

/-- Solvability of `b q ≡ a` modulo a number of the form `1 + b T`. -/
theorem exists_mul_modEq (a b T : ℕ) : ∃ q, b * q ≡ a [MOD 1 + b * T] := by
  set M := 1 + b * T with hM
  have hcop : Nat.Coprime b M := by
    have hg : Nat.gcd b M = Nat.gcd b 1 := by
      have hc : M = 1 + T * b := by rw [hM]; ring
      rw [hc]
      exact Nat.gcd_add_mul_right_right b 1 T
    simp [Nat.Coprime, hg]
  rcases eq_or_lt_of_le (show 1 ≤ M by omega) with h1 | h1
  · exact ⟨0, by rw [← h1]; exact Nat.modEq_one⟩
  · obtain ⟨m, _, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    refine ⟨a * m, ?_⟩
    have hbm : b * m ≡ 1 [MOD M] := by
      unfold Nat.ModEq
      rw [hm, Nat.mod_eq_of_lt h1]
    calc b * (a * m) = a * (b * m) := by ring
      _ ≡ a * 1 [MOD M] := Nat.ModEq.mul_left a hbm
      _ = a := by ring

/-- The Diophantine characterisation of `prodLin`. -/
theorem prodLin_iff {a b N z : ℕ} :
    prodLin a b N = z ↔
      (b = 0 ∧ z = a ^ N) ∨
      (0 < b ∧ ∃ q, b * q ≡ a [MOD 1 + b * (a + b * N + 1) ^ N] ∧
        z = (b ^ N * (Nat.factorial N * Nat.choose (q + N) N))
              % (1 + b * (a + b * N + 1) ^ N)) := by
  have main : ∀ q : ℕ, 0 < b → b * q ≡ a [MOD 1 + b * (a + b * N + 1) ^ N] →
      prodLin a b N = (b ^ N * (Nat.factorial N * Nat.choose (q + N) N))
        % (1 + b * (a + b * N + 1) ^ N) := by
    intro q hb hq
    have h := prodLin_modEq (N := N) (M := 1 + b * (a + b * N + 1) ^ N) hq
    calc prodLin a b N = prodLin a b N % (1 + b * (a + b * N + 1) ^ N) :=
          (Nat.mod_eq_of_lt (prodLin_lt hb)).symm
      _ = _ := h
  constructor
  · rintro rfl
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact Or.inl ⟨rfl, prodLin_zero a N⟩
    · obtain ⟨q, hq⟩ := exists_mul_modEq a b ((a + b * N + 1) ^ N)
      exact Or.inr ⟨hb, q, hq, main q hb hq⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hb, q, hq, rfl⟩)
    · exact prodLin_zero a N
    · exact main q hb hq

/-! ## Diophantine description -/

section Dioph

open Dioph Fin2 Vector3

/-- The product `∏_{k=1}^{N} (a + b k)` is a Diophantine function of `(a, b, N)`. -/
theorem prodLin_diophFn : DiophFn fun v : Vector3 ℕ 3 => prodLin (v &0) (v &1) (v &2) := by
  refine (diophFn_vec _).2 ?_
  -- variables: `&0` value, `&1` = a, `&2` = b, `&3` = N
  have hM : DiophFn fun v : Vector3 ℕ 4 => 1 + v &2 * (v &1 + v &2 * v &3 + 1) ^ (v &3) :=
    (D.1) D+ ((D&2) D* pow_dioph ((D&1) D+ ((D&2) D* (D&3)) D+ (D.1)) (D&3))
  -- after `(D∃) 4`: `&0` = q, `&1` = value, `&2` = a, `&3` = b, `&4` = N
  have hM' : DiophFn fun v : Vector3 ℕ 5 => 1 + v &3 * (v &2 + v &3 * v &4 + 1) ^ (v &4) :=
    (D.1) D+ ((D&3) D* pow_dioph ((D&2) D+ ((D&3) D* (D&4)) D+ (D.1)) (D&4))
  have hinner : Dioph fun v : Vector3 ℕ 5 =>
      (v &3 * v &0 ≡ v &2 [MOD 1 + v &3 * (v &2 + v &3 * v &4 + 1) ^ (v &4)]) ∧
      v &1 = (v &3 ^ (v &4) * (Nat.factorial (v &4) * Nat.choose (v &0 + v &4) (v &4)))
              % (1 + v &3 * (v &2 + v &3 * v &4 + 1) ^ (v &4)) :=
    (Dioph.modEq_dioph ((D&3) D* (D&0)) (D&2) hM') D∧
      ((D&1) D= ((pow_dioph (D&3) (D&4)) D*
        ((factorial_dioph (D&4)) D* (choose_dioph ((D&0) D+ (D&4)) (D&4)))) D% hM')
  have hbig : Dioph fun v : Vector3 ℕ 4 =>
      (v &2 = 0 ∧ v &0 = (v &1) ^ (v &3)) ∨
      (0 < v &2 ∧ ∃ q : ℕ,
        (v &2 * q ≡ v &1 [MOD 1 + v &2 * (v &1 + v &2 * v &3 + 1) ^ (v &3)]) ∧
        v &0 = (v &2 ^ (v &3) * (Nat.factorial (v &3) * Nat.choose (q + v &3) (v &3)))
                % (1 + v &2 * (v &1 + v &2 * v &3 + 1) ^ (v &3))) :=
    (((D&2) D= (D.0)) D∧ ((D&0) D= pow_dioph (D&1) (D&3))) D∨
      (((D.1) D≤ (D&2)) D∧ ((D∃) 4 hinner))
  refine hbig.ext fun v => ?_
  show ((v &2 = 0 ∧ v &0 = (v &1) ^ (v &3)) ∨
      (0 < v &2 ∧ ∃ q : ℕ,
        (v &2 * q ≡ v &1 [MOD 1 + v &2 * (v &1 + v &2 * v &3 + 1) ^ (v &3)]) ∧
        v &0 = (v &2 ^ (v &3) * (Nat.factorial (v &3) * Nat.choose (q + v &3) (v &3)))
                % (1 + v &2 * (v &1 + v &2 * v &3 + 1) ^ (v &3)))) ↔ _
  exact prodLin_iff.symm

section
variable {α : Type} {f g h : (α → ℕ) → ℕ}

/-- Diophantine functions are closed under `prodLin`. -/
theorem prodLin_dioph (df : DiophFn f) (dg : DiophFn g) (dh : DiophFn h) :
    DiophFn fun v => prodLin (f v) (g v) (h v) :=
  diophFn_comp prodLin_diophFn [f, g, h] ⟨df, dg, dh⟩

end

end Dioph

end CS

import Mathlib

/-!
# Basic tools for Hilbert's tenth problem

This file collects the elementary ingredients used in the proof that Hilbert's tenth problem is
undecidable:

* `CS.HaltSet`, an r.e. but non-computable set of natural numbers;
* `CS.dioph_exists_finite_poly`, saying that a Diophantine set can be presented by a polynomial
  with finitely many auxiliary variables;
* `CS.exists_mvPolynomial`, converting Mathlib's `Poly` into an `MvPolynomial`.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code Encodable Denumerable

/-! ## An r.e. but non-computable set of naturals -/

/-- The halting set, as a set of natural numbers: `HaltSet m` holds iff the `m`-th partial
recursive code halts on input `0`. -/
def HaltSet : ℕ → Prop := fun m => (eval (ofNat Code m) 0).Dom

theorem haltSet_re : REPred HaltSet :=
  (eval_part.comp (Computable.ofNat Code) (Computable.const 0)).dom_re

theorem haltSet_not_computable : ¬ ComputablePred HaltSet := by
  rintro ⟨inst, hc⟩
  have h2 : ComputablePred fun c : Code => HaltSet (encode c) :=
    ⟨fun c => inst _, hc.comp Computable.encode⟩
  exact ComputablePred.halting_problem 0
    (h2.of_eq fun c => by simp [HaltSet, Denumerable.ofNat_encode])

/-! ## Normalisation of Diophantine sets -/

/-- A polynomial over `α ⊕ β` only depends on finitely many of the `β`-variables. -/
theorem poly_finset_support {α β : Type} (p : Poly (α ⊕ β)) :
    ∃ (s : Finset β) (q : Poly (α ⊕ {b // b ∈ s})),
      ∀ (v : α → ℕ) (t : β → ℕ), q (Sum.elim v (fun b => t b.1)) = p (Sum.elim v t) := by
  classical
  induction p using Poly.induction with
  | H1 i =>
    cases i with
    | inl a => exact ⟨∅, Poly.proj (Sum.inl a), fun _ _ => rfl⟩
    | inr b => exact ⟨{b}, Poly.proj (Sum.inr ⟨b, Finset.mem_singleton_self b⟩), fun _ _ => rfl⟩
  | H2 n => exact ⟨∅, Poly.const n, fun _ _ => rfl⟩
  | H3 f g hf hg =>
    obtain ⟨s₁, q₁, h₁⟩ := hf
    obtain ⟨s₂, q₂, h₂⟩ := hg
    refine ⟨s₁ ∪ s₂,
      q₁.map (Sum.elim Sum.inl
          (fun b : {b // b ∈ s₁} => Sum.inr ⟨b.1, Finset.mem_union_left _ b.2⟩))
        - q₂.map (Sum.elim Sum.inl
          (fun b : {b // b ∈ s₂} => Sum.inr ⟨b.1, Finset.mem_union_right _ b.2⟩)),
      fun v t => ?_⟩
    rw [Poly.sub_apply, Poly.map_apply, Poly.map_apply]
    have e₁ : (Sum.elim v (fun b : {b // b ∈ s₁ ∪ s₂} => t b.1)) ∘
        (Sum.elim Sum.inl (fun b : {b // b ∈ s₁} => Sum.inr ⟨b.1, Finset.mem_union_left _ b.2⟩))
        = Sum.elim v (fun b : {b // b ∈ s₁} => t b.1) := by
      funext x; rcases x with a | b <;> rfl
    have e₂ : (Sum.elim v (fun b : {b // b ∈ s₁ ∪ s₂} => t b.1)) ∘
        (Sum.elim Sum.inl (fun b : {b // b ∈ s₂} => Sum.inr ⟨b.1, Finset.mem_union_right _ b.2⟩))
        = Sum.elim v (fun b : {b // b ∈ s₂} => t b.1) := by
      funext x; rcases x with a | b <;> rfl
    rw [e₁, e₂, h₁, h₂]
    rfl
  | H4 f g hf hg =>
    obtain ⟨s₁, q₁, h₁⟩ := hf
    obtain ⟨s₂, q₂, h₂⟩ := hg
    refine ⟨s₁ ∪ s₂,
      q₁.map (Sum.elim Sum.inl
          (fun b : {b // b ∈ s₁} => Sum.inr ⟨b.1, Finset.mem_union_left _ b.2⟩))
        * q₂.map (Sum.elim Sum.inl
          (fun b : {b // b ∈ s₂} => Sum.inr ⟨b.1, Finset.mem_union_right _ b.2⟩)),
      fun v t => ?_⟩
    rw [Poly.mul_apply, Poly.map_apply, Poly.map_apply]
    have e₁ : (Sum.elim v (fun b : {b // b ∈ s₁ ∪ s₂} => t b.1)) ∘
        (Sum.elim Sum.inl (fun b : {b // b ∈ s₁} => Sum.inr ⟨b.1, Finset.mem_union_left _ b.2⟩))
        = Sum.elim v (fun b : {b // b ∈ s₁} => t b.1) := by
      funext x; rcases x with a | b <;> rfl
    have e₂ : (Sum.elim v (fun b : {b // b ∈ s₁ ∪ s₂} => t b.1)) ∘
        (Sum.elim Sum.inl (fun b : {b // b ∈ s₂} => Sum.inr ⟨b.1, Finset.mem_union_right _ b.2⟩))
        = Sum.elim v (fun b : {b // b ∈ s₂} => t b.1) := by
      funext x; rcases x with a | b <;> rfl
    rw [e₁, e₂, h₁, h₂]
    rfl

/-- Every Diophantine set of tuples can be presented by a polynomial with *finitely many*
auxiliary variables. -/
theorem dioph_exists_finite_poly {α : Type} {S : Set (α → ℕ)} (h : Dioph S) :
    ∃ (n : ℕ) (p : Poly (α ⊕ Fin n)), ∀ v, v ∈ S ↔ ∃ t : Fin n → ℕ, p (Sum.elim v t) = 0 := by
  classical
  obtain ⟨β, p, hp⟩ := h
  obtain ⟨s, q, hq⟩ := poly_finset_support p
  set e := Fintype.equivFin {b // b ∈ s} with he
  refine ⟨Fintype.card {b // b ∈ s},
    q.map (Sum.elim Sum.inl (fun b : {b // b ∈ s} => Sum.inr (e b))), fun v => ?_⟩
  have key : ∀ u : Fin (Fintype.card {b // b ∈ s}) → ℕ,
      (q.map (Sum.elim Sum.inl (fun b : {b // b ∈ s} => Sum.inr (e b)))) (Sum.elim v u)
        = q (Sum.elim v (fun b => u (e b))) := by
    intro u
    rw [Poly.map_apply]
    congr 1
    funext x; rcases x with a | b <;> rfl
  refine Iff.trans (hp v) ?_
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun j => t (e.symm j).1, ?_⟩
    rw [key]
    simpa using (hq v t).trans ht
  · rintro ⟨u, hu⟩
    refine ⟨fun b => if h : b ∈ s then u (e ⟨b, h⟩) else 0, ?_⟩
    rw [← hq v]
    rw [key] at hu
    simpa using hu

/-- Mathlib's `Poly` functions are exactly the evaluations of multivariate integer polynomials. -/
theorem exists_mvPolynomial {k : ℕ} (p : Poly (Fin k)) :
    ∃ P : MvPolynomial (Fin k) ℤ,
      ∀ v : Fin k → ℕ, MvPolynomial.eval (fun i => (v i : ℤ)) P = p v := by
  induction p using Poly.induction with
  | H1 i => exact ⟨MvPolynomial.X i, fun v => by simp⟩
  | H2 n => exact ⟨MvPolynomial.C n, fun v => by simp⟩
  | H3 f g hf hg =>
      obtain ⟨F, hF⟩ := hf
      obtain ⟨G, hG⟩ := hg
      exact ⟨F - G, fun v => by simp [hF, hG]⟩
  | H4 f g hf hg =>
      obtain ⟨F, hF⟩ := hf
      obtain ⟨G, hG⟩ := hg
      exact ⟨F * G, fun v => by simp [hF, hG]⟩

end CS

import RequestProject.Hilbert10.Basic
import RequestProject.Hilbert10.Primrec

/-!
# The MRDP theorem

The Matiyasevich–Robinson–Davis–Putnam theorem: every recursively enumerable set of natural
numbers is Diophantine.

The proof here goes through Mathlib's `evaln`: a recursively enumerable predicate `S` is the
projection `∃ k, G (pair k a) = 1` of the graph of a *primitive recursive* function `G` built
from `Nat.Partrec.Code.evaln`, and primitive recursive functions have Diophantine graphs
(`CS.dioph_of_primrec`), which in turn rests on Gödel's `β` function and the
Davis–Putnam–Robinson elimination of bounded universal quantifiers (`CS.bddForall_dioph`).
-/

namespace CS

open Dioph Nat Fin2 Vector3

/-- **MRDP theorem**: every recursively enumerable set of natural numbers is Diophantine. -/
theorem dioph_of_rePred {S : ℕ → Prop} (h : REPred S) : Dioph {v : Fin 1 → ℕ | S (v 0)} := by
  -- Turn the r.e. predicate into a partial recursive function and get a code for it.
  have hp : Nat.Partrec fun a : ℕ => (Part.assert (S a) fun _ => Part.some ()).map fun _ => 0 :=
    Partrec.nat_iff.1 (h.map (Computable.const 0).to₂)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hp
  -- The "step-indexed" evaluation function is primitive recursive.
  set G : ℕ → ℕ := fun m =>
    ((Nat.Partrec.Code.evaln m.unpair.1 c m.unpair.2).map fun _ => 1).getD 0 with hG
  have hGp : Nat.Primrec G := by
    refine Primrec.nat_iff.1 ?_
    have h2 : Primrec fun m : ℕ => Nat.Partrec.Code.evaln m.unpair.1 c m.unpair.2 :=
      (Nat.Partrec.Code.primrec_evaln.comp
        (((Primrec.fst.comp Primrec.unpair).pair (Primrec.const c)).pair
          (Primrec.snd.comp Primrec.unpair)) :)
    exact Primrec.option_getD.comp (Primrec.option_map h2 (Primrec.const 1).to₂)
      (Primrec.const 0)
  have key : ∀ a : ℕ, (∃ k, G (Nat.pair k a) = 1) ↔ S a := by
    intro a
    constructor
    · rintro ⟨k, hk⟩
      simp only [hG, Nat.unpair_pair] at hk
      rcases hev : Nat.Partrec.Code.evaln k c a with _ | x
      · simp [hev] at hk
      · have hx : x ∈ Nat.Partrec.Code.eval c a :=
          Nat.Partrec.Code.evaln_complete.2 ⟨k, hev⟩
        rw [hc] at hx
        simp only [Part.mem_map_iff, Part.mem_assert_iff] at hx
        tauto
    · intro hs
      have hx : (0 : ℕ) ∈ (Part.assert (S a) fun _ => Part.some ()).map fun _ => (0 : ℕ) :=
        (Part.mem_map_iff _).2 ⟨(), Part.mem_assert hs (Part.mem_some ()), rfl⟩
      have : (0 : ℕ) ∈ Nat.Partrec.Code.eval c a := by rw [hc]; exact hx
      obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 this
      exact ⟨k, by simp [hG, Option.mem_def.1 hk]⟩
  -- Assemble the Diophantine description.
  have dG : DiophFn fun v : Vector3 ℕ 1 => G (v &0) := dioph_of_primrec hGp
  have step : Dioph fun u : Vector3 ℕ 2 => G (Nat.pair (u &0) (u &1)) = 1 :=
    (comp1_dioph dG (pairFn_dioph (D&0) (D&1))) D= (D.1)
  have proj : Dioph fun v : Vector3 ℕ 1 => ∃ k, G (Nat.pair k (v &0)) = 1 :=
    Dioph.ext ((D∃) 1 step) fun _ => Iff.rfl
  have := reindex_dioph (Fin 1) (fun _ : Fin2 1 => (0 : Fin 1)) proj
  refine this.ext fun v => ?_
  show (∃ k, G (Nat.pair k (v 0)) = 1) ↔ S (v 0)
  exact key (v 0)

end CS

import RequestProject.Hilbert10.DPRTools

/-!
# The arithmetical core of the Davis–Putnam–Robinson theorem

Let `p` be a polynomial and consider the relation

`R i v ↔ ∃ t, p (i, v, t) = 0`.

The statement `∀ i < N, R i v` is equivalent to the existence of natural numbers `c, Y, K` and
`X : Fin m → ℕ` satisfying finitely many Diophantine conditions.  The idea (Davis, Putnam,
Robinson) is Chinese remaindering with the Gödel moduli `1 + c ! * k` (`1 ≤ k ≤ N`):

* `K` codes the sequence `0, 1, …, N-1` of values of the bounded variable; the single condition
  `M ∣ c ! * (K+1) + 1` (where `M = ∏ (1 + c ! * k)`) expresses `K ≡ k - 1` modulo each modulus;
* `X j` codes the sequence of `j`-th witnesses, all of which are `≤ Y`; the condition
  `M ∣ (Y+1)! * (X j).choose (Y+1)` says that each residue of `X j` is one of `0, …, Y`;
* `M ∣ |p (K, v, X)|` transfers the polynomial equation to every residue.

In the converse direction one picks a prime factor `q` of `1 + c ! * (i+1)`; all such prime
factors exceed `c`, which is chosen larger than every possible value of `|p|` on the relevant
range, so the congruence `p ≡ 0 (mod q)` forces the equation `p = 0` on the nose.
-/

namespace CS

open Finset Dioph

variable {n m : ℕ}

/-- **The core of the Davis–Putnam–Robinson theorem.** -/
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
theorem pair_dioph_set : Dioph fun v : Vector3 ℕ 3 => Nat.pair (v &0) (v &1) = v &2 := by
  have h : Dioph fun v : Vector3 ℕ 3 =>
      (v &0 < v &1 ∧ v &2 = v &1 * v &1 + v &0) ∨
        (v &1 ≤ v &0 ∧ v &2 = v &0 * v &0 + v &0 + v &1) :=
    (D&0 D< D&1 D∧ D&2 D= (D&1 D* D&1) D+ D&0) D∨
      (D&1 D≤ D&0 D∧ D&2 D= (D&0 D* D&0) D+ D&0 D+ D&1)
  refine h.ext fun v => ?_
  show ((v &0 < v &1 ∧ v &2 = v &1 * v &1 + v &0) ∨
      (v &1 ≤ v &0 ∧ v &2 = v &0 * v &0 + v &0 + v &1)) ↔ Nat.pair (v &0) (v &1) = v &2
  rw [Nat.pair]
  split_ifs with hlt <;> omega

/-- Cantor pairing is a Diophantine function. -/
theorem pair_diophFn : DiophFn fun v : Vector3 ℕ 2 => Nat.pair (v &0) (v &1) := by
  refine (diophFn_vec _).2 ?_
  have h : Dioph fun v : Vector3 ℕ 3 =>
      (v &1 < v &2 ∧ v &0 = v &2 * v &2 + v &1) ∨
        (v &2 ≤ v &1 ∧ v &0 = v &1 * v &1 + v &1 + v &2) :=
    (D&1 D< D&2 D∧ D&0 D= (D&2 D* D&2) D+ D&1) D∨
      (D&2 D≤ D&1 D∧ D&0 D= (D&1 D* D&1) D+ D&1 D+ D&2)
  refine h.ext fun v => ?_
  show ((v &1 < v &2 ∧ v &0 = v &2 * v &2 + v &1) ∨
      (v &2 ≤ v &1 ∧ v &0 = v &1 * v &1 + v &1 + v &2)) ↔ Nat.pair (v &1) (v &2) = v &0
  rw [Nat.pair]
  split_ifs with hlt <;> omega

/-- The first component of unpairing is a Diophantine function. -/
theorem unpair1_diophFn : DiophFn fun v : Vector3 ℕ 1 => (v &0).unpair.1 := by
  refine (diophFn_vec _).2 ?_
  have h : Dioph fun v : Vector3 ℕ 2 => ∃ b : ℕ, Nat.pair (v &0) b = v &1 :=
    Dioph.ext ((D∃) 2 (dioph_comp pair_dioph_set
      [fun w : Vector3 ℕ 3 => w &1, fun w => w &0, fun w => w &2] ⟨D&1, D&0, D&2⟩))
      fun _ => Iff.rfl
  refine h.ext fun v => ?_
  show (∃ b : ℕ, Nat.pair (v &0) b = v &1) ↔ (v &1).unpair.1 = v &0
  constructor
  · rintro ⟨b, hb⟩; rw [← hb, Nat.unpair_pair]
  · intro h; exact ⟨(v &1).unpair.2, by rw [← h, Nat.pair_unpair]⟩

/-- The second component of unpairing is a Diophantine function. -/
theorem unpair2_diophFn : DiophFn fun v : Vector3 ℕ 1 => (v &0).unpair.2 := by
  refine (diophFn_vec _).2 ?_
  have h : Dioph fun v : Vector3 ℕ 2 => ∃ a : ℕ, Nat.pair a (v &0) = v &1 :=
    Dioph.ext ((D∃) 2 (dioph_comp pair_dioph_set
      [fun w : Vector3 ℕ 3 => w &0, fun w => w &1, fun w => w &2] ⟨D&0, D&1, D&2⟩))
      fun _ => Iff.rfl
  refine h.ext fun v => ?_
  show (∃ a : ℕ, Nat.pair a (v &0) = v &1) ↔ (v &1).unpair.2 = v &0
  constructor
  · rintro ⟨a, ha⟩; rw [← ha, Nat.unpair_pair]
  · intro h; exact ⟨(v &1).unpair.1, by rw [← h, Nat.pair_unpair]⟩

section
variable {α : Type} {f g : (α → ℕ) → ℕ}

/-- Diophantine functions are closed under Cantor pairing. -/
theorem pairFn_dioph (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => Nat.pair (f v) (g v) := diophFn_comp2 df dg pair_diophFn

/-- Diophantine functions are closed under the first unpairing component. -/
theorem unpair1_dioph (df : DiophFn f) : DiophFn fun v => (f v).unpair.1 :=
  diophFn_comp unpair1_diophFn [f] df

/-- Diophantine functions are closed under the second unpairing component. -/
theorem unpair2_dioph (df : DiophFn f) : DiophFn fun v => (f v).unpair.2 :=
  diophFn_comp unpair2_diophFn [f] df

/-- Gödel's `β` function is Diophantine. -/
theorem beta_dioph (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => Nat.beta (f v) (g v) :=
  (unpair1_dioph df) D% (((dg D+ D.1) D* (unpair2_dioph df)) D+ D.1)

/-- Composition of a unary Diophantine function with a Diophantine function. -/
theorem comp1_dioph {F : ℕ → ℕ} (dF : DiophFn fun v : Vector3 ℕ 1 => F (v &0))
    (df : DiophFn f) : DiophFn fun v => F (f v) :=
  diophFn_comp dF [f] df

end

end CS

import RequestProject.Hilbert10.DPRCore
import RequestProject.Hilbert10.Basic

/-!
# The Davis–Putnam–Robinson theorem

Diophantine relations are closed under bounded universal quantification.  The arithmetic content
is `CS.dpr_core`; here it is turned into a statement about Diophantine sets by exhibiting the
Chinese remainder data (`c`, `Y`, `K` and the codes `X`) as extra existentially quantified
variables and each of the four conditions as a Diophantine condition on them.
-/

namespace CS

open Dioph Fin2 Vector3 Finset

/-- The four Diophantine conditions of the Davis–Putnam–Robinson coding. -/
def dprCond {n m : ℕ} (p : Poly (Fin2 (n + 1) ⊕ Fin m)) (C D : ℕ) (b : Vector3 ℕ n → ℕ)
    (c Y K : ℕ) (v : Vector3 ℕ n) (X : Fin m → ℕ) : Prop :=
  C * (b v + Y + (∑ a, v a) + 1) ^ D + (b v + Y + (∑ a, v a)) < c ∧
  prodLin 1 (Nat.factorial c) (b v) ∣ Nat.factorial c * (K + 1) + 1 ∧
  (∀ j, Y < X j ∧ prodLin 1 (Nat.factorial c) (b v) ∣
      Nat.factorial (Y + 1) * Nat.choose (X j) (Y + 1)) ∧
  prodLin 1 (Nat.factorial c) (b v) ∣ (p (Sum.elim (Vector3.cons K v) X)).natAbs

section

variable {n m : ℕ}

/-- The index type of the variables used in the coding: three scalars `c, Y, K`, the original
variables and the codes `X`. -/
private abbrev Idx (n m : ℕ) : Type := Option (Option (Option (Fin2 n ⊕ Fin m)))

private def vIdx (a : Fin2 n) : Idx n m := some (some (some (Sum.inl a)))

private def xIdx (j : Fin m) : Idx n m := some (some (some (Sum.inr j)))

/-- Reindexing of the polynomial `p` into the variables of the coding. -/
private def argIdx (n m : ℕ) : (Fin2 (n + 1) ⊕ Fin m) → Idx n m
  | Sum.inl z => Fin2.cases' (some (some none)) (fun a => vIdx a) z
  | Sum.inr j => xIdx j

/-- Each of the four conditions of `dprCond` is Diophantine in the coding variables. -/
private theorem dprCond_dioph (p : Poly (Fin2 (n + 1) ⊕ Fin m)) (C D : ℕ)
    {b : Vector3 ℕ n → ℕ} (db : DiophFn b) :
    Dioph {w : Idx n m → ℕ | dprCond p C D b (w none) (w (some none)) (w (some (some none)))
      (fun a => w (vIdx a)) (fun j => w (xIdx j))} := by
  have dc : DiophFn fun w : Idx n m → ℕ => w none := proj_dioph _
  have dY : DiophFn fun w : Idx n m → ℕ => w (some none) := proj_dioph _
  have dK : DiophFn fun w : Idx n m → ℕ => w (some (some none)) := proj_dioph _
  have dN : DiophFn fun w : Idx n m → ℕ => b (fun a => w (vIdx a)) :=
    reindex_diophFn (fun a : Fin2 n => (vIdx a : Idx n m)) db
  have dS : DiophFn fun w : Idx n m → ℕ => ∑ a : Fin2 n, w (vIdx a) :=
    finsum_dioph fun a _ => proj_dioph (vIdx a)
  have dd : DiophFn fun w : Idx n m → ℕ => Nat.factorial (w none) := factorial_dioph dc
  have dM : DiophFn fun w : Idx n m → ℕ =>
      prodLin 1 (Nat.factorial (w none)) (b fun a => w (vIdx a)) :=
    prodLin_dioph (const_dioph 1) dd dN
  have c1 : Dioph fun w : Idx n m → ℕ =>
      C * (b (fun a => w (vIdx a)) + w (some none) + (∑ a : Fin2 n, w (vIdx a)) + 1) ^ D
        + (b (fun a => w (vIdx a)) + w (some none) + (∑ a : Fin2 n, w (vIdx a))) < w none :=
    ((const_dioph C) D* (pow_dioph ((dN D+ dY D+ dS) D+ (D.1)) (const_dioph D))
      D+ (dN D+ dY D+ dS)) D< dc
  have c2 : Dioph fun w : Idx n m → ℕ =>
      prodLin 1 (Nat.factorial (w none)) (b fun a => w (vIdx a)) ∣
        Nat.factorial (w none) * (w (some (some none)) + 1) + 1 :=
    dvd_dioph dM ((dd D* (dK D+ (D.1))) D+ (D.1))
  have c3 : Dioph fun w : Idx n m → ℕ => ∀ j : Fin m,
      w (some none) < w (xIdx j) ∧
      prodLin 1 (Nat.factorial (w none)) (b fun a => w (vIdx a)) ∣
        Nat.factorial (w (some none) + 1) * Nat.choose (w (xIdx j)) (w (some none) + 1) := by
    refine dioph_forall_fin (S := fun j => {w : Idx n m → ℕ |
      w (some none) < w (xIdx j) ∧
      prodLin 1 (Nat.factorial (w none)) (b fun a => w (vIdx a)) ∣
        Nat.factorial (w (some none) + 1) * Nat.choose (w (xIdx j)) (w (some none) + 1)})
      fun j => ?_
    exact (dY D< (proj_dioph (xIdx j))) D∧
      dvd_dioph dM ((factorial_dioph (dY D+ (D.1))) D*
        (choose_dioph (proj_dioph (xIdx j)) (dY D+ (D.1))))
  have c4 : Dioph fun w : Idx n m → ℕ =>
      prodLin 1 (Nat.factorial (w none)) (b fun a => w (vIdx a)) ∣
        (p (Sum.elim (Vector3.cons (w (some (some none))) (fun a => w (vIdx a)))
          (fun j => w (xIdx j)))).natAbs := by
    have h := dvd_dioph dM (abs_poly_dioph (p.map (argIdx n m)))
    refine h.ext fun w => ?_
    have heq : (fun x => w (argIdx n m x)) =
        Sum.elim (Vector3.cons (w (some (some none))) (fun a => w (vIdx a)))
          (fun j => w (xIdx j)) := by
      funext x
      rcases x with z | j
      · cases z with
        | fz => rfl
        | fs a => rfl
      · rfl
    show (prodLin 1 (Nat.factorial (w none)) (b fun a => w (vIdx a)) ∣
        (p fun x => w (argIdx n m x)).natAbs) ↔ _
    rw [heq]
    exact Iff.rfl
  exact c1 D∧ c2 D∧ c3 D∧ c4

end

/-- **Davis–Putnam–Robinson**: Diophantine relations are closed under bounded universal
quantification. -/
theorem bddForall_dioph {n : ℕ} {R : ℕ → Vector3 ℕ n → Prop}
    (dR : Dioph fun u : Vector3 ℕ (n + 1) => R (u &0) (u ∘ fs))
    {b : Vector3 ℕ n → ℕ} (db : DiophFn b) :
    Dioph fun v : Vector3 ℕ n => ∀ i < b v, R i v := by
  classical
  obtain ⟨m, p, hp⟩ := dioph_exists_finite_poly dR
  obtain ⟨C, D, hCD⟩ := poly_bound p
  have hR : ∀ (i : ℕ) (v : Vector3 ℕ n),
      R i v ↔ ∃ t : Fin m → ℕ, p (Sum.elim (Vector3.cons i v) t) = 0 := by
    intro i v
    have h := hp (Vector3.cons i v)
    have e2 : (Vector3.cons i v) ∘ fs = v := funext fun j => rfl
    have e3 : R ((Vector3.cons i v) &0) ((Vector3.cons i v) ∘ fs) ↔ R i v := by
      rw [e2]; exact Iff.rfl
    exact e3.symm.trans h
  have step := ex_dioph (ex1_dioph (ex1_dioph (ex1_dioph (dprCond_dioph p C D db))))
  refine step.ext fun v => ?_
  constructor
  · rintro ⟨X, K, Y, c, hcond⟩
    have hcond' : dprCond p C D b c Y K v X := hcond
    intro i hi
    rw [hR i v]
    refine (dpr_core p C D hCD v (∑ a, v a) (fun a => Finset.single_le_sum
      (f := fun a : Fin2 n => v a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)) (b v)).2
      ⟨c, Y, K, X, hcond'.1, hcond'.2.1, hcond'.2.2.1, hcond'.2.2.2⟩ i hi
  · intro h
    have h' : ∀ i < b v, ∃ t : Fin m → ℕ, p (Sum.elim (Vector3.cons i v) t) = 0 := by
      intro i hi
      exact (hR i v).1 (h i hi)
    obtain ⟨c, Y, K, X, h1, h2, h3, h4⟩ :=
      (dpr_core p C D hCD v (∑ a, v a) (fun a => Finset.single_le_sum
        (f := fun a : Fin2 n => v a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)) (b v)).1 h'
    exact ⟨X, K, Y, c, ⟨h1, h2, h3, h4⟩⟩

end CS

import RequestProject.Hilbert10.DiophTools

/-!
# Binomial coefficients and factorials are Diophantine

Given that exponentiation is Diophantine (Matiyasevich's theorem, `Dioph.pow_dioph` in Mathlib),
binomial coefficients and factorials are Diophantine as well, by two classical formulas of
Julia Robinson:

* `Nat.choose n k` is the `k`-th digit of `(u+1)^n` written in base `u`, as soon as `u > 2^n`;
* `Nat.factorial n = r ^ n / Nat.choose r n` as soon as `r` is large enough compared with `n`.
-/

namespace CS

open Finset

/-! ## Digit extraction -/

/-- Reading off a digit of a number given by its base-`u` expansion. -/
theorem digit_extract {u : ℕ} (hu : 0 < u) (c : ℕ → ℕ) {N k : ℕ} (hk : k ≤ N)
    (hA : ∑ m ∈ range k, c m * u ^ m < u ^ k) (hck : c k < u) :
    (∑ m ∈ range (N + 1), c m * u ^ m) / u ^ k % u = c k := by
  have hupos : 0 < u ^ k := Nat.pow_pos hu
  obtain ⟨B, hB⟩ : ∃ B, ∑ m ∈ Ico (k + 1) (N + 1), c m * u ^ m = u ^ (k + 1) * B := by
    refine ⟨(∑ m ∈ Ico (k + 1) (N + 1), c m * u ^ m) / u ^ (k + 1), (Nat.mul_div_cancel' ?_).symm⟩
    refine Finset.dvd_sum fun m hm => ?_
    exact Dvd.dvd.mul_left (pow_dvd_pow u (by simp at hm; omega)) _
  have hsplit : ∑ m ∈ range (N + 1), c m * u ^ m
      = (∑ m ∈ range k, c m * u ^ m) + (c k + u * B) * u ^ k := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (by omega : k ≤ N + 1),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : k < N + 1), hB, ← Finset.range_eq_Ico]
    ring
  rw [hsplit, Nat.add_mul_div_right _ _ hupos, Nat.div_eq_of_lt hA]
  simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hck]

/-! ## Binomial coefficients -/

/-- **Julia Robinson's formula for binomial coefficients**: for `u > 2 ^ n`, the binomial
coefficient `n.choose k` is the `k`-th base-`u` digit of `(u+1) ^ n`. -/
theorem choose_eq_div_mod (n k : ℕ) {u : ℕ} (hu : 2 ^ n < u) :
    n.choose k = ((u + 1) ^ n / u ^ k) % u := by
  have hupos : 0 < u := lt_of_le_of_lt (Nat.zero_le _) hu
  have hbin : (u + 1) ^ n = ∑ m ∈ range (n + 1), n.choose m * u ^ m := by
    rw [add_pow]; simp [mul_comm]
  have hchoose : ∀ j, n.choose j < u := fun j => lt_of_le_of_lt (Nat.choose_le_two_pow n j) hu
  rcases le_or_gt k n with hk | hk
  · rw [hbin]
    refine (digit_extract hupos (fun m => n.choose m) hk ?_ (hchoose k)).symm
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hsub : range (j + 1) ⊆ range (n + 1) := by
        intro x hx; simp at hx ⊢; omega
      calc ∑ m ∈ range (j + 1), n.choose m * u ^ m
          ≤ ∑ m ∈ range (j + 1), n.choose m * u ^ j := by
            refine Finset.sum_le_sum fun m hm => ?_
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hupos (by simp at hm; omega))
        _ = (∑ m ∈ range (j + 1), n.choose m) * u ^ j := by rw [Finset.sum_mul]
        _ ≤ 2 ^ n * u ^ j := by
            refine Nat.mul_le_mul_right _ ?_
            calc ∑ m ∈ range (j + 1), n.choose m
                ≤ ∑ m ∈ range (n + 1), n.choose m := Finset.sum_le_sum_of_subset hsub
              _ = 2 ^ n := Nat.sum_range_choose n
        _ < u ^ (j + 1) := by
            rw [pow_succ, mul_comm (u ^ j) u]
            exact (Nat.mul_lt_mul_right (Nat.pow_pos hupos)).2 hu
  · rw [Nat.choose_eq_zero_of_lt hk, Nat.div_eq_of_lt, Nat.zero_mod]
    calc (u + 1) ^ n = ∑ m ∈ range (n + 1), n.choose m * u ^ m := hbin
      _ ≤ ∑ m ∈ range (n + 1), n.choose m * u ^ n := by
          refine Finset.sum_le_sum fun m hm => ?_
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hupos (by simp at hm; omega))
      _ = 2 ^ n * u ^ n := by rw [← Finset.sum_mul, Nat.sum_range_choose]
      _ < u ^ (n + 1) := by
          rw [pow_succ, mul_comm (u ^ n) u]
          exact (Nat.mul_lt_mul_right (Nat.pow_pos hupos)).2 hu
      _ ≤ u ^ k := Nat.pow_le_pow_right hupos hk

/-! ## Factorials -/

/-- An upper bound for `r ^ (n+1)` in terms of the descending factorial. -/
theorem pow_le_descFactorial_aux : ∀ (n r : ℕ), n ≤ r →
    r ^ (n + 1) ≤ r * r.descFactorial n + n * n * r ^ n := by
  intro n
  induction n with
  | zero => intro r _; simp
  | succ n ih =>
    intro r hr
    have h1 := ih r (by omega)
    have hd : r.descFactorial n ≤ r ^ n := Nat.descFactorial_le_pow r n
    have h2 : r * r.descFactorial n * r ≤ r * r.descFactorial (n + 1) + n * r ^ (n + 1) := by
      rw [Nat.descFactorial_succ]
      have e1 : (r - n) * r.descFactorial n + n * r.descFactorial n = r * r.descFactorial n := by
        rw [← Nat.add_mul]; congr 1; omega
      have hn : n * (r * r.descFactorial n) ≤ n * r ^ (n + 1) := by
        refine Nat.mul_le_mul_left _ ?_
        calc r * r.descFactorial n ≤ r * r ^ n := Nat.mul_le_mul_left _ hd
          _ = r ^ (n + 1) := by ring
      calc r * r.descFactorial n * r
          = r * ((r - n) * r.descFactorial n + n * r.descFactorial n) := by rw [e1]; ring
        _ = r * ((r - n) * r.descFactorial n) + n * (r * r.descFactorial n) := by ring
        _ ≤ r * ((r - n) * r.descFactorial n) + n * r ^ (n + 1) := by omega
    calc r ^ (n + 2) = r ^ (n + 1) * r := by ring
      _ ≤ (r * r.descFactorial n + n * n * r ^ n) * r := Nat.mul_le_mul_right _ h1
      _ = r * r.descFactorial n * r + n * n * r ^ (n + 1) := by ring
      _ ≤ (r * r.descFactorial (n + 1) + n * r ^ (n + 1)) + n * n * r ^ (n + 1) := by omega
      _ ≤ r * r.descFactorial (n + 1) + (n + 1) * (n + 1) * r ^ (n + 1) := by
          nlinarith [Nat.zero_le (r ^ (n + 1))]

/-- A lower bound for the descending factorial. -/
theorem pow_sub_le_descFactorial (r : ℕ) : ∀ n, (r - n) ^ n ≤ r.descFactorial n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.descFactorial_succ]
    have hmono : (r - (n + 1)) ^ n ≤ (r - n) ^ n := Nat.pow_le_pow_left (by omega) n
    calc (r - (n + 1)) ^ (n + 1) = (r - (n + 1)) * (r - (n + 1)) ^ n := by ring
      _ ≤ (r - n) * r.descFactorial n :=
          Nat.mul_le_mul (by omega) (le_trans hmono ih)

/-- **Julia Robinson's formula for the factorial**: for `r` large compared with `n`,
`Nat.factorial n = r ^ n / (r.choose n)`. -/
theorem factorial_eq_div {n r : ℕ} (hr : 2 ^ n * n ^ (n + 2) < r) :
    Nat.factorial n = r ^ n / r.choose n := by
  have hdesc : r.descFactorial n = Nat.factorial n * r.choose n := Nat.descFactorial_eq_factorial_mul_choose r n
  refine (Nat.div_eq_of_lt_le ?_ ?_).symm
  · rw [← hdesc]; exact Nat.descFactorial_le_pow r n
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hrpos : 0 < r := by omega
    have h2n : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hnn : n ≤ n ^ (n + 2) := by
      calc n = n ^ 1 := (pow_one n).symm
        _ ≤ n ^ (n + 2) := Nat.pow_le_pow_right hn (by omega)
    have h2r : 2 * n ≤ r := by nlinarith
    have hnr : n ≤ r := by omega
    -- the key inequality `n * n * r ^ n < r * r.choose n`
    have hkey : n * n * r ^ n < r * r.choose n := by
      refine lt_of_mul_lt_mul_right ?_ (Nat.zero_le (n ^ n * 2 ^ n))
      have hchoose_lb : r ^ n ≤ r.choose n * (n ^ n * 2 ^ n) := by
        have h1 : (r - n) ^ n * 2 ^ n ≥ r ^ n := by
          have : r ≤ 2 * (r - n) := by omega
          calc r ^ n ≤ (2 * (r - n)) ^ n := Nat.pow_le_pow_left this n
            _ = (r - n) ^ n * 2 ^ n := by rw [mul_pow]; ring
        have h2 : (r - n) ^ n ≤ r.choose n * n ^ n := by
          calc (r - n) ^ n ≤ r.descFactorial n := pow_sub_le_descFactorial r n
            _ = Nat.factorial n * r.choose n := hdesc
            _ ≤ n ^ n * r.choose n := Nat.mul_le_mul_right _ (Nat.factorial_le_pow n)
            _ = r.choose n * n ^ n := by ring
        calc r ^ n ≤ (r - n) ^ n * 2 ^ n := h1
          _ ≤ (r.choose n * n ^ n) * 2 ^ n := Nat.mul_le_mul_right _ h2
          _ = r.choose n * (n ^ n * 2 ^ n) := by ring
      calc n * n * r ^ n * (n ^ n * 2 ^ n)
          = (2 ^ n * n ^ (n + 2)) * r ^ n := by ring
        _ < r * r ^ n := by
            exact (Nat.mul_lt_mul_right (Nat.pow_pos hrpos)).2 hr
        _ ≤ r * (r.choose n * (n ^ n * 2 ^ n)) := Nat.mul_le_mul_left _ hchoose_lb
        _ = r * r.choose n * (n ^ n * 2 ^ n) := by ring
    have haux := pow_le_descFactorial_aux n r hnr
    have hfinal : r ^ (n + 1) < r * (Nat.factorial n * r.choose n) + r * r.choose n := by
      calc r ^ (n + 1) ≤ r * r.descFactorial n + n * n * r ^ n := haux
        _ < r * r.descFactorial n + r * r.choose n := by omega
        _ = r * (Nat.factorial n * r.choose n) + r * r.choose n := by rw [hdesc]
    have : r * r ^ n < r * ((Nat.factorial n + 1) * r.choose n) := by
      calc r * r ^ n = r ^ (n + 1) := by ring
        _ < r * (Nat.factorial n * r.choose n) + r * r.choose n := hfinal
        _ = r * ((Nat.factorial n + 1) * r.choose n) := by ring
    exact lt_of_mul_lt_mul_left this (Nat.zero_le r)

/-! ## Diophantine descriptions -/

section Dioph

open Dioph Fin2 Vector3

/-- The binomial coefficient is a Diophantine function. -/
theorem choose_diophFn : DiophFn fun v : Vector3 ℕ 2 => Nat.choose (v &0) (v &1) := by
  have key : (fun v : Vector3 ℕ 2 => Nat.choose (v &0) (v &1))
      = fun v : Vector3 ℕ 2 =>
        ((2 ^ (v &0) + 1 + 1) ^ (v &0) / (2 ^ (v &0) + 1) ^ (v &1)) % (2 ^ (v &0) + 1) :=
    funext fun v => choose_eq_div_mod (v &0) (v &1) (Nat.lt_succ_self _)
  rw [key]
  have hu : DiophFn fun v : Vector3 ℕ 2 => 2 ^ (v &0) + 1 := pow_dioph (D.2) (D&0) D+ (D.1)
  exact (pow_dioph (hu D+ (D.1)) (D&0)) D/ (pow_dioph hu (D&1)) D% hu

section
variable {α : Type} {f g : (α → ℕ) → ℕ}

/-- Diophantine functions are closed under binomial coefficients. -/
theorem choose_dioph (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => Nat.choose (f v) (g v) := diophFn_comp2 df dg choose_diophFn

end

/-- The factorial is a Diophantine function. -/
theorem factorial_diophFn : DiophFn fun v : Vector3 ℕ 1 => Nat.factorial (v &0) := by
  have key : (fun v : Vector3 ℕ 1 => Nat.factorial (v &0))
      = fun v : Vector3 ℕ 1 =>
        (2 ^ (v &0) * (v &0) ^ (v &0 + 2) + 1) ^ (v &0)
          / Nat.choose (2 ^ (v &0) * (v &0) ^ (v &0 + 2) + 1) (v &0) :=
    funext fun v => factorial_eq_div (Nat.lt_succ_self _)
  rw [key]
  have hr : DiophFn fun v : Vector3 ℕ 1 => 2 ^ (v &0) * (v &0) ^ (v &0 + 2) + 1 :=
    (pow_dioph (D.2) (D&0)) D* (pow_dioph (D&0) ((D&0) D+ (D.2))) D+ (D.1)
  exact (pow_dioph hr (D&0)) D/ (choose_dioph hr (D&0))

/-- Diophantine functions are closed under the factorial. -/
theorem factorial_dioph {α : Type} {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    DiophFn fun v => Nat.factorial (f v) := comp1_dioph factorial_diophFn df

end Dioph

end CS

