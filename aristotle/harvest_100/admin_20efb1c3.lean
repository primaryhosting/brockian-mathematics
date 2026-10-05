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
def prodAB (a b y : ℕ) : ℕ := ∏ k ∈ range y, (a + b * (k + 1))

theorem prodAB_zero (a y : ℕ) : prodAB a 0 y = a ^ y := by simp [prodAB]

theorem prodAB_le (a b y : ℕ) : prodAB a b y ≤ (a + b * y + 1) ^ y := by
  calc prodAB a b y ≤ ∏ _k ∈ range y, (a + b * y + 1) := by
        refine Finset.prod_le_prod' ?_
        intro i hi
        simp only [mem_range] at hi
        nlinarith [hi]
    _ = (a + b * y + 1) ^ y := by simp

theorem modEq_prod {N : ℕ} (y : ℕ) (f g : ℕ → ℕ) (h : ∀ k, f k ≡ g k [MOD N]) :
    ∏ k ∈ range y, f k ≡ ∏ k ∈ range y, g k [MOD N] := by
  induction y with
  | zero => simp; rfl
  | succ y ih => rw [prod_range_succ, prod_range_succ]; exact ih.mul (h y)

/-- The key congruence: the product is determined modulo a large `N` by a binomial
coefficient. -/
theorem prodAB_eq (a b y m : ℕ) (N : ℕ) (hN : (a + b * y + 1) ^ y < N)
    (hm : b * m ≡ a [MOD N]) :
    prodAB a b y = (b ^ y * (y ! * (m + y).choose y)) % N := by
  have hlt : prodAB a b y < N := lt_of_le_of_lt (prodAB_le a b y) hN
  have h1 : prodAB a b y ≡ ∏ k ∈ range y, (b * m + b * (k + 1)) [MOD N] :=
    modEq_prod y _ _ (fun _ => Nat.ModEq.add_right _ hm.symm)
  have h2 : ∏ k ∈ range y, (b * m + b * (k + 1)) = b ^ y * ∏ k ∈ range y, (m + k + 1) := by
    rw [show (b ^ y : ℕ) = ∏ _k ∈ range y, b by simp, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (by intros; ring)
  have h3 : ∏ k ∈ range y, (m + k + 1) = y ! * (m + y).choose y := by
    have h : ∏ k ∈ range y, (m + k + 1) = (m + 1).ascFactorial y := by
      rw [Nat.ascFactorial_eq_prod_range]
      exact Finset.prod_congr rfl (by intros; ring_nf)
    rw [h, Nat.ascFactorial_eq_factorial_mul_choose]
  rw [h2, h3] at h1
  have h4 := h1.symm
  unfold Nat.ModEq at h4
  rw [h4, Nat.mod_eq_of_lt hlt]

/-- The three-variable version: `prodAB` is a Diophantine function. -/
theorem dioph_prodAB3 : DiophFn fun v : Vector3 ℕ 3 => prodAB (v &0) (v &1) (v &2) := by
  have dN : DiophFn fun v : Vector3 ℕ 5 => v &3 * ((v &2 + v &3 * v &4 + 1) ^ (v &4) + 1) + 1 :=
    ((D&3) D* ((pow_dioph (((D&2) D+ ((D&3) D* (D&4))) D+ (D.1)) (D&4)) D+ (D.1))) D+ (D.1)
  have inner : Dioph {v : Vector3 ℕ 5 |
      (v &3 * v &0 ≡ v &2 [MOD (v &3 * ((v &2 + v &3 * v &4 + 1) ^ (v &4) + 1) + 1)]) ∧
      v &1 = (v &3 ^ v &4 * ((v &4)! * (v &0 + v &4).choose (v &4)))
        % (v &3 * ((v &2 + v &3 * v &4 + 1) ^ (v &4) + 1) + 1) } :=
    (D≡ ((D&3) D* (D&0)) (D&2) dN) D∧
      ((D&1) D= ((pow_dioph (D&3) (D&4) D* (dioph_factorial (D&4) D*
        dioph_choose ((D&0) D+ (D&4)) (D&4))) D% dN))
  have big : Dioph {v : Vector3 ℕ 4 |
      (v &2 = 0 ∧ v &0 = v &1 ^ v &3) ∨ (0 < v &2 ∧ ∃ m : ℕ,
        (v &2 * m ≡ v &1 [MOD (v &2 * ((v &1 + v &2 * v &3 + 1) ^ (v &3) + 1) + 1)]) ∧
        v &0 = (v &2 ^ v &3 * ((v &3)! * (m + v &3).choose (v &3)))
          % (v &2 * ((v &1 + v &2 * v &3 + 1) ^ (v &3) + 1) + 1)) } :=
    (((D&2) D= (D.0)) D∧ ((D&0) D= (pow_dioph (D&1) (D&3)))) D∨
      (((D.0) D< (D&2)) D∧ ((D∃) 4 inner))
  refine (diophFn_vec _).2 <| Dioph.ext big <| (vectorAll_iff_forall _).1 fun P a b y => ?_
  show ((b = 0 ∧ P = a ^ y) ∨ (0 < b ∧ ∃ m : ℕ,
      (b * m ≡ a [MOD (b * ((a + b * y + 1) ^ y + 1) + 1)]) ∧
      P = (b ^ y * (y ! * (m + y).choose y)) % (b * ((a + b * y + 1) ^ y + 1) + 1)))
    ↔ prodAB a b y = P
  set N := b * ((a + b * y + 1) ^ y + 1) + 1 with hNdef
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨hb, m, hm, rfl⟩)
    · exact prodAB_zero a y
    · refine prodAB_eq a b y m N ?_ hm
      have : 1 ≤ b := hb
      nlinarith [Nat.one_le_iff_ne_zero.mpr (pow_ne_zero y (show a + b * y + 1 ≠ 0 by omega))]
  · rintro rfl
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact Or.inl ⟨rfl, prodAB_zero a y⟩
    · refine Or.inr ⟨hb, ?_⟩
      have hNlt : (a + b * y + 1) ^ y < N := by
        have : 1 ≤ b := hb
        nlinarith [Nat.one_le_iff_ne_zero.mpr (pow_ne_zero y (show a + b * y + 1 ≠ 0 by omega))]
      have hN1 : 1 < N := by
        have : 1 ≤ (a + b * y + 1) ^ y := Nat.one_le_pow _ _ (by omega)
        omega
      have hcop : Nat.Coprime b N := by
        rw [hNdef]; simp [Nat.coprime_mul_left_add_right]
      obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hN1
      refine ⟨m' * a, ?_, prodAB_eq a b y (m' * a) N hNlt ?_⟩ <;>
      · have : b * (m' * a) = (b * m') * a := by ring
        rw [this]
        calc (b * m') * a ≡ 1 * a [MOD N] :=
              Nat.ModEq.mul_right a (by unfold Nat.ModEq; rw [Nat.mod_eq_of_lt hN1]; exact hm')
          _ = a := one_mul a

end H10

import Mathlib

/-!
# Base-`B` digits

Extraction of the `k`-th base-`B` digit of a number, and the fact that the digits of
`∑ i ∈ range n, c i * B ^ i` are the `c i`, provided `c i < B`.

This is used both for the Diophantine definition of binomial coefficients and for coding
finite sequences (traces of primitive recursive computations) by a single number.
-/

namespace H10

open Finset

/-- The `k`-th digit of `S` in base `B`. -/
def digit (S B k : ℕ) : ℕ := S / B ^ k % B

theorem digit_lt {S B k : ℕ} (hB : 0 < B) : digit S B k < B := Nat.mod_lt _ hB

theorem sum_lt_pow {B : ℕ} (c : ℕ → ℕ) (hc : ∀ i, c i < B) (k : ℕ) :
    ∑ i ∈ range k, c i * B ^ i < B ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    calc ∑ i ∈ range k, c i * B ^ i + c k * B ^ k
        < B ^ k + c k * B ^ k := by omega
      _ = (c k + 1) * B ^ k := by ring
      _ ≤ B * B ^ k := Nat.mul_le_mul_right _ (hc k)
      _ = B ^ k * B := by ring

/-- The digits of a digit sum are the given coefficients. -/
theorem digit_ofSum (B : ℕ) (c : ℕ → ℕ) (hc : ∀ i, c i < B) (n k : ℕ) :
    digit (∑ i ∈ range n, c i * B ^ i) B k = if k < n then c k else 0 := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hc 0)
  rcases lt_or_ge k n with hkn | hkn
  · rw [if_pos hkn]
    obtain ⟨d, rfl⟩ : ∃ d, n = k + (d + 1) := ⟨n - k - 1, by omega⟩
    rw [Finset.sum_range_add]
    have h2 : ∑ i ∈ range (d + 1), c (k + i) * B ^ (k + i)
        = B ^ k * (c k + B * ∑ i ∈ range d, c (k + 1 + i) * B ^ i) := by
      rw [Finset.sum_range_succ']
      simp [pow_add, Finset.mul_sum, mul_add, mul_comm, mul_left_comm, mul_assoc,
        pow_succ, add_comm, add_left_comm]
    rw [h2, digit, Nat.add_mul_div_left _ _ (Nat.pow_pos hB),
      Nat.div_eq_of_lt (sum_lt_pow c hc k)]
    simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hc k)]
  · rw [if_neg (by omega)]
    have : ∑ i ∈ range n, c i * B ^ i < B ^ k :=
      lt_of_lt_of_le (sum_lt_pow c hc n) (Nat.pow_le_pow_right hB hkn)
    simp [digit, Nat.div_eq_of_lt this]

/-- Binomial coefficients are the base-`u` digits of `(u+1)^n`, for `u` large. -/
theorem choose_eq_digit (n k u : ℕ) (hu : 2 ^ n < u) :
    n.choose k = digit ((u + 1) ^ n) u k := by
  have hexp : (u + 1) ^ n = ∑ i ∈ range (n + 1), n.choose i * u ^ i := by
    rw [add_pow]; simp [mul_comm]
  have hlt : ∀ i, n.choose i < u := fun i => lt_of_le_of_lt (Nat.choose_le_two_pow n i) hu
  rw [hexp, digit_ofSum u _ hlt]
  by_cases h : k < n + 1
  · rw [if_pos h]
  · rw [if_neg h, Nat.choose_eq_zero_of_lt (by omega)]

end H10

import Mathlib

/-!
# Auxiliary facts about `Poly` and `Dioph`

* `isPoly_support`: a polynomial depends on finitely many variables;
* `isPoly_majorant`: a polynomial is dominated by a monotone polynomial;
* `isPoly_modEq`: polynomials respect congruences;
* `dioph_fin_dummies`: a Diophantine set can be defined using finitely many dummy variables.
-/

namespace H10

open Dioph

local infixr:65 " ⊗ " => Sum.elim

/-- A polynomial depends only on finitely many of its variables. -/
theorem isPoly_support {γ : Type} {p : (γ → ℕ) → ℤ} (hp : IsPoly p) :
    ∃ s : Finset γ, ∀ v w : γ → ℕ, (∀ i ∈ s, v i = w i) → p v = p w := by
  classical
  induction hp with
  | proj i =>
      refine ⟨{i}, fun v w h => ?_⟩
      dsimp only
      rw [h i (Finset.mem_singleton_self i)]
  | const n => exact ⟨∅, fun _ _ _ => rfl⟩
  | sub _ _ ih1 ih2 =>
      obtain ⟨s1, h1⟩ := ih1; obtain ⟨s2, h2⟩ := ih2
      refine ⟨s1 ∪ s2, fun v w h => ?_⟩
      dsimp only
      rw [h1 v w (fun i hi => h i (Finset.mem_union_left _ hi)),
          h2 v w (fun i hi => h i (Finset.mem_union_right _ hi))]
  | mul _ _ ih1 ih2 =>
      obtain ⟨s1, h1⟩ := ih1; obtain ⟨s2, h2⟩ := ih2
      refine ⟨s1 ∪ s2, fun v w h => ?_⟩
      dsimp only
      rw [h1 v w (fun i hi => h i (Finset.mem_union_left _ hi)),
          h2 v w (fun i hi => h i (Finset.mem_union_right _ hi))]

/-- Every polynomial is dominated in absolute value by a monotone polynomial. -/
theorem isPoly_majorant {γ : Type} {p : (γ → ℕ) → ℤ} (hp : IsPoly p) :
    ∃ q : (γ → ℕ) → ℤ, IsPoly q ∧ (∀ v, |p v| ≤ q v) ∧
      (∀ v w : γ → ℕ, (∀ i, v i ≤ w i) → q v ≤ q w) := by
  induction hp with
  | proj i => exact ⟨_, IsPoly.proj i, fun v => by simp, fun v w h => by exact_mod_cast h i⟩
  | const n => exact ⟨_, IsPoly.const |n|, fun _ => le_refl _, fun _ _ _ => le_refl _⟩
  | sub _ _ ih1 ih2 =>
      obtain ⟨q1, hq1, hb1, hm1⟩ := ih1; obtain ⟨q2, hq2, hb2, hm2⟩ := ih2
      refine ⟨fun x => q1 x + q2 x, hq1.add hq2, fun v => ?_, fun v w h => ?_⟩
      · exact le_trans (abs_sub _ _) (add_le_add (hb1 v) (hb2 v))
      · exact add_le_add (hm1 v w h) (hm2 v w h)
  | mul _ _ ih1 ih2 =>
      obtain ⟨q1, hq1, hb1, hm1⟩ := ih1; obtain ⟨q2, hq2, hb2, hm2⟩ := ih2
      refine ⟨fun x => q1 x * q2 x, hq1.mul hq2, fun v => ?_, fun v w h => ?_⟩
      · rw [abs_mul]
        exact mul_le_mul (hb1 v) (hb2 v) (abs_nonneg _) (le_trans (abs_nonneg _) (hb1 v))
      · exact mul_le_mul (hm1 v w h) (hm2 v w h) (le_trans (abs_nonneg _) (hb2 v))
          (le_trans (le_trans (abs_nonneg _) (hb1 v)) (hm1 v w h))

/-- Polynomials respect congruences. -/
theorem isPoly_modEq {γ : Type} {p : (γ → ℕ) → ℤ} (hp : IsPoly p) {N : ℤ} {v w : γ → ℕ}
    (h : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD N]) : p v ≡ p w [ZMOD N] := by
  induction hp with
  | proj i => exact h i
  | const n => rfl
  | sub _ _ ih1 ih2 => exact ih1.sub ih2
  | mul _ _ ih1 ih2 => exact ih1.mul ih2

/-- Every Diophantine set can be defined with finitely many dummy variables. -/
theorem dioph_fin_dummies {n : ℕ} {S : Set (Vector3 ℕ n)} (d : Dioph S) :
    ∃ (m : ℕ) (p : Poly (Fin2 n ⊕ Fin2 m)), ∀ v, S v ↔ ∃ t : Vector3 ℕ m, p (v ⊗ t) = 0 := by
  classical
  obtain ⟨β, p, pe⟩ := d
  obtain ⟨s, hs⟩ := isPoly_support p.isPoly
  set sb : Finset β := s.biUnion (fun x => Sum.elim (fun _ => (∅ : Finset β)) (fun b => {b}) x)
    with hsb
  set m := sb.card with hm
  set e := sb.equivFin with he
  set f : β → Fin2 (m + 1) := fun b =>
    if h : b ∈ sb then Fin2.fs ((Fin2.equivFin m).symm (e ⟨b, h⟩)) else Fin2.fz with hf
  refine ⟨m + 1, Poly.map (Sum.map id f) p, fun v => ?_⟩
  have hcomp : ∀ (u : Vector3 ℕ (m + 1)),
      (Poly.map (Sum.map id f) p) (v ⊗ u) = p (v ⊗ (u ∘ f)) := by
    intro u
    rw [Poly.map_apply]
    congr 1
    funext x
    rcases x with a | b <;> rfl
  rw [pe v]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun j => Fin2.cases' 0 (fun j' => t (e.symm ((Fin2.equivFin m) j') : β)) j, ?_⟩
    rw [hcomp]
    rw [show p (v ⊗ ((fun j => Fin2.cases' 0
      (fun j' => t (e.symm ((Fin2.equivFin m) j') : β)) j) ∘ f)) = p (v ⊗ t) from ?_]
    · exact ht
    · refine hs _ _ ?_
      intro i hi
      rcases i with a | b
      · rfl
      · have hbsb : b ∈ sb := by
          rw [hsb]
          exact Finset.mem_biUnion.2 ⟨Sum.inr b, hi, by simp⟩
        show (fun j => Fin2.cases' 0 (fun j' => t (e.symm ((Fin2.equivFin m) j') : β)) j) (f b) = t b
        rw [hf]
        simp only [dif_pos hbsb]
        show t (e.symm ((Fin2.equivFin m) ((Fin2.equivFin m).symm (e ⟨b, hbsb⟩))) : β) = t b
        rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  · rintro ⟨u, hu⟩
    exact ⟨u ∘ f, by rw [← hcomp]; exact hu⟩

end H10

import Mathlib
import RequestProject.H10.Product
import RequestProject.H10.PolyAux

/-!
# The Davis–Putnam–Robinson bounded quantifier elimination (arithmetic core)

Here we prove the arithmetic equivalence underlying the theorem that Diophantine relations
are closed under bounded universal quantification:

`(∀ k < N, ∃ t, P (k, x, t) = 0)` holds if and only if there are numbers `c, Q, M, K, Y`
with `Q = W !` (for an explicit bound `W`), `M = ∏_{k<N} (1 + (k+1) Q)`,
`M ∣ Q K + Q + 1` (which forces `K ≡ k` modulo each factor), the residues of `Y` bounded
by `c`, and `M ∣ P (K, x, Y)`.

The Diophantine consequence is `H10.dioph_bounded_forall` in `RequestProject.H10.Forall`.
-/

namespace H10

open Nat Finset Dioph Vector3

local infixr:65 " ⊗ " => Sum.elim

theorem prime_gt_of_dvd_modulus {W k p : ℕ} (hp : p.Prime) (hdvd : p ∣ 1 + (k + 1) * (W !)) :
    W < p := by
  by_contra h
  push_neg at h
  have h1 : p ∣ W ! := Nat.dvd_factorial hp.pos h
  have h2 : p ∣ (k + 1) * (W !) := Dvd.dvd.mul_left h1 _
  have : p ∣ 1 := (Nat.dvd_add_right h2).mp (by rwa [Nat.add_comm] at hdvd)
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem coprime_moduli_aux {W k k' : ℕ} (hk : k ≤ W) (h : k' < k) :
    Nat.Coprime (1 + (k + 1) * (W !)) (1 + (k' + 1) * (W !)) := by
  by_contra hg
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
  have hA : p ∣ 1 + (k + 1) * (W !) := hpg.trans (Nat.gcd_dvd_left _ _)
  have hB : p ∣ 1 + (k' + 1) * (W !) := hpg.trans (Nat.gcd_dvd_right _ _)
  have hfac : ¬ (p ∣ W !) := by
    intro hd
    have h2 : p ∣ (k' + 1) * (W !) := Dvd.dvd.mul_left hd _
    have : p ∣ 1 := (Nat.dvd_add_right h2).mp (by rwa [Nat.add_comm] at hB)
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hdiff : p ∣ (k - k') * (W !) := by
    have hd := Nat.dvd_sub hA hB
    have e : 1 + (k + 1) * (W !) - (1 + (k' + 1) * (W !)) = (k - k') * (W !) := by
      have : (k + 1) * (W !) - (k' + 1) * (W !) = (k - k') * W ! := by
        rw [← Nat.sub_mul]; congr 1; omega
      omega
    rwa [e] at hd
  rcases (Nat.Prime.dvd_mul hp).mp hdiff with h1 | h1
  · exact hfac (Nat.dvd_factorial hp.pos (le_trans (Nat.le_of_dvd (by omega) h1) (by omega)))
  · exact hfac h1

theorem coprime_moduli {W k k' : ℕ} (hk : k ≤ W) (hk' : k' ≤ W) (hne : k ≠ k') :
    Nat.Coprime (1 + (k + 1) * (W !)) (1 + (k' + 1) * (W !)) := by
  rcases Nat.lt_or_ge k k' with h | h
  · exact (coprime_moduli_aux hk' h).symm
  · exact coprime_moduli_aux hk (by omega)

theorem prod_dvd_of_pairwise_coprime {ι : Type} {s : Finset ι} {f : ι → ℕ} {z : ℕ}
    (hco : (s : Set ι).Pairwise (Function.onFun Nat.Coprime f))
    (h : ∀ i ∈ s, f i ∣ z) : (∏ i ∈ s, f i) ∣ z := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hco' : (s : Set ι).Pairwise (Function.onFun Nat.Coprime f) :=
        hco.mono (by simp [Finset.coe_insert, Set.subset_insert])
      have hcop : Nat.Coprime (f a) (∏ i ∈ s, f i) := by
        apply Nat.Coprime.prod_right
        intro i hi
        exact hco (by simp) (by simp [hi]) (by rintro rfl; exact ha hi)
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (h a (by simp))
        (ih hco' (fun i hi => h i (by simp [hi])))

/-- Soundness of the Davis–Putnam–Robinson coding: the arithmetic conditions imply that
every `k < N` has a witness. -/
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
theorem dioph_choose {α : Type} {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => (f v).choose (g v) := by
  have key : ∀ v : α → ℕ, (f v).choose (g v) =
      (((2 ^ f v + 1) + 1) ^ f v / (2 ^ f v + 1) ^ g v) % (2 ^ f v + 1) := by
    intro v
    have := choose_eq_digit (f v) (g v) (2 ^ f v + 1) (by omega)
    simpa [digit] using this
  have d2 : DiophFn fun v => (2 : ℕ) ^ f v + 1 := (pow_dioph (D.2) df) D+ (D.1)
  have : DiophFn fun v => ((2 ^ f v + 1) + 1) ^ f v / (2 ^ f v + 1) ^ g v % (2 ^ f v + 1) :=
    ((pow_dioph (d2 D+ (D.1)) df) D/ (pow_dioph d2 dg)) D% d2
  simpa [key] using this

/-- A Bernoulli-type estimate: `r ^ (n+1) ≤ (r - a) ^ (n+1) + (n+1) * a * r ^ n`. -/
theorem pow_le_sub_pow (a r : ℕ) : ∀ n : ℕ, r ^ (n + 1) ≤ (r - a) ^ (n + 1) + (n + 1) * a * r ^ n := by
  intro n
  induction n with
  | zero => simp; omega
  | succ n ih =>
    have h1 : r * r ^ (n + 1) ≤ r * ((r - a) ^ (n + 1) + (n + 1) * a * r ^ n) :=
      Nat.mul_le_mul_left _ ih
    have h2 : r * (r - a) ^ (n + 1) ≤ (r - a) ^ (n + 2) + a * r ^ (n + 1) := by
      have hle : r ≤ (r - a) + a := by omega
      calc r * (r - a) ^ (n + 1) ≤ ((r - a) + a) * (r - a) ^ (n + 1) :=
            Nat.mul_le_mul_right _ hle
        _ = (r - a) ^ (n + 2) + a * (r - a) ^ (n + 1) := by ring
        _ ≤ (r - a) ^ (n + 2) + a * r ^ (n + 1) := by
            have : (r - a) ^ (n + 1) ≤ r ^ (n + 1) := Nat.pow_le_pow_left (by omega) _
            exact Nat.add_le_add_left (Nat.mul_le_mul_left _ this) _
    calc r ^ (n + 2) = r * r ^ (n + 1) := by ring
      _ ≤ r * ((r - a) ^ (n + 1) + (n + 1) * a * r ^ n) := h1
      _ = r * (r - a) ^ (n + 1) + (n + 1) * a * (r * r ^ n) := by ring
      _ ≤ ((r - a) ^ (n + 2) + a * r ^ (n + 1)) + (n + 1) * a * r ^ (n + 1) := by
          have h3 : r * r ^ n = r ^ (n + 1) := by ring
          rw [h3]; exact Nat.add_le_add_right h2 _
      _ = (r - a) ^ (n + 2) + (n + 2) * a * r ^ (n + 1) := by ring

/-- For `r` large, `n ! = ⌊r ^ n / C(r, n)⌋`. -/
theorem factorial_eq_div (n r : ℕ) (h1 : n ^ 2 * (n ! + 1) < r) : n ! = r ^ n / r.choose n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  set n := n' + 1 with hndef
  have hnr : n ≤ r := by nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)]
  have hC : 0 < r.choose n := Nat.choose_pos hnr
  have hD : r.descFactorial n = n ! * r.choose n := Nat.descFactorial_eq_factorial_mul_choose r n
  have hlow : n ! * r.choose n ≤ r ^ n := by rw [← hD]; exact Nat.descFactorial_le_pow r n
  have hkey : r ^ n ≤ (r - n) ^ n + n * n * r ^ n' := by
    have := pow_le_sub_pow n r n'
    simpa [hndef] using this
  have hsub : (r - n) ^ n ≤ r.descFactorial n :=
    le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_sub_le_descFactorial r n)
  have hrpos : 0 < r ^ n' := Nat.pow_pos (by omega)
  have hbig : n ! * (n * n * r ^ n') < (r - n) ^ n := by
    have e1 : (n ! + 1) * (n * n) * r ^ n' < r * r ^ n' := by
      have h : (n ! + 1) * (n * n) < r := by
        have : n ^ 2 * (n ! + 1) = (n ! + 1) * (n * n) := by ring
        omega
      exact Nat.mul_lt_mul_of_lt_of_le h (le_refl _) hrpos
    have e2 : r * r ^ n' = r ^ n := by rw [hndef]; ring
    rw [e2] at e1
    nlinarith [hkey]
  have hCbig : n * n * r ^ n' < r.choose n := by
    have h : n ! * (n * n * r ^ n') < n ! * r.choose n := by
      calc n ! * (n * n * r ^ n') < (r - n) ^ n := hbig
        _ ≤ r.descFactorial n := hsub
        _ = n ! * r.choose n := hD
    exact lt_of_mul_lt_mul_left h (Nat.zero_le _)
  have hhigh : r ^ n < (n ! + 1) * r.choose n := by
    have h4 : r ^ n ≤ n ! * r.choose n + n * n * r ^ n' := by
      calc r ^ n ≤ (r - n) ^ n + n * n * r ^ n' := hkey
        _ ≤ r.descFactorial n + n * n * r ^ n' := Nat.add_le_add_right hsub _
        _ = n ! * r.choose n + n * n * r ^ n' := by rw [hD]
    have h5 : r ^ n < n ! * r.choose n + r.choose n := by omega
    nlinarith [h5]
  exact (Nat.div_eq_of_lt_le hlow hhigh).symm

theorem factorial_bound (n : ℕ) : n ^ 2 * (n ! + 1) < 2 * (n + 1) ^ (n + 3) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  have h1 : n ! ≤ (n + 1) ^ n := le_trans (Nat.factorial_le_pow n) (Nat.pow_le_pow_left (by omega) n)
  have h2 : (1 : ℕ) ≤ (n + 1) ^ n := Nat.one_le_pow _ _ (by omega)
  have h3 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  calc n ^ 2 * (n ! + 1) ≤ (n + 1) ^ 2 * ((n + 1) ^ n + 1) := Nat.mul_le_mul h3 (by omega)
    _ ≤ (n + 1) ^ 2 * (2 * (n + 1) ^ n) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (n + 1) ^ (n + 2) := by ring
    _ < 2 * (n + 1) ^ (n + 3) := by
        have : (n + 1) ^ (n + 2) < (n + 1) ^ (n + 3) := Nat.pow_lt_pow_right (by omega) (by omega)
        omega

/-- The factorial function is Diophantine. -/
theorem dioph_factorial {α : Type} {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    DiophFn fun v => (f v)! := by
  have key : ∀ v : α → ℕ, (f v)! =
      (2 * (f v + 1) ^ (f v + 3)) ^ (f v) / (2 * (f v + 1) ^ (f v + 3)).choose (f v) :=
    fun v => factorial_eq_div _ _ (factorial_bound (f v))
  have dr : DiophFn fun v => 2 * (f v + 1) ^ (f v + 3) :=
    (D.2) D* (pow_dioph (df D+ (D.1)) (df D+ (D.3)))
  have : DiophFn fun v =>
      (2 * (f v + 1) ^ (f v + 3)) ^ (f v) / (2 * (f v + 1) ^ (f v + 3)).choose (f v) :=
    (pow_dioph dr df) D/ (dioph_choose dr df)
  simpa [key] using this

end H10

import Mathlib
import RequestProject.H10.Bounded

/-!
# Diophantine sets are closed under bounded universal quantification

This is the Davis–Putnam–Robinson theorem, the last missing ingredient (besides Matiyasevic's
theorem `Dioph.pow_dioph`, already in Mathlib) for the negative solution of Hilbert's tenth
problem.
-/

namespace H10

open Nat Dioph Vector3 Sum Fin2

local infixr:65 " ⊗ " => Sum.elim

theorem dioph_prodAB {α : Type} {fa fb fy : (α → ℕ) → ℕ} (da : DiophFn fa) (db : DiophFn fb)
    (dy : DiophFn fy) : DiophFn fun v => prodAB (fa v) (fb v) (fy v) :=
  Dioph.diophFn_comp dioph_prodAB3 [fa, fb, fy] ⟨da, db, dy⟩

theorem dioph_descFactorial {α : Type} {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => (f v).descFactorial (g v) := by
  simpa [Nat.descFactorial_eq_factorial_mul_choose] using
    (dioph_factorial dg) D* (dioph_choose df dg)

theorem dioph_univ {α : Type} : Dioph (Set.univ : Set (α → ℕ)) :=
  Dioph.of_no_dummies _ (Poly.const 0) (fun _ => ⟨fun _ => rfl, fun _ => trivial⟩)

/-- A finite (indexed by `Fin2 m`) conjunction of Diophantine conditions is Diophantine. -/
theorem dioph_forall_fin2 {α : Type} : ∀ {m : ℕ} (S : Fin2 m → Set (α → ℕ)), (∀ j, Dioph (S j)) →
    Dioph {v | ∀ j, v ∈ S j}
  | 0, S, _ => by
      have h : {v : α → ℕ | ∀ j : Fin2 0, v ∈ S j} = Set.univ := by
        ext v; exact ⟨fun _ => trivial, fun _ j => nomatch j⟩
      rw [h]; exact dioph_univ
  | (m + 1), S, d => by
      have h := Dioph.inter (d Fin2.fz) (dioph_forall_fin2 (fun j => S (Fin2.fs j)) (fun j => d _))
      have e : {v : α → ℕ | ∀ j : Fin2 (m + 1), v ∈ S j} =
          (S Fin2.fz) ∩ {v | ∀ j : Fin2 m, v ∈ S (Fin2.fs j)} := by
        ext v
        exact ⟨fun hv => ⟨hv _, fun j => hv _⟩, fun ⟨h1, h2⟩ j => by cases j with
          | fz => exact h1
          | fs j => exact h2 j⟩
      rw [e]; exact h

theorem vector3_eta {n : ℕ} (v : Vector3 ℕ (n + 1)) : (v fz :: (v ∘ fs)) = v := by
  funext i; cases i with
  | fz => rfl
  | fs i => rfl

/-- **Davis–Putnam–Robinson**: Diophantine relations are closed under bounded universal
quantification. Here the bound is the first coordinate of the vector of parameters. -/
theorem dioph_bounded_forall {n : ℕ} {S : Set (Vector3 ℕ (n + 1))} (d : Dioph S) :
    Dioph {v : Vector3 ℕ (n + 1) | ∀ k < v fz, (k :: (v ∘ fs)) ∈ S} := by
  obtain ⟨m, pp, pe⟩ := dioph_fin_dummies d
  obtain ⟨q, hqp, hqb, hqm⟩ := isPoly_majorant pp.isPoly
  set qq : Poly (Fin2 (n + 1) ⊕ Fin2 m) := ⟨q, hqp⟩ with hqq
  set mp1 : Fin2 (n + 1) ⊕ Fin2 m → Fin2 (n + 1) ⊕ (Fin2 4 ⊕ Fin2 m) :=
    Sum.elim (fun i => Sum.inl i) (fun _ => Sum.inr (Sum.inl &0)) with hmp1
  set mp2 : Fin2 (n + 1) ⊕ Fin2 m → Fin2 (n + 1) ⊕ (Fin2 4 ⊕ Fin2 m) :=
    Sum.elim (fun a => Fin2.cases' (Sum.inr (Sum.inl &3)) (fun i => Sum.inl (Fin2.fs i)) a)
      (fun j => Sum.inr (Sum.inr j)) with hmp2
  have hcond : Dioph {w : (Fin2 (n + 1) ⊕ (Fin2 4 ⊕ Fin2 m)) → ℕ |
      (w (inr (inl &1)) = (((Poly.map mp1 qq) w).natAbs + w (inr (inl &0)) + w (inl fz))!) ∧
      (w (inr (inl &2)) = prodAB 1 (w (inr (inl &1))) (w (inl fz))) ∧
      (w (inr (inl &2)) ∣ w (inr (inl &1)) * w (inr (inl &3)) + w (inr (inl &1)) + 1) ∧
      (∀ j : Fin2 m, w (inr (inl &0)) ≤ w (inr (inr j)) ∧
        w (inr (inl &2)) ∣ (w (inr (inr j))).descFactorial (w (inr (inl &0)) + 1)) ∧
      (w (inr (inl &2)) ∣ ((Poly.map mp2 pp) w).natAbs)} := by
    refine ((Dioph.proj_dioph (inr (inl &1))) D= (dioph_factorial
      (((Dioph.abs_poly_dioph (Poly.map mp1 qq)) D+ (Dioph.proj_dioph (inr (inl &0))))
        D+ (Dioph.proj_dioph (inl fz))))) D∧ ?_
    refine ((Dioph.proj_dioph (inr (inl &2))) D= (dioph_prodAB (D.1)
      (Dioph.proj_dioph (inr (inl &1))) (Dioph.proj_dioph (inl fz)))) D∧ ?_
    refine ((Dioph.proj_dioph (inr (inl &2))) D∣ (((Dioph.proj_dioph (inr (inl &1)))
      D* (Dioph.proj_dioph (inr (inl &3)))) D+ (Dioph.proj_dioph (inr (inl &1))) D+ (D.1))) D∧ ?_
    refine (dioph_forall_fin2 _ (fun j => ?_)) D∧
      ((Dioph.proj_dioph (inr (inl &2))) D∣ (Dioph.abs_poly_dioph (Poly.map mp2 pp)))
    exact ((Dioph.proj_dioph (inr (inl &0))) D≤ (Dioph.proj_dioph (inr (inr j)))) D∧
      ((Dioph.proj_dioph (inr (inl &2))) D∣
        (dioph_descFactorial (Dioph.proj_dioph (inr (inr j)))
          ((Dioph.proj_dioph (inr (inl &0))) D+ (D.1))))
  refine Dioph.ext (Dioph.ex_dioph hcond) (fun v => ?_)
  have hv1 : ∀ (z : (Fin2 4 ⊕ Fin2 m) → ℕ),
      ((v ⊗ z) ∘ mp1) = ((v fz :: (v ∘ fs)) ⊗ (fun _ => z (inl &0))) := by
    intro z
    funext y
    rcases y with a | j
    · cases a with
      | fz => rfl
      | fs a => rfl
    · rfl
  have hv2 : ∀ (z : (Fin2 4 ⊕ Fin2 m) → ℕ),
      ((v ⊗ z) ∘ mp2) = ((z (inl &3) :: (v ∘ fs)) ⊗ (fun j => z (inr j))) := by
    intro z
    funext y
    rcases y with a | j
    · cases a with
      | fz => rfl
      | fs a => rfl
    · rfl
  constructor
  · rintro ⟨z, h1, h2, h3, h4, h5⟩
    rw [Poly.map_apply, hv1 z] at h1
    rw [Poly.map_apply, hv2 z] at h5
    intro k hk
    refine (pe _).2 ?_
    refine dpr_of_exists pp.isPoly hqb hqm (v fz) (v ∘ fs)
      (z (inl &0)) (z (inl &1)) (z (inl &2)) (z (inl &3)) (fun j => z (inr j))
      h1 h2 h3 h4 h5 k hk
  · intro H
    obtain ⟨c, Q, M, K, Y, e1, e2, e3, e4, e5⟩ :=
      exists_of_dpr (q := q) pp.isPoly (v fz) (v ∘ fs)
        (fun k hk => (pe _).1 (H k hk))
    refine ⟨Sum.elim [c, Q, M, K] Y, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Poly.map_apply, hv1 _]; exact e1
    · exact e2
    · exact e3
    · exact e4
    · rw [Poly.map_apply, hv2 _]; exact e5

end H10

