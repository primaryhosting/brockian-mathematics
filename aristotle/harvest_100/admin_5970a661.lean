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

import RequestProject.AKS.Algorithm

/-!
# Correctness of the AKS primality test

The main result of this file is `AKS.aksTest_iff_prime`:
the decision procedure `AKS.aksTest` returns `true` exactly on the primes.
-/

namespace AKS

open Polynomial Finset

theorem getD_pXAdd_lt (n r k c : ℕ) (hn : 0 < n) (i : ℕ) (hi : i < r) :
    (pXAdd n r k c).getD i 0 < n := by
  rw [pXAdd, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simpa using Nat.mod_lt _ hn

/-- The polynomial `(X + a).comp (X ^ m)` is `X ^ m + a`. -/
theorem comp_X_add_C {R : Type*} [CommRing R] (a : R) (m : ℕ) :
    ((X + C a : R[X])).comp (X ^ m) = X ^ m + C a := by
  simp

/-- The list-level test `polyOK` implies the introspective relation. -/
theorem introspective_of_polyOK {n r a : ℕ} (hr : 0 < r) (h : polyOK n r a = true) :
    Introspective r n ((X + C ((a : ℕ) : ZMod n)) : (ZMod n)[X]) := by
  rw [polyOK, beq_iff_eq] at h
  have h1 : Cong r (emb n r (ppow n r (pXAdd n r 1 a) n))
      (((X : (ZMod n)[X]) + C ((a : ℕ) : ZMod n)) ^ n) := by
    refine (emb_ppow n r hr _ n).trans ?_
    refine Cong.pow ?_ n
    have := emb_pXAdd n r 1 a hr
    simpa using this
  have h2 : Cong r (emb n r (pXAdd n r n a))
      ((X : (ZMod n)[X]) ^ n + C ((a : ℕ) : ZMod n)) := emb_pXAdd n r n a hr
  have := (h1.symm.trans (h ▸ h2))
  rw [Introspective, comp_X_add_C]
  exact this

/-- For prime `n` the list-level test `polyOK` succeeds. -/
theorem polyOK_of_prime {n : ℕ} [Fact n.Prime] {r : ℕ} (hr : 0 < r) (a : ℕ) :
    polyOK n r a = true := by
  have hn : 1 < n := (Fact.out (p := n.Prime)).one_lt
  haveI : CharP (ZMod n) n := ZMod.charP n
  have hfrob : ((X : (ZMod n)[X]) + C ((a : ℕ) : ZMod n)) ^ n
      = X ^ n + C ((a : ℕ) : ZMod n) := by
    rw [add_pow_char]
    congr 1
    rw [← map_pow, ZMod.pow_card]
  rw [polyOK, beq_iff_eq]
  refine emb_injective n r hr (length_ppow n r _ n) (length_pXAdd n r n a)
    (fun k hk => getD_ppow_lt n r hn _ n k hk) (fun k hk => getD_pXAdd_lt n r n a (by omega) k hk)
    ?_
  have h1 : Cong r (emb n r (ppow n r (pXAdd n r 1 a) n))
      (((X : (ZMod n)[X]) + C ((a : ℕ) : ZMod n)) ^ n) := by
    refine (emb_ppow n r hr _ n).trans ?_
    refine Cong.pow ?_ n
    have := emb_pXAdd n r 1 a hr
    simpa using this
  have h2 : Cong r (emb n r (pXAdd n r n a))
      ((X : (ZMod n)[X]) ^ n + C ((a : ℕ) : ZMod n)) := emb_pXAdd n r n a hr
  rw [hfrob] at h1
  exact h1.trans h2.symm

/-- If every `a` in `[2, r]` has `gcd a n ∈ {1, n}` and `n ≤ r`, then `n` is prime. -/
theorem prime_of_gcdOK_le {n r : ℕ} (hn : 2 ≤ n) (hnr : n ≤ r)
    (h : ∀ a, 2 ≤ a → a ≤ r → Nat.gcd a n = 1 ∨ Nat.gcd a n = n) : n.Prime := by
  rw [Nat.prime_def_lt]
  refine ⟨hn, fun m hm hmn => ?_⟩
  by_contra hm1
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd (Nat.eq_zero_of_zero_dvd hmn) (by omega)
  have hgcd : Nat.gcd m n = m := Nat.gcd_eq_left hmn
  rcases h m (by omega) (by omega) with h1 | h1 <;> omega

theorem gcd_one_of_gcdOK {n r : ℕ} (hrn : r < n)
    (h : ∀ a, 2 ≤ a → a ≤ r → Nat.gcd a n = 1 ∨ Nat.gcd a n = n) :
    ∀ a, 2 ≤ a → a ≤ r → Nat.gcd a n = 1 := by
  intro a ha2 har
  rcases h a ha2 har with h1 | h1
  · exact h1
  · exfalso
    have : Nat.gcd a n ≤ a := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a n)
    omega

/-- **Correctness of the AKS test.** -/
theorem aksTest_iff_prime (n : ℕ) : aksTest n = true ↔ n.Prime := by
  constructor
  · intro h
    rw [aksTest] at h
    split at h
    · simp at h
    · rename_i hn2
      push_neg at hn2
      split at h
      · simp at h
      · rename_i hpp
        simp only at h
        set r := findR n with hrdef
        have hr2 : 2 ≤ r := two_le_findR n hn2
        split at h
        · simp at h
        · rename_i hgcd
          have hgcdOK : gcdOK n r = true := by
            rcases Bool.eq_false_or_eq_true (gcdOK n r) with h1 | h1
            · exact absurd h1 hgcd
            · exact h1
          have hg := (gcdOK_iff n r).1 hgcdOK
          split at h
          · rename_i hle
            exact prime_of_gcdOK_le hn2 hle hg
          · rename_i hle
            push_neg at hle
            -- now `r < n`
            have hrn : r < n := hle
            have hcop1 := gcd_one_of_gcdOK hrn hg
            -- every prime factor of `n` exceeds `r`
            have hbig : ∀ q : ℕ, q.Prime → q ∣ n → r < q := by
              intro q hq hqn
              by_contra hqr
              push_neg at hqr
              have : Nat.gcd q n = q := Nat.gcd_eq_left hqn
              have := hcop1 q hq.two_le hqr
              omega
            have hcopn : Nat.Coprime n r := by
              rw [Nat.coprime_comm]
              rw [Nat.coprime_iff_gcd_eq_one]
              by_contra hgc
              obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hgc
              have hqr : q ∣ r := hqd.trans (Nat.gcd_dvd_left r n)
              have hqn : q ∣ n := hqd.trans (Nat.gcd_dvd_right r n)
              have := hbig q hq hqn
              have := Nat.le_of_dvd (by omega) hqr
              omega
            set p := n.minFac with hpdef
            have hp : p.Prime := Nat.minFac_prime (by omega)
            have hpn : p ∣ n := Nat.minFac_dvd n
            have hrp : r < p := hbig p hp hpn
            have hord : ∀ i, 1 ≤ i → i ≤ 100 * (bitLen n) ^ 2 → (n : ZMod r) ^ i ≠ 1 := by
              intro i hi1 hi2 hcon
              have := findR_ord n hn2 i hi1 (by simpa [thr] using hi2)
              apply this
              have h1 : ((n ^ i : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
                push_cast
                simpa using hcon
              have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
              have h3 : n ^ i % r = 1 % r := h2
              rwa [Nat.mod_eq_of_lt (by omega)] at h3
            have hintro : ∀ a : ℕ, a ≤ 4 * (Nat.sqrt r + 1) * bitLen n →
                Introspective r n ((X + C ((a : ℕ) : ZMod n)) : (ZMod n)[X]) := by
              intro a ha
              have hmem : a ∈ List.range (ell n r + 1) := by
                rw [List.mem_range]
                simpa [ell] using Nat.lt_succ_of_le ha
              have := List.all_eq_true.1 h a hmem
              exact introspective_of_polyOK (by omega) this
            obtain ⟨k, hk⟩ := prime_pow_of_introspective n r p (bitLen n) hp hn2
              (lt_two_pow_bitLen n) hr2 hcopn hpn hrp hord hintro
            rcases Nat.lt_or_ge k 2 with hk2 | hk2
            · interval_cases k
              · simp at hk; omega
              · rw [pow_one] at hk; rwa [hk]
            · exfalso
              have : isPerfectPower n = true := (isPerfectPower_iff n hn2).2 ⟨p, k, hk2, hk⟩
              rw [this] at hpp
              simp at hpp
  · intro hp
    haveI : Fact n.Prime := ⟨hp⟩
    have hn2 : 2 ≤ n := hp.two_le
    rw [aksTest]
    rw [if_neg (by omega)]
    have hpp : isPerfectPower n = false := by
      rcases Bool.eq_false_or_eq_true (isPerfectPower n) with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨a, b, hb, hab⟩ := (isPerfectPower_iff n hn2).1 h1
        have hadvd : a ∣ n := ⟨a ^ (b - 1), by rw [hab, ← pow_succ']; congr 1; omega⟩
        rcases (Nat.Prime.eq_one_or_self_of_dvd hp a hadvd) with h2 | h2
        · rw [h2, one_pow] at hab; omega
        · subst h2
          have : a ^ 2 ≤ a ^ b := Nat.pow_le_pow_right (by omega) hb
          rw [← hab] at this
          nlinarith
    rw [hpp]
    simp only [Bool.false_eq_true, if_false]
    have hr2 : 2 ≤ findR n := two_le_findR n hn2
    have hgcdOK : gcdOK n (findR n) = true := by
      rw [gcdOK_iff]
      intro a _ _
      rcases hp.eq_one_or_self_of_dvd (Nat.gcd a n) (Nat.gcd_dvd_right a n) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    simp only [hgcdOK, Bool.true_eq_false, if_false]
    split
    · rfl
    · refine List.all_eq_true.2 fun a _ => polyOK_of_prime (by omega) a

end AKS

import RequestProject.AKS.Introspective
import RequestProject.AKS.Numeric

/-!
# The AKS criterion

The main theorem of this file, `AKS.prime_pow_of_introspective`, is the mathematical heart of
the Agrawal–Kayal–Saxena primality test: if `n` passes the polynomial congruence tests
`(X + a)^n ≡ X^n + a  (mod X^r - 1, n)` for enough values of `a`, and the multiplicative order
of `n` modulo `r` is large, then `n` is a power of a prime.
-/

namespace AKS

open Polynomial Finset

/-! ## Numeric preliminaries -/

theorem two_pow_le_choose (d : ℕ) : 2 ^ d ≤ (2 * d).choose d := by
  induction d with
  | zero => simp
  | succ k ih =>
      have hstep : 2 * ((2 * k).choose k) ≤ (2 * (k + 1)).choose (k + 1) := by
        have h1 : (2 * k + 1 + 1).choose (k + 1) =
            (2 * k + 1).choose k + (2 * k + 1).choose (k + 1) := Nat.choose_succ_succ _ _
        have h2 : (2 * k + 1).choose k = (2 * k + 1).choose (k + 1) := by
          have := Nat.choose_symm (n := 2 * k + 1) (k := k) (by omega)
          rw [show 2 * k + 1 - k = k + 1 by omega] at this
          exact this.symm
        have h3 : (2 * k + 1).choose (k + 1) = (2 * k).choose k + (2 * k).choose (k + 1) :=
          Nat.choose_succ_succ _ _
        have h4 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
        rw [h4, h1]
        omega
      calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        _ ≤ 2 * ((2 * k).choose k) := by omega
        _ ≤ (2 * (k + 1)).choose (k + 1) := hstep

/-- If `n` is not a power of `p`, the numbers `n ^ i * p ^ j` are pairwise distinct. -/
theorem nat_pow_mul_pow_injective {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime)
    (hnk : ∀ k, n ≠ p ^ k) {i₁ j₁ i₂ j₂ : ℕ} (h : n ^ i₁ * p ^ j₁ = n ^ i₂ * p ^ j₂) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  have hp2 : 2 ≤ p := hp.two_le
  have hn0 : 0 < n := by omega
  have hp0 : 0 < p := by omega
  have key : ∀ a b c e : ℕ, a < b → n ^ a * p ^ c = n ^ b * p ^ e → False := by
    intro a b c e hab heq
    have hdvd : n ∣ p ^ c := by
      have h1 : n ^ a * p ^ c = n ^ a * (n ^ (b - a) * p ^ e) := by
        rw [heq, ← mul_assoc, ← pow_add]
        congr 2
        omega
      have h2 : p ^ c = n ^ (b - a) * p ^ e := by
        exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hn0) h1
      refine ⟨n ^ (b - a - 1) * p ^ e, ?_⟩
      rw [h2, ← mul_assoc, ← pow_succ']
      congr 2
      omega
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact hnk k hk
  rcases lt_trichotomy i₁ i₂ with hlt | heq | hgt
  · exact absurd h (fun hh => key i₁ i₂ j₁ j₂ hlt hh)
  · subst heq
    refine ⟨rfl, ?_⟩
    have := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hn0 (n := i₁)) h
    exact Nat.pow_right_injective hp2 this
  · exact absurd h.symm (fun hh => key i₂ i₁ j₂ j₁ hgt hh)

/-! ## Introspection at a root of unity -/

theorem Introspective.pow_exp {R : Type*} [CommRing R] {r m : ℕ} {f : R[X]}
    (h : Introspective r m f) (i : ℕ) : Introspective r (m ^ i) f := by
  induction i with
  | zero => simpa using introspective_one r f
  | succ k ih => rw [pow_succ]; exact ih.mul_exp h

theorem aeval_pow_of_introspective {p r m : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    [Algebra (ZMod p) K] {x : K} (hx : x ^ r = 1) {f : (ZMod p)[X]}
    (h : Introspective r m f) : (aeval x f) ^ m = aeval (x ^ m) f := by
  obtain ⟨q, hq⟩ := h
  have := congrArg (fun g : (ZMod p)[X] => aeval x g) hq
  simp only [map_sub, map_pow, aeval_comp, aeval_X, map_one, hx, sub_self, zero_mul,
    map_mul] at this
  exact sub_eq_zero.mp this

/-! ## Products of linear polynomials -/

/-- The polynomial `∏_{a ∈ T} (X + a)` over `ZMod p`. -/
noncomputable def linProd (p : ℕ) (T : Finset ℕ) : (ZMod p)[X] :=
  ∏ a ∈ T, (X + C ((a : ℕ) : ZMod p))

theorem linProd_natDegree (p : ℕ) [Fact p.Prime] (T : Finset ℕ) :
    (linProd p T).natDegree = T.card := by
  classical
  rw [linProd, Polynomial.natDegree_prod]
  · rw [Finset.sum_congr rfl (fun i _ => Polynomial.natDegree_X_add_C ((i : ℕ) : ZMod p))]
    simp
  · intro i _
    exact Polynomial.X_add_C_ne_zero _

theorem linProd_eval (p : ℕ) [Fact p.Prime] (T : Finset ℕ) (y : ZMod p) :
    (linProd p T).eval y = ∏ a ∈ T, (y + (a : ZMod p)) := by
  simp [linProd, Polynomial.eval_prod]

/-- On subsets of `range N` with `N ≤ p`, the map `T ↦ ∏_{a ∈ T} (X + a)` is injective. -/
theorem linProd_injOn (p N : ℕ) [Fact p.Prime] (hN : N ≤ p) :
    ∀ T ⊆ Finset.range N, ∀ T' ⊆ Finset.range N, linProd p T = linProd p T' → T = T' := by
  classical
  have key : ∀ (T : Finset ℕ), T ⊆ Finset.range N → ∀ a < N,
      ((linProd p T).eval (-(a : ZMod p)) = 0 ↔ a ∈ T) := by
    intro T hT a ha
    rw [linProd_eval]
    constructor
    · intro h
      obtain ⟨b, hb, hb0⟩ := Finset.prod_eq_zero_iff.1 h
      have hbN : b < N := Finset.mem_range.1 (hT hb)
      have : ((b : ZMod p)) = ((a : ZMod p)) := by
        have : (-(a : ZMod p)) + (b : ZMod p) = 0 := hb0
        linear_combination this
      have hab : b = a := by
        have h1 : (b : ZMod p).val = b := ZMod.val_cast_of_lt (by omega)
        have h2 : (a : ZMod p).val = a := ZMod.val_cast_of_lt (by omega)
        rw [← h1, ← h2, this]
      rwa [hab] at hb
    · intro h
      refine Finset.prod_eq_zero h ?_
      ring
  intro T hT T' hT' heq
  ext a
  by_cases ha : a < N
  · rw [← key T hT a ha, ← key T' hT' a ha, heq]
  · constructor
    · intro h; exact absurd (Finset.mem_range.1 (hT h)) ha
    · intro h; exact absurd (Finset.mem_range.1 (hT' h)) ha

/-! ## The main criterion -/

theorem prime_pow_of_introspective_aux
    (n r p B : ℕ) [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K] (x : K)
    (hxord : orderOf x = r)
    (hn : 2 ≤ n) (hB : n < 2 ^ B) (hr2 : 2 ≤ r) (hcopn : Nat.Coprime n r)
    (hpn : p ∣ n) (hrp : r < p)
    (hord : ∀ i, 1 ≤ i → i ≤ 100 * B ^ 2 → (n : ZMod r) ^ i ≠ 1)
    (hintro : ∀ a : ℕ, a ≤ 4 * (Nat.sqrt r + 1) * B →
        Introspective r n ((X + C ((a : ℕ) : ZMod n)) : (ZMod n)[X])) :
    ∃ k, n = p ^ k := by
  classical
  by_contra hnk
  push_neg at hnk
  haveI : NeZero r := ⟨by omega⟩
  have hp : p.Prime := Fact.out
  have hcopp : Nat.Coprime p r := Nat.Coprime.coprime_dvd_left hpn hcopn
  -- The multiplicative data modulo `r`.
  set u : (ZMod r)ˣ := ZMod.unitOfCoprime n hcopn with hu
  set v : (ZMod r)ˣ := ZMod.unitOfCoprime p hcopp with hv
  set Mf : Finset (ZMod r)ˣ :=
    Finset.image (fun q : Fin r × Fin r => u ^ (q.1 : ℕ) * v ^ (q.2 : ℕ)) Finset.univ with hMfdef
  set t : ℕ := Mf.card with htdef
  have hcardunits : Fintype.card (ZMod r)ˣ < r := by
    rw [ZMod.card_units_eq_totient]
    exact Nat.totient_lt r (by omega)
  have horder_lt : ∀ w : (ZMod r)ˣ, orderOf w < r := by
    intro w
    exact lt_of_le_of_lt (orderOf_le_card_univ) hcardunits
  have hmem : ∀ i j : ℕ, u ^ i * v ^ j ∈ Mf := by
    intro i j
    have hi : u ^ i = u ^ (i % orderOf u) := (pow_mod_orderOf u i).symm
    have hj : v ^ j = v ^ (j % orderOf v) := (pow_mod_orderOf v j).symm
    rw [hi, hj, hMfdef]
    refine Finset.mem_image.2 ⟨(⟨i % orderOf u, ?_⟩, ⟨j % orderOf v, ?_⟩), Finset.mem_univ _, rfl⟩
    · exact lt_of_lt_of_le (Nat.mod_lt _ (orderOf_pos u)) (le_of_lt (horder_lt u))
    · exact lt_of_lt_of_le (Nat.mod_lt _ (orderOf_pos v)) (le_of_lt (horder_lt v))
  have hMfspec : ∀ w ∈ Mf, ∃ i j : ℕ, w = u ^ i * v ^ j := by
    intro w hw
    rw [hMfdef] at hw
    obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hw
    exact ⟨q.1, q.2, hq.symm⟩
  have htr : t < r := by
    calc t ≤ Fintype.card (ZMod r)ˣ := Finset.card_le_univ Mf
      _ < r := hcardunits
  have hordu : 100 * B ^ 2 < orderOf u := by
    by_contra hcon
    push_neg at hcon
    have h1 : 1 ≤ orderOf u := orderOf_pos u
    have := pow_orderOf_eq_one u
    have h2 : ((n : ZMod r)) ^ orderOf u = 1 := by
      have h3 : ((u ^ orderOf u : (ZMod r)ˣ) : ZMod r) = 1 := by rw [this]; simp
      rw [Units.val_pow_eq_pow_val] at h3
      rw [hu] at h3
      simpa using h3
    exact hord (orderOf u) h1 hcon h2
  have htlarge : 100 * B ^ 2 < t := by
    have hsub : Finset.image (fun i : Fin (orderOf u) => u ^ (i : ℕ)) Finset.univ ⊆ Mf := by
      intro w hw
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hw
      rw [← hi]
      have := hmem (i : ℕ) 0
      simpa using this
    have hcardim : (Finset.image (fun i : Fin (orderOf u) => u ^ (i : ℕ))
        Finset.univ).card = orderOf u := by
      rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
      intro a b hab
      have := pow_injOn_Iio_orderOf (x := u) (Set.mem_Iio.2 a.isLt) (Set.mem_Iio.2 b.isLt) hab
      exact Fin.ext this
    have : orderOf u ≤ t := by
      rw [htdef, ← hcardim]
      exact Finset.card_le_card hsub
    omega
  -- Numeric consequences.
  set s := Nat.sqrt t with hsdef
  set d := 2 * (s + 1) * B with hddef
  have hdt : d < t := d_lt_t htlarge
  have h2dr : 2 * d ≤ r := two_d_le htlarge (le_of_lt htr)
  have hnpow : n ^ (2 * s) < 2 ^ d := pow_lt_two_pow_d hn hB htlarge
  have h2dl : 2 * d ≤ 4 * (Nat.sqrt r + 1) * B := by
    have : s ≤ Nat.sqrt r := Nat.sqrt_le_sqrt (le_of_lt htr)
    have : 4 * (s + 1) * B ≤ 4 * (Nat.sqrt r + 1) * B := by
      apply Nat.mul_le_mul_right
      omega
    calc 2 * d = 4 * (s + 1) * B := by rw [hddef]; ring
      _ ≤ 4 * (Nat.sqrt r + 1) * B := this
  -- Introspection over `ZMod p`.
  have hintro_p : ∀ a : ℕ, a ≤ 4 * (Nat.sqrt r + 1) * B →
      Introspective r n ((X + C ((a : ℕ) : ZMod p)) : (ZMod p)[X]) := by
    intro a ha
    have h := (hintro a ha).map (ZMod.castHom hpn (ZMod p))
    simpa using h
  have hintro_all : ∀ (T : Finset ℕ), T ⊆ Finset.range (2 * d) → ∀ i j : ℕ,
      Introspective r (n ^ i * p ^ j) (linProd p T) := by
    intro T hT i j
    refine Introspective.prod T ?_
    intro a haT
    have haltd : a < 2 * d := Finset.mem_range.1 (hT haT)
    have hbase : Introspective r n ((X + C ((a : ℕ) : ZMod p)) : (ZMod p)[X]) :=
      hintro_p a (by omega)
    exact (hbase.pow_exp i).mul_exp ((introspective_char p r _).pow_exp j)
  -- The set of evaluation points.
  have hxr : x ^ r = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  set Rt : Finset K :=
    Finset.image (fun w : (ZMod r)ˣ => x ^ ((w : ZMod r)).val) Mf with hRtdef
  have hRtcard : Rt.card = t := by
    rw [hRtdef, htdef]
    refine Finset.card_image_of_injOn ?_
    intro a _ b _ hab
    have hlt : ∀ w : (ZMod r)ˣ, ((w : ZMod r)).val < r := fun w => ZMod.val_lt _
    have := pow_injOn_Iio_orderOf (x := x)
      (Set.mem_Iio.2 (by rw [hxord]; exact hlt a)) (Set.mem_Iio.2 (by rw [hxord]; exact hlt b)) hab
    exact Units.ext (ZMod.val_injective _ this)
  -- Evaluating at powers of `x`.
  have hxpow : ∀ i j : ℕ, x ^ (n ^ i * p ^ j) = x ^ (((u ^ i * v ^ j : (ZMod r)ˣ) : ZMod r)).val := by
    intro i j
    have hcast : ((u ^ i * v ^ j : (ZMod r)ˣ) : ZMod r) = ((n ^ i * p ^ j : ℕ) : ZMod r) := by
      push_cast
      simp [hu, hv, ZMod.coe_unitOfCoprime]
    rw [hcast, ZMod.val_natCast, ← hxord, pow_mod_orderOf]
  have heval : ∀ (T : Finset ℕ), T ⊆ Finset.range (2 * d) → ∀ i j : ℕ,
      (aeval x (linProd p T)) ^ (n ^ i * p ^ j) =
        aeval (x ^ (((u ^ i * v ^ j : (ZMod r)ˣ) : ZMod r)).val) (linProd p T) := by
    intro T hT i j
    rw [← hxpow i j]
    exact aeval_pow_of_introspective hxr (hintro_all T hT i j)
  -- Injectivity of `T ↦ f_T(x)` on subsets of size `d`.
  have hinj : ∀ T ∈ Finset.powersetCard d (Finset.range (2 * d)),
      ∀ T' ∈ Finset.powersetCard d (Finset.range (2 * d)),
      aeval x (linProd p T) = aeval x (linProd p T') → T = T' := by
    intro T hT T' hT' hval
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.1 hT
    obtain ⟨hT'sub, hT'card⟩ := Finset.mem_powersetCard.1 hT'
    -- the two polynomials agree at all `t` points of `Rt`
    have hpolyeq : linProd p T = linProd p T' := by
      by_contra hne
      set g : K[X] := (linProd p T - linProd p T').map (algebraMap (ZMod p) K) with hg
      have hg0 : g ≠ 0 := by
        rw [hg]
        simp only [ne_eq, Polynomial.map_eq_zero_iff (algebraMap (ZMod p) K).injective,
          sub_eq_zero]
        exact hne
      have hdeg : g.natDegree ≤ d := by
        rw [hg]
        refine le_trans (Polynomial.natDegree_map_le) ?_
        refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        rw [linProd_natDegree, linProd_natDegree, hTcard, hT'card]
        simp
      have hroots : Rt.val ⊆ g.roots := by
        intro y hy
        have hy' : y ∈ Rt := hy
        rw [hRtdef] at hy'
        obtain ⟨w, hw, hwy⟩ := Finset.mem_image.1 hy'
        obtain ⟨i, j, hij⟩ := hMfspec w hw
        rw [Polynomial.mem_roots hg0]
        rw [hg]
        simp only [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
          map_sub]
        rw [← hwy, hij, ← heval T hTsub i j, ← heval T' hT'sub i j, hval, sub_self]
      have := Polynomial.card_le_degree_of_subset_roots hroots
      rw [hRtcard] at this
      omega
    exact linProd_injOn p (2 * d) (by omega) T hTsub T' hT'sub hpolyeq
  set Img : Finset K :=
    (Finset.powersetCard d (Finset.range (2 * d))).image (fun T => aeval x (linProd p T))
    with hImgdef
  have hImgcard : Img.card = (2 * d).choose d := by
    rw [hImgdef, Finset.card_image_of_injOn (fun T hT T' hT' h => hinj T hT T' hT' h),
      Finset.card_powersetCard, Finset.card_range]
  -- Pigeonhole: two of the exponents `n^i p^j` agree modulo `r`.
  have hcardlt : Mf.card < (Finset.univ : Finset (Fin (s + 1) × Fin (s + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    have h1 : t < (Nat.sqrt t + 1) ^ 2 := Nat.lt_succ_sqrt' t
    have h2 : (s + 1) ^ 2 = (s + 1) * (s + 1) := by ring
    rw [← hsdef, h2] at h1
    omega
  obtain ⟨q₁, -, q₂, -, hq12, hqeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardlt
      (f := fun q : Fin (s + 1) × Fin (s + 1) => u ^ (q.1 : ℕ) * v ^ (q.2 : ℕ))
      (fun q _ => hmem _ _)
  -- The two exponents are distinct as natural numbers.
  have hne : n ^ (q₁.1 : ℕ) * p ^ (q₁.2 : ℕ) ≠ n ^ (q₂.1 : ℕ) * p ^ (q₂.2 : ℕ) := by
    intro hcon
    obtain ⟨h1, h2⟩ := nat_pow_mul_pow_injective hn hp hnk hcon
    exact hq12 (Prod.ext (Fin.ext h1) (Fin.ext h2))
  -- Every element of `Img` is a root of `X^{m₁} - X^{m₂}`.
  have hmain : ∀ m₁ m₂ : ℕ, m₂ < m₁ → m₁ ≤ n ^ (2 * s) →
      (∀ y ∈ Img, y ^ m₁ = y ^ m₂) → False := by
    intro m₁ m₂ hlt hle hy
    set g : K[X] := X ^ m₁ - X ^ m₂ with hg
    have hg0 : g ≠ 0 := by
      intro h0
      have : g.coeff m₁ = 1 := by
        rw [hg]
        simp [Polynomial.coeff_X_pow, Nat.ne_of_gt hlt]
      rw [h0] at this
      simp at this
    have hdeg : g.natDegree ≤ m₁ := by
      rw [hg]
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      simp
      omega
    have hsub : Img.val ⊆ g.roots := by
      intro y hy'
      rw [Polynomial.mem_roots hg0]
      simp only [hg, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X]
      rw [hy y hy', sub_self]
    have hcard := Polynomial.card_le_degree_of_subset_roots hsub
    rw [hImgcard] at hcard
    have h1 : 2 ^ d ≤ (2 * d).choose d := two_pow_le_choose d
    omega
  -- Apply it to the two exponents produced by the pigeonhole principle.
  have hyall : ∀ (m₁ m₂ : ℕ) (i₁ j₁ i₂ j₂ : ℕ), m₁ = n ^ i₁ * p ^ j₁ → m₂ = n ^ i₂ * p ^ j₂ →
      u ^ i₁ * v ^ j₁ = u ^ i₂ * v ^ j₂ → ∀ y ∈ Img, y ^ m₁ = y ^ m₂ := by
    intro m₁ m₂ i₁ j₁ i₂ j₂ hm₁ hm₂ hunits y hy
    rw [hImgdef] at hy
    obtain ⟨T, hT, hTy⟩ := Finset.mem_image.1 hy
    obtain ⟨hTsub, -⟩ := Finset.mem_powersetCard.1 hT
    rw [← hTy, hm₁, hm₂, heval T hTsub i₁ j₁, heval T hTsub i₂ j₂, hunits]
  have hbound : ∀ i j : ℕ, i ≤ s → j ≤ s → n ^ i * p ^ j ≤ n ^ (2 * s) := by
    intro i j hi hj
    calc n ^ i * p ^ j ≤ n ^ s * n ^ s := by
          refine Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hi) ?_
          calc p ^ j ≤ n ^ j := Nat.pow_le_pow_left (Nat.le_of_dvd (by omega) hpn) j
            _ ≤ n ^ s := Nat.pow_le_pow_right (by omega) hj
      _ = n ^ (2 * s) := by rw [← pow_add, two_mul]
  rcases lt_trichotomy (n ^ (q₁.1 : ℕ) * p ^ (q₁.2 : ℕ)) (n ^ (q₂.1 : ℕ) * p ^ (q₂.2 : ℕ)) with
    h | h | h
  · exact hmain _ _ h (hbound _ _ (by omega) (by omega))
      (hyall _ _ _ _ _ _ rfl rfl hqeq.symm)
  · exact hne h
  · exact hmain _ _ h (hbound _ _ (by omega) (by omega))
      (hyall _ _ _ _ _ _ rfl rfl hqeq)

/-- **The AKS criterion.** If `n ≥ 2` has a prime factor `p > r`, `n` is coprime to `r`, the
multiplicative order of `n` modulo `r` exceeds `100 B²` (where `n < 2 ^ B`), and `n` is
introspective for all the linear polynomials `X + a` with `a ≤ 4(⌊√r⌋+1)B`, then `n` is a power
of `p`. -/
theorem prime_pow_of_introspective
    (n r p B : ℕ) (hp : p.Prime)
    (hn : 2 ≤ n) (hB : n < 2 ^ B) (hr2 : 2 ≤ r) (hcopn : Nat.Coprime n r)
    (hpn : p ∣ n) (hrp : r < p)
    (hord : ∀ i, 1 ≤ i → i ≤ 100 * B ^ 2 → (n : ZMod r) ^ i ≠ 1)
    (hintro : ∀ a : ℕ, a ≤ 4 * (Nat.sqrt r + 1) * B →
        Introspective r n ((X + C ((a : ℕ) : ZMod n)) : (ZMod n)[X])) :
    ∃ k, n = p ^ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero r := ⟨by omega⟩
  have hcopp : Nat.Coprime p r := Nat.Coprime.coprime_dvd_left hpn hcopn
  obtain ⟨d0, hd0⟩ : ∃ d0 : ℕ, d0 = orderOf (ZMod.unitOfCoprime p hcopp) := ⟨_, rfl⟩
  have hd0pos : 0 < d0 := hd0 ▸ orderOf_pos _
  let K := GaloisField p d0
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = p ^ d0 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p d0 hd0pos.ne'
  have hcardU : Fintype.card Kˣ = p ^ d0 - 1 := by
    rw [Fintype.card_units, hcardK]
  have hppos : 0 < p ^ d0 := Nat.pow_pos hp.pos
  have hrdvd : r ∣ Fintype.card Kˣ := by
    rw [hcardU]
    have h1 : ((p ^ d0 : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
      have h3 : (((ZMod.unitOfCoprime p hcopp) ^ d0 : (ZMod r)ˣ) : ZMod r) = 1 := by
        rw [hd0, pow_orderOf_eq_one]; simp
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime] at h3
      push_cast
      simpa using h3
    have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
    exact (Nat.modEq_iff_dvd' (by omega)).1 h4.symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hNcard : Nat.card Kˣ = Fintype.card Kˣ := Nat.card_eq_fintype_card
  have hp2 : 1 < p ^ d0 := Nat.one_lt_pow hd0pos.ne' hp.one_lt
  have hNpos : 0 < Nat.card Kˣ := by rw [hNcard, hcardU]; omega
  have hrN : r ∣ Nat.card Kˣ := by rw [hNcard]; exact hrdvd
  have hdiv0 : Nat.card Kˣ / r ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd hNpos hrN) (by omega : 0 < r)
    omega
  have hxord : orderOf ((g ^ (Nat.card Kˣ / r) : Kˣ) : K) = r := by
    rw [orderOf_units, orderOf_pow' g hdiv0, hg,
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd hrN)]
    exact Nat.div_div_self hrN (by omega)
  exact prime_pow_of_introspective_aux n r p B (K := K) ((g ^ (Nat.card Kˣ / r) : Kˣ) : K) hxord
    hn hB hr2 hcopn hpn hrp hord hintro

end AKS

import Mathlib
import RequestProject.AKS.Core

/-!
# Existence of a small auxiliary modulus `r`

The AKS algorithm needs a modulus `r` for which the multiplicative order of `n` modulo `r`
exceeds a given threshold `K`.  This file shows that such an `r` can always be found below
`2 * B * K ^ 2`, where `n < 2 ^ B`.  The proof uses the classical fact that
`lcm (1, …, 2M)` is at least `binomial(2M, M) ≥ 2 ^ M`.
-/

namespace AKS

/-- `lcmUpTo m = lcm (1, 2, …, m)`. -/
def lcmUpTo (m : ℕ) : ℕ := (Finset.Icc 1 m).lcm id

theorem lcmUpTo_ne_zero (m : ℕ) : lcmUpTo m ≠ 0 := by
  rw [lcmUpTo, Ne, Finset.lcm_eq_zero_iff]
  simp only [Set.mem_image, Finset.mem_coe, id_eq, not_exists]
  intro r
  rintro ⟨hr, hr0⟩
  obtain ⟨h1, -⟩ := Finset.mem_Icc.1 hr
  omega

theorem dvd_lcmUpTo {r m : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ m) : r ∣ lcmUpTo m :=
  Finset.dvd_lcm (Finset.mem_Icc.2 ⟨h1, h2⟩)

theorem choose_dvd_lcmUpTo (M : ℕ) : (2 * M).choose M ∣ lcmUpTo (2 * M) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  have hL : lcmUpTo (2 * M) ≠ 0 := lcmUpTo_ne_zero _
  have hC : (2 * M).choose M ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [← Nat.factorization_le_iff_dvd hC hL]
  intro q
  by_cases hq : q.Prime
  · haveI : Fact q.Prime := ⟨hq⟩
    have h1 : q ^ ((2 * M).choose M).factorization q ≤ 2 * M :=
      Nat.pow_factorization_choose_le (by omega)
    have h2 : q ^ ((2 * M).choose M).factorization q ∣ lcmUpTo (2 * M) :=
      dvd_lcmUpTo (Nat.one_le_pow _ _ hq.pos) h1
    exact (Nat.Prime.pow_dvd_iff_le_factorization hq hL).1 h2
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

theorem two_pow_le_lcmUpTo (M : ℕ) : 2 ^ M ≤ lcmUpTo (2 * M) := by
  refine le_trans (AKS.two_pow_le_choose M) ?_
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (lcmUpTo_ne_zero _)) (choose_dvd_lcmUpTo M)

/-- There is a small `r ≥ 2` for which `n` has multiplicative order greater than `K`
modulo `r` (expressed as: no power `n ^ i` with `1 ≤ i ≤ K` is `1` modulo `r`). -/
theorem exists_good_r (n B K : ℕ) (hn : 2 ≤ n) (hB : n < 2 ^ B) (hK : 1 ≤ K) :
    ∃ r, 2 ≤ r ∧ r ≤ 2 * (B * K ^ 2) ∧ ∀ i, 1 ≤ i → i ≤ K → n ^ i % r ≠ 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  set M := B * K ^ 2 with hM
  set P : ℕ := ∏ i ∈ Finset.Icc 1 K, (n ^ i - 1) with hP
  have hPpos : 0 < P := by
    rw [hP]
    refine Finset.prod_pos ?_
    intro i hi
    obtain ⟨hi1, -⟩ := Finset.mem_Icc.1 hi
    have : 2 ≤ n ^ i := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ n ^ i := Nat.pow_le_pow_left hn 1 |>.trans (Nat.pow_le_pow_right (by omega) hi1)
    omega
  -- every `r ∈ [1, 2M]` divides `P`
  have hdvd : ∀ r ∈ Finset.Icc 1 (2 * M), (id r : ℕ) ∣ P := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.1 hr
    rcases Nat.lt_or_ge r 2 with hlt | hge
    · have : r = 1 := by omega
      simp [this]
    · obtain ⟨i, hi1, hiK, hieq⟩ := hcon r hge hr2
      have hni : 1 ≤ n ^ i := Nat.one_le_pow _ _ (by omega)
      have hrd : r ∣ n ^ i - 1 := by
        have h1 : n ^ i % r = 1 % r := by
          rw [hieq, Nat.mod_eq_of_lt (by omega)]
        exact (Nat.modEq_iff_dvd' hni).1 (Nat.ModEq.symm h1)
      refine dvd_trans hrd ?_
      rw [hP]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨hi1, hiK⟩)
  have hlcm : lcmUpTo (2 * M) ∣ P := Finset.lcm_dvd hdvd
  have h1 : 2 ^ M ≤ P := le_trans (two_pow_le_lcmUpTo M) (Nat.le_of_dvd hPpos hlcm)
  -- but `P` is small
  have h2 : P ≤ n ^ (K * K) := by
    calc P ≤ ∏ i ∈ Finset.Icc 1 K, n ^ i := by
          refine Finset.prod_le_prod' ?_
          intro i _
          omega
      _ = n ^ (∑ i ∈ Finset.Icc 1 K, i) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ n ^ (K * K) := by
          refine Nat.pow_le_pow_right (by omega) ?_
          calc (∑ i ∈ Finset.Icc 1 K, i) ≤ ∑ _i ∈ Finset.Icc 1 K, K := by
                refine Finset.sum_le_sum ?_
                intro i hi
                exact (Finset.mem_Icc.1 hi).2
            _ = (Finset.Icc 1 K).card * K := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ K * K := by
                have hcard : (Finset.Icc 1 K).card = K := by rw [Nat.card_Icc]; omega
                rw [hcard]
  have h3 : n ^ (K * K) < 2 ^ M := by
    calc n ^ (K * K) < (2 ^ B) ^ (K * K) := Nat.pow_lt_pow_left hB (by positivity)
      _ = 2 ^ (B * (K * K)) := by rw [← pow_mul]
      _ = 2 ^ M := by rw [hM]; congr 1; ring
  omega

end AKS

import RequestProject.AKS.Introspective

/-!
# Polynomials modulo `X ^ r - 1` represented by coefficient lists

The AKS algorithm computes with polynomials in `(ZMod n)[X] / (X ^ r - 1)`.  Here we represent
such a polynomial by the list of its `r` coefficients (natural numbers `< n`) and give the
schoolbook implementations of multiplication and of binary exponentiation, together with proofs
that they implement the intended ring operations.
-/

namespace AKS

open Polynomial Finset

/-! ## Congruence modulo `X ^ r - 1` -/

/-- `Cong r f g` means `f ≡ g` modulo `X ^ r - 1`. -/
def Cong {R : Type*} [CommRing R] (r : ℕ) (f g : R[X]) : Prop := (X ^ r - 1 : R[X]) ∣ f - g

namespace Cong

variable {R : Type*} [CommRing R] {r : ℕ} {f g h : R[X]}

theorem refl (r : ℕ) (f : R[X]) : Cong r f f := by simp [Cong]

theorem symm (hfg : Cong r f g) : Cong r g f := by
  obtain ⟨q, hq⟩ := hfg
  exact ⟨-q, by linear_combination -hq⟩

theorem trans (hfg : Cong r f g) (hgh : Cong r g h) : Cong r f h := by
  obtain ⟨q₁, h₁⟩ := hfg
  obtain ⟨q₂, h₂⟩ := hgh
  exact ⟨q₁ + q₂, by linear_combination h₁ + h₂⟩

theorem add {f' g' : R[X]} (h₁ : Cong r f f') (h₂ : Cong r g g') : Cong r (f + g) (f' + g') := by
  obtain ⟨q₁, e₁⟩ := h₁
  obtain ⟨q₂, e₂⟩ := h₂
  exact ⟨q₁ + q₂, by linear_combination e₁ + e₂⟩

theorem mul {f' g' : R[X]} (h₁ : Cong r f f') (h₂ : Cong r g g') : Cong r (f * g) (f' * g') := by
  obtain ⟨q₁, e₁⟩ := h₁
  obtain ⟨q₂, e₂⟩ := h₂
  exact ⟨q₁ * g + f' * q₂, by linear_combination g * e₁ + f' * e₂⟩

theorem pow {f g : R[X]} (h : Cong r f g) (e : ℕ) : Cong r (f ^ e) (g ^ e) := by
  induction e with
  | zero => simpa using Cong.refl r 1
  | succ k ih => simpa [_root_.pow_succ] using ih.mul h

end Cong

/-- `X ^ a ≡ X ^ (a % r)` modulo `X ^ r - 1`. -/
theorem cong_X_pow_mod {R : Type*} [CommRing R] (r a : ℕ) (hr : 0 < r) :
    Cong r (X ^ a : R[X]) (X ^ (a % r)) := by
  refine ⟨X ^ (a % r) * (∑ i ∈ Finset.range (a / r), (X ^ r) ^ i), ?_⟩
  have hgeom : ((X : R[X]) ^ r - 1) * (∑ i ∈ Finset.range (a / r), (X ^ r) ^ i)
      = (X ^ r) ^ (a / r) - 1 := by
    rw [mul_comm]
    exact geom_sum_mul _ _
  calc (X : R[X]) ^ a - X ^ (a % r)
      = X ^ (a % r) * ((X ^ r) ^ (a / r) - 1) := by
        rw [mul_sub, mul_one, ← pow_mul, ← pow_add]
        congr 2
        exact (Nat.mod_add_div a r).symm
    _ = (X ^ r - 1) * (X ^ (a % r) * (∑ i ∈ Finset.range (a / r), (X ^ r) ^ i)) := by
        rw [← hgeom]; ring

/-! ## Coefficient lists -/

/-- The polynomial represented by a coefficient list of length `r`. -/
noncomputable def emb (n r : ℕ) (l : List ℕ) : (ZMod n)[X] :=
  ∑ i ∈ Finset.range r, C ((l.getD i 0 : ℕ) : ZMod n) * X ^ i

/-- The coefficient list of the constant polynomial `1`. -/
def pone (n r : ℕ) : List ℕ := (List.range r).map (fun i => if i = 0 then 1 % n else 0)

/-- The coefficient list of `X ^ k + c`. -/
def pXAdd (n r k c : ℕ) : List ℕ :=
  (List.range r).map (fun i => ((if i = k % r then 1 else 0) + (if i = 0 then c else 0)) % n)

/-- Multiplication of coefficient lists modulo `X ^ r - 1` and `n`. -/
def pmul (n r : ℕ) (f g : List ℕ) : List ℕ :=
  (List.range r).map fun k =>
    (∑ q ∈ (Finset.range r ×ˢ Finset.range r) with (q.1 + q.2) % r = k,
      f.getD q.1 0 * g.getD q.2 0) % n

/-- Binary exponentiation of coefficient lists. -/
def ppow (n r : ℕ) (base : List ℕ) : ℕ → List ℕ
  | 0 => pone n r
  | (e + 1) =>
      let h := ppow n r base ((e + 1) / 2)
      let sq := pmul n r h h
      if (e + 1) % 2 = 0 then sq else pmul n r sq base
decreasing_by omega

theorem length_pone (n r : ℕ) : (pone n r).length = r := by simp [pone]

theorem length_pXAdd (n r k c : ℕ) : (pXAdd n r k c).length = r := by simp [pXAdd]

theorem length_pmul (n r : ℕ) (f g : List ℕ) : (pmul n r f g).length = r := by simp [pmul]

theorem length_ppow (n r : ℕ) (base : List ℕ) (e : ℕ) : (ppow n r base e).length = r := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
      match e with
      | 0 => simp [ppow, length_pone]
      | (m + 1) =>
          rw [ppow]
          split <;> simp [length_pmul]

theorem Cong.sum {R : Type*} [CommRing R] {ι : Type*} {r : ℕ} (s : Finset ι) {u w : ι → R[X]}
    (h : ∀ i ∈ s, Cong r (u i) (w i)) : Cong r (∑ i ∈ s, u i) (∑ i ∈ s, w i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Cong.refl r 0
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem getD_pmul_lt (n r : ℕ) (hn : 0 < n) (f g : List ℕ) (k : ℕ) (hk : k < r) :
    (pmul n r f g).getD k 0 < n := by
  rw [pmul, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk]
  simpa using Nat.mod_lt _ hn

theorem getD_ppow_lt (n r : ℕ) (hn : 1 < n) (base : List ℕ) (e k : ℕ) (hk : k < r) :
    (ppow n r base e).getD k 0 < n := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
      match e with
      | 0 =>
          rw [ppow, pone, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range hk]
          simp only [Option.map_some, Option.getD_some]
          split
          · exact Nat.mod_lt _ (by omega)
          · omega
      | (m + 1) =>
          rw [ppow]
          split <;> exact getD_pmul_lt n r (by omega) _ _ k hk

/-! ## The coefficient lists implement the ring operations -/

theorem emb_getD (n r : ℕ) (l : List ℕ) (k : ℕ) (hk : k < r) :
    (emb n r l).coeff k = ((l.getD k 0 : ℕ) : ZMod n) := by
  rw [emb, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hbk
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hbk]
  · intro h
    exact absurd (Finset.mem_range.2 hk) h

theorem emb_pone (n r : ℕ) (hr : 0 < r) : emb n r (pone n r) = 1 := by
  rw [emb, pone]
  rw [Finset.sum_eq_single 0]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr]
    simp
  · intro b hb hb0
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (Finset.mem_range.1 hb)]
    simp [hb0]
  · intro h
    exact absurd (Finset.mem_range.2 hr) h

theorem emb_pXAdd (n r k c : ℕ) (hr : 0 < r) :
    Cong r (emb n r (pXAdd n r k c)) (X ^ k + C ((c : ℕ) : ZMod n)) := by
  have hval : ∀ i < r, (((pXAdd n r k c).getD i 0 : ℕ) : ZMod n) =
      (if i = k % r then 1 else 0) + (if i = 0 then ((c : ℕ) : ZMod n) else 0) := by
    intro i hi
    rw [pXAdd, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some, Option.getD_some, ZMod.natCast_mod]
    push_cast
    split <;> split <;> simp
  have h1 : emb n r (pXAdd n r k c) = X ^ (k % r) + C ((c : ℕ) : ZMod n) := by
    rw [emb]
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [hval i (Finset.mem_range.1 hi)])]
    simp only [map_add, add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single (k % r)]
      · simp
      · intro b _ hbk
        simp [hbk]
      · intro h
        exact absurd (Finset.mem_range.2 (Nat.mod_lt _ hr)) h
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb0
        simp [hb0]
      · intro h
        exact absurd (Finset.mem_range.2 hr) h
  rw [h1]
  exact (cong_X_pow_mod r k hr).symm.add (Cong.refl r _)

theorem emb_pmul (n r : ℕ) (hr : 0 < r) (f g : List ℕ) :
    Cong r (emb n r (pmul n r f g)) (emb n r f * emb n r g) := by
  classical
  set F : ℕ → ZMod n := fun i => ((f.getD i 0 : ℕ) : ZMod n) with hF
  set G : ℕ → ZMod n := fun i => ((g.getD i 0 : ℕ) : ZMod n) with hG
  -- the product, expanded
  have hprod : emb n r f * emb n r g =
      ∑ q ∈ Finset.range r ×ˢ Finset.range r, C (F q.1 * G q.2) * X ^ (q.1 + q.2) := by
    rw [emb, emb, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  -- reduce the exponents modulo r
  have hstep : Cong r (∑ q ∈ Finset.range r ×ˢ Finset.range r,
      C (F q.1 * G q.2) * X ^ ((q.1 + q.2) % r))
      (∑ q ∈ Finset.range r ×ˢ Finset.range r, C (F q.1 * G q.2) * X ^ (q.1 + q.2)) := by
    refine Cong.sum _ fun q _ => ?_
    exact (Cong.refl r _).mul (cong_X_pow_mod r (q.1 + q.2) hr).symm
  -- group by the residue
  have hgroup : ∑ q ∈ Finset.range r ×ˢ Finset.range r,
      C (F q.1 * G q.2) * X ^ ((q.1 + q.2) % r) =
      ∑ k ∈ Finset.range r, (∑ q ∈ (Finset.range r ×ˢ Finset.range r) with (q.1 + q.2) % r = k,
        C (F q.1 * G q.2)) * X ^ k := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (t := Finset.range r) (g := fun q : ℕ × ℕ => (q.1 + q.2) % r)
      (fun q _ => Finset.mem_range.2 (Nat.mod_lt _ hr))
      (fun q => C (F q.1 * G q.2) * X ^ ((q.1 + q.2) % r))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [(Finset.mem_filter.1 hq).2]
  -- the left-hand side
  have hlhs : emb n r (pmul n r f g) =
      ∑ k ∈ Finset.range r, (∑ q ∈ (Finset.range r ×ˢ Finset.range r) with (q.1 + q.2) % r = k,
        C (F q.1 * G q.2)) * X ^ k := by
    rw [emb]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < r := Finset.mem_range.1 hk
    rw [pmul, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk']
    simp only [Option.map_some, Option.getD_some, ZMod.natCast_mod]
    rw [Nat.cast_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    push_cast
    rw [map_mul]
  rw [hlhs, ← hgroup, hprod]
  exact hstep

theorem emb_ppow (n r : ℕ) (hr : 0 < r) (base : List ℕ) (e : ℕ) :
    Cong r (emb n r (ppow n r base e)) ((emb n r base) ^ e) := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
      match e with
      | 0 => rw [ppow, emb_pone n r hr]; simpa using Cong.refl r 1
      | (m + 1) =>
          have hhalf : (m + 1) / 2 < m + 1 := by omega
          have ihh := ih ((m + 1) / 2) hhalf
          rw [ppow]
          have hsq : Cong r (emb n r (pmul n r (ppow n r base ((m + 1) / 2))
              (ppow n r base ((m + 1) / 2))))
              ((emb n r base) ^ ((m + 1) / 2 * 2)) := by
            refine (emb_pmul n r hr _ _).trans ?_
            have := ihh.mul ihh
            refine this.trans ?_
            rw [← pow_add]
            have : (m + 1) / 2 + (m + 1) / 2 = (m + 1) / 2 * 2 := by ring
            rw [this]
            exact Cong.refl r _
          split
          · rename_i heven
            have : (m + 1) / 2 * 2 = m + 1 := by omega
            rw [this] at hsq
            exact hsq
          · rename_i hodd
            refine (emb_pmul n r hr _ _).trans ?_
            refine (hsq.mul (Cong.refl r (emb n r base))).trans ?_
            rw [← pow_succ]
            have hexp : (m + 1) / 2 * 2 + 1 = m + 1 := by omega
            rw [hexp]
            exact Cong.refl r _

theorem degree_emb_lt (n r : ℕ) (l : List ℕ) : (emb n r l).degree < (r : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  have hm' : r ≤ m := by exact_mod_cast hm
  rw [emb, Polynomial.finset_sum_coeff]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i < r := Finset.mem_range.1 hi
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (m = i)), mul_zero]

theorem emb_injective (n r : ℕ) [Fact n.Prime] (hr : 0 < r) {f g : List ℕ}
    (hf : f.length = r) (hg : g.length = r)
    (hfb : ∀ k < r, f.getD k 0 < n) (hgb : ∀ k < r, g.getD k 0 < n)
    (h : Cong r (emb n r f) (emb n r g)) : f = g := by
  have hn : 1 < n := (Fact.out (p := n.Prime)).one_lt
  haveI : NeZero n := ⟨by omega⟩
  have hdegdvd : (X ^ r - 1 : (ZMod n)[X]).degree = (r : ℕ) := by
    have : (X ^ r - 1 : (ZMod n)[X]) = X ^ r - C 1 := by simp
    rw [this, Polynomial.degree_X_pow_sub_C hr]
  have hzero : emb n r f - emb n r g = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt h ?_
    rw [hdegdvd]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt (degree_emb_lt n r f) (degree_emb_lt n r g))
  have heq : emb n r f = emb n r g := by
    have := sub_eq_zero.1 hzero
    exact this
  refine List.ext_getElem (by omega) ?_
  intro k h1 h2
  have hk : k < r := by omega
  have hcoeff : ((f.getD k 0 : ℕ) : ZMod n) = ((g.getD k 0 : ℕ) : ZMod n) := by
    rw [← emb_getD n r f k hk, ← emb_getD n r g k hk, heq]
  have hval : f.getD k 0 = g.getD k 0 := by
    have h3 : ((f.getD k 0 : ℕ) : ZMod n).val = ((g.getD k 0 : ℕ) : ZMod n).val := by
      rw [hcoeff]
    rwa [ZMod.val_cast_of_lt (hfb k hk), ZMod.val_cast_of_lt (hgb k hk)] at h3
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at hval

end AKS

import RequestProject.AKS.Core
import RequestProject.AKS.SmallR
import RequestProject.AKS.PolyList

/-!
# The AKS primality test

This file defines the decision procedure `AKS.aksTest : ℕ → Bool` and proves
`AKS.aksTest_iff_prime : aksTest n = true ↔ n.Prime`.

All the searches performed by the test are bounded by explicit polynomials in the bit length
of the input (see `AKS.findR_le`).
-/

namespace AKS

open Polynomial Finset

/-- Bit length of `n`. -/
def bitLen (n : ℕ) : ℕ := Nat.log 2 n + 1

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := Nat.lt_pow_succ_log_self (by norm_num) n

theorem one_le_bitLen (n : ℕ) : 1 ≤ bitLen n := by simp [bitLen]

/-- The threshold for the multiplicative order of `n` modulo `r`. -/
def thr (n : ℕ) : ℕ := 100 * (bitLen n) ^ 2

theorem one_le_thr (n : ℕ) : 1 ≤ thr n := by
  have := one_le_bitLen n
  simp only [thr]
  nlinarith

/-- The bound within which a suitable `r` is guaranteed to exist. -/
def rBound (n : ℕ) : ℕ := 2 * (bitLen n * (thr n) ^ 2)

/-- The number of linear polynomials that get tested. -/
def ell (n r : ℕ) : ℕ := 4 * (Nat.sqrt r + 1) * bitLen n

/-- `n` has no power `n ^ i`, `1 ≤ i ≤ K`, congruent to `1` modulo `r`. -/
def ordOK (n r K : ℕ) : Bool := (List.range K).all (fun i => n ^ (i + 1) % r != 1)

theorem ordOK_iff (n r K : ℕ) :
    ordOK n r K = true ↔ ∀ i, 1 ≤ i → i ≤ K → n ^ i % r ≠ 1 := by
  simp only [ordOK, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]
  constructor
  · intro h i hi1 hiK
    have := h (i - 1) (by omega)
    rwa [show i - 1 + 1 = i by omega] at this
  · intro h i hi
    exact h (i + 1) (by omega) (by omega)

/-- The candidate list for the auxiliary modulus. -/
def rPred (n r : ℕ) : Bool := decide (2 ≤ r) && ordOK n r (thr n)

/-- The auxiliary modulus used by the test: the first `r ≥ 2` below `rBound n`
for which the order of `n` mod `r` exceeds `thr n`. -/
def findR (n : ℕ) : ℕ :=
  ((List.range (rBound n + 1)).find? (fun r => rPred n r)).getD 2

theorem exists_r_in_range (n : ℕ) (hn : 2 ≤ n) :
    ∃ r ∈ List.range (rBound n + 1), rPred n r = true := by
  obtain ⟨r, hr2, hrle, hr⟩ :=
    exists_good_r n (bitLen n) (thr n) hn (lt_two_pow_bitLen n) (one_le_thr n)
  refine ⟨r, List.mem_range.2 (by simp only [rBound]; omega), ?_⟩
  simp only [rPred, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hr2, (ordOK_iff n r (thr n)).2 hr⟩

theorem findR_spec (n : ℕ) (hn : 2 ≤ n) : rPred n (findR n) = true ∧ findR n ≤ rBound n := by
  rcases h : (List.range (rBound n + 1)).find? (fun r => rPred n r) with _ | r
  · exfalso
    rw [List.find?_eq_none] at h
    obtain ⟨r, hr, hr'⟩ := exists_r_in_range n hn
    exact (h r hr) hr'
  · have h1 : rPred n r = true := List.find?_some h
    have h2 : r ∈ List.range (rBound n + 1) := List.mem_of_find?_eq_some h
    refine ⟨?_, ?_⟩ <;> rw [findR, h] <;> simp only [Option.getD_some]
    · exact h1
    · exact Nat.lt_succ_iff.1 (List.mem_range.1 h2)

theorem two_le_findR (n : ℕ) (hn : 2 ≤ n) : 2 ≤ findR n := by
  have := (findR_spec n hn).1
  simp only [rPred, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

theorem findR_ord (n : ℕ) (hn : 2 ≤ n) :
    ∀ i, 1 ≤ i → i ≤ thr n → n ^ i % findR n ≠ 1 := by
  have := (findR_spec n hn).1
  simp only [rPred, Bool.and_eq_true, decide_eq_true_eq] at this
  exact (ordOK_iff n (findR n) (thr n)).1 this.2

theorem findR_le (n : ℕ) (hn : 2 ≤ n) : findR n ≤ rBound n := (findR_spec n hn).2

/-- Whether `n` is a perfect power `a ^ b` with `b ≥ 2`. -/
def isPerfectPower (n : ℕ) : Bool :=
  (List.range (n + 1)).any fun a =>
    (List.range (bitLen n + 1)).any fun b => decide (2 ≤ b) && (n == a ^ b)

theorem isPerfectPower_iff (n : ℕ) (hn : 2 ≤ n) :
    isPerfectPower n = true ↔ ∃ a b, 2 ≤ b ∧ n = a ^ b := by
  simp only [isPerfectPower, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨a, -, b, -, hb, hab⟩
    exact ⟨a, b, hb, hab⟩
  · rintro ⟨a, b, hb, hab⟩
    have ha2 : 2 ≤ a := by
      rcases Nat.lt_or_ge a 2 with h | h
      · interval_cases a
        · rw [zero_pow (by omega)] at hab; omega
        · rw [one_pow] at hab; omega
      · exact h
    have han : a ≤ n := by
      calc a = a ^ 1 := (pow_one a).symm
        _ ≤ a ^ b := Nat.pow_le_pow_right (by omega) (by omega)
        _ = n := hab.symm
    have hbb : b ≤ bitLen n := by
      have h1 : 2 ^ b ≤ n := by
        calc 2 ^ b ≤ a ^ b := Nat.pow_le_pow_left ha2 b
          _ = n := hab.symm
      have h2 : b ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 h1
      simp only [bitLen]
      omega
    exact ⟨a, by omega, b, by omega, hb, hab⟩

/-- No `a` with `2 ≤ a ≤ r` exhibits a nontrivial factor of `n`. -/
def gcdOK (n r : ℕ) : Bool :=
  (List.range (r + 1)).all fun a => decide (a < 2) || (Nat.gcd a n == 1) || (Nat.gcd a n == n)

theorem gcdOK_iff (n r : ℕ) :
    gcdOK n r = true ↔ ∀ a, 2 ≤ a → a ≤ r → Nat.gcd a n = 1 ∨ Nat.gcd a n = n := by
  simp only [gcdOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  constructor
  · intro h a ha2 har
    rcases h a (by omega) with (h1 | h1) | h1
    · omega
    · exact Or.inl h1
    · exact Or.inr h1
  · intro h a ha
    rcases Nat.lt_or_ge a 2 with h1 | h1
    · exact Or.inl (Or.inl h1)
    · rcases h a h1 (by omega) with h2 | h2
      · exact Or.inl (Or.inr h2)
      · exact Or.inr h2

/-- The polynomial congruence test for a single `a`. -/
def polyOK (n r a : ℕ) : Bool := ppow n r (pXAdd n r 1 a) n == pXAdd n r n a

/-- **The AKS primality test.** -/
def aksTest (n : ℕ) : Bool :=
  if n < 2 then false
  else if isPerfectPower n then false
  else
    let r := findR n
    if gcdOK n r = false then false
    else if n ≤ r then true
    else (List.range (ell n r + 1)).all fun a => polyOK n r a

end AKS

import Mathlib

/-!
# Numeric estimates used in the AKS argument

Throughout, `B` plays the role of a bound on the bit length of `n` (so `n < 2 ^ B`),
`t` is the size of the monoid generated by `n` and `p` modulo `r`, `s = ⌊√t⌋` and
`d = 2 (s+1) B`.
-/

namespace AKS

theorem sqrt_ge_of_lt {B t : ℕ} (ht : 100 * B ^ 2 < t) : 10 * B ≤ Nat.sqrt t := by
  refine Nat.le_sqrt.2 ?_
  nlinarith [sq_nonneg B]

theorem d_lt_t {B t : ℕ} (ht : 100 * B ^ 2 < t) :
    2 * (Nat.sqrt t + 1) * B < t := by
  have h1 : 10 * B ≤ Nat.sqrt t := sqrt_ge_of_lt ht
  have h2 : Nat.sqrt t * Nat.sqrt t ≤ t := by
    have := Nat.sqrt_le' t; nlinarith
  have h3 : Nat.sqrt t ≤ t := Nat.sqrt_le_self t
  have hkey : 10 * B * Nat.sqrt t ≤ Nat.sqrt t * Nat.sqrt t :=
    Nat.mul_le_mul_right _ h1
  have ht0 : 0 < t := by nlinarith
  nlinarith

theorem two_d_le {B t r : ℕ} (ht : 100 * B ^ 2 < t) (htr : t ≤ r) :
    2 * (2 * (Nat.sqrt t + 1) * B) ≤ r := by
  have h1 : 10 * B ≤ Nat.sqrt r := sqrt_ge_of_lt (lt_of_lt_of_le ht htr)
  have h2 : Nat.sqrt r * Nat.sqrt r ≤ r := by
    have := Nat.sqrt_le' r; nlinarith
  have h3 : Nat.sqrt t ≤ Nat.sqrt r := Nat.sqrt_le_sqrt htr
  have h4 : Nat.sqrt r ≤ r := Nat.sqrt_le_self r
  have hkey : 10 * B * Nat.sqrt r ≤ Nat.sqrt r * Nat.sqrt r :=
    Nat.mul_le_mul_right _ h1
  have hkey2 : Nat.sqrt t * B ≤ Nat.sqrt r * B := Nat.mul_le_mul_right _ h3
  nlinarith

theorem pow_lt_two_pow_d {n B t : ℕ} (hn : 2 ≤ n) (hB : n < 2 ^ B) (ht : 100 * B ^ 2 < t) :
    n ^ (2 * Nat.sqrt t) < 2 ^ (2 * (Nat.sqrt t + 1) * B) := by
  have hB1 : 1 ≤ B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · rw [h] at hB; simp at hB; omega
    · exact h
  have h1 : 10 * B ≤ Nat.sqrt t := sqrt_ge_of_lt ht
  calc n ^ (2 * Nat.sqrt t) < (2 ^ B) ^ (2 * Nat.sqrt t) :=
        Nat.pow_lt_pow_left hB (by omega)
    _ = 2 ^ (B * (2 * Nat.sqrt t)) := by rw [← pow_mul]
    _ ≤ 2 ^ (2 * (Nat.sqrt t + 1) * B) := Nat.pow_le_pow_right (by omega) (by ring_nf; omega)

end AKS

import Mathlib

/-!
# Introspective numbers

Following Agrawal–Kayal–Saxena, a natural number `m` is *introspective* for a polynomial
`f` (with respect to a modulus `r`) when

  `f(X)^m ≡ f(X^m)  (mod X^r - 1)`.

This file develops the basic closure properties: introspective numbers are closed under
multiplication, and for a fixed `m` the polynomials for which `m` is introspective are
closed under multiplication.
-/

namespace AKS

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `m` is introspective for `f` modulo `X ^ r - 1`. -/
def Introspective (r m : ℕ) (f : R[X]) : Prop :=
  (X ^ r - 1 : R[X]) ∣ f ^ m - f.comp (X ^ m)

theorem introspective_one (r : ℕ) (f : R[X]) : Introspective r 1 f := by
  simp [Introspective]

theorem Introspective.map {r m : ℕ} {f : R[X]} (φ : R →+* S) (h : Introspective r m f) :
    Introspective r m (f.map φ) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q.map φ, ?_⟩
  have := congrArg (Polynomial.map φ) hq
  simpa [Polynomial.map_comp] using this

/-- Substituting `X ^ k` into a polynomial divisible by `X ^ r - 1` gives a polynomial
divisible by `X ^ (r * k) - 1`. -/
theorem dvd_comp_of_dvd {r k : ℕ} {A : R[X]} (h : (X ^ r - 1 : R[X]) ∣ A) :
    (X ^ (r * k) - 1 : R[X]) ∣ A.comp (X ^ k) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q.comp (X ^ k), ?_⟩
  rw [hq, mul_comp, sub_comp, pow_comp, X_comp, one_comp, ← pow_mul, mul_comm k r]

theorem X_pow_sub_one_dvd (r k : ℕ) :
    (X ^ r - 1 : R[X]) ∣ X ^ (r * k) - 1 := by
  have h := sub_dvd_pow_sub_pow ((X : R[X]) ^ r) 1 k
  rw [← pow_mul, one_pow] at h
  simpa using h

/-- Introspective exponents are closed under multiplication. -/
theorem Introspective.mul_exp {r m m' : ℕ} {f : R[X]}
    (h : Introspective r m f) (h' : Introspective r m' f) :
    Introspective r (m * m') f := by
  show (X ^ r - 1 : R[X]) ∣ _
  have key : f ^ (m * m') - f.comp (X ^ (m * m')) =
      ((f ^ m) ^ m' - (f.comp (X ^ m)) ^ m') +
        ((f ^ m' - f.comp (X ^ m')).comp (X ^ m)) := by
    have hc : (f.comp (X ^ m')).comp (X ^ m) = f.comp (X ^ (m * m')) := by
      rw [Polynomial.comp_assoc]
      congr 1
      simp [← pow_mul, mul_comm]
    simp only [sub_comp, pow_comp, X_comp, hc]
    rw [pow_mul]
    ring
  rw [key]
  refine dvd_add ?_ ?_
  · exact dvd_trans h (sub_dvd_pow_sub_pow _ _ m')
  · have := dvd_comp_of_dvd (k := m) h'
    exact dvd_trans (X_pow_sub_one_dvd r m) this

/-- For a fixed exponent, introspective polynomials are closed under multiplication. -/
theorem Introspective.mul_poly {r m : ℕ} {f g : R[X]}
    (hf : Introspective r m f) (hg : Introspective r m g) :
    Introspective r m (f * g) := by
  show (X ^ r - 1 : R[X]) ∣ _
  have key : (f * g) ^ m - (f * g).comp (X ^ m) =
      (f ^ m - f.comp (X ^ m)) * g ^ m + f.comp (X ^ m) * (g ^ m - g.comp (X ^ m)) := by
    simp only [mul_comp, mul_pow]
    ring
  rw [key]
  exact dvd_add (hf.mul_right _) (hg.mul_left _)

theorem introspective_one_poly (r m : ℕ) : Introspective r m (1 : R[X]) := by
  simp [Introspective]

theorem Introspective.prod {r m : ℕ} {ι : Type*} (s : Finset ι) {f : ι → R[X]}
    (hf : ∀ i ∈ s, Introspective r m (f i)) :
    Introspective r m (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using introspective_one_poly (R := R) r m
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).mul_poly
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- In characteristic `p`, every polynomial is introspective for `p`. -/
theorem introspective_char (p : ℕ) [Fact p.Prime] (r : ℕ) (f : (ZMod p)[X]) :
    Introspective r p f := by
  have : f ^ p = f.comp (X ^ p) := by
    rw [← ZMod.expand_card f, Polynomial.expand_eq_comp_X_pow]
  simp [Introspective, this]

end AKS

