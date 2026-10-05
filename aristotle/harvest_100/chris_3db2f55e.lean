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

import RequestProject.AKS.Defs

/-!
# Introspective exponents

Fix a prime `p` and let `F = AlgebraicClosure (ZMod p)`.  A natural number `m` is
*introspective* for a polynomial `f ∈ 𝔽ₚ[X]` (relative to `r`) if `f(z)^m = f(z^m)` for every
`r`-th root of unity `z ∈ F`.  This is the key notion in the AKS correctness proof.
-/

open Polynomial

namespace CS
namespace AKS

/-- The algebraic closure of `𝔽ₚ`, the field in which the AKS argument takes place. -/
abbrev AC (p : ℕ) [Fact p.Prime] := AlgebraicClosure (ZMod p)

variable {p : ℕ} [Fact p.Prime]

/-- `m` is introspective for `f`: `f(z)^m = f(z^m)` for all `r`-th roots of unity `z`. -/
def Intro (p : ℕ) [Fact p.Prime] (r m : ℕ) (f : (ZMod p)[X]) : Prop :=
  ∀ z : AC p, z ^ r = 1 → (aeval z f) ^ m = aeval (z ^ m) f

lemma intro_one (r : ℕ) (f : (ZMod p)[X]) : Intro p r 1 f := by
  intro z _
  simp

lemma Intro.mul_poly {r m : ℕ} {f g : (ZMod p)[X]} (hf : Intro p r m f) (hg : Intro p r m g) :
    Intro p r m (f * g) := by
  intro z hz
  simp only [map_mul, mul_pow, hf z hz, hg z hz]

lemma Intro.mul_exp {r m₁ m₂ : ℕ} {f : (ZMod p)[X]} (h₁ : Intro p r m₁ f)
    (h₂ : Intro p r m₂ f) : Intro p r (m₁ * m₂) f := by
  intro z hz
  have hz' : (z ^ m₁) ^ r = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  calc (aeval z f) ^ (m₁ * m₂) = ((aeval z f) ^ m₁) ^ m₂ := by rw [pow_mul]
    _ = (aeval (z ^ m₁) f) ^ m₂ := by rw [h₁ z hz]
    _ = aeval ((z ^ m₁) ^ m₂) f := h₂ _ hz'
    _ = aeval (z ^ (m₁ * m₂)) f := by rw [pow_mul]

lemma Intro.pow {r m : ℕ} {f : (ZMod p)[X]} (h : Intro p r m f) (i : ℕ) :
    Intro p r (m ^ i) f := by
  induction i with
  | zero => simpa using intro_one r f
  | succ k ih => rw [pow_succ]; exact ih.mul_exp h

lemma intro_prod {r m : ℕ} {ι : Type*} (s : Finset ι) (g : ι → (ZMod p)[X])
    (h : ∀ i ∈ s, Intro p r m (g i)) : Intro p r m (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => intro z _; simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul_poly
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The characteristic `p` is introspective for every polynomial over `𝔽ₚ`. -/
lemma intro_char (r : ℕ) (f : (ZMod p)[X]) : Intro p r p f := by
  intro z _
  have key : ((frobenius (AC p) p).comp
        ((aeval z : (ZMod p)[X] →ₐ[ZMod p] AC p) : (ZMod p)[X] →+* AC p))
      = ((aeval (z ^ p) : (ZMod p)[X] →ₐ[ZMod p] AC p) : (ZMod p)[X] →+* AC p) := by
    apply Polynomial.ringHom_ext
    · intro a
      show frobenius (AC p) p (aeval z (C a)) = aeval (z ^ p) (C a)
      simp only [aeval_C, frobenius_def, ← map_pow, ZMod.pow_card]
    · show frobenius (AC p) p (aeval z X) = aeval (z ^ p) X
      simp [frobenius_def]
  have := RingHom.congr_fun key f
  simpa [frobenius_def] using this

end AKS
end CS

import RequestProject.AKS.Aux

/-!
# Correctness of the AKS criterion

The main result of this file is `CS.AKS.prime_of_conditions`: if `n ≥ 2` passes the AKS
conditions for a suitable parameter `r`, then `n` is prime.
-/

open Polynomial

set_option maxHeartbeats 2000000

namespace CS
namespace AKS

variable {p : ℕ} [Fact p.Prime]

/-- Every `n ^ i * p ^ j` is introspective for the products `∏_{a ∈ S} (X + a)`. -/
lemma intro_prod_family {n r L : ℕ} (hpn : p ∣ n)
    (hpoly : ∀ a ≤ L, PolyCond n r a) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 L) (i j : ℕ) :
    Intro p r (n ^ i * p ^ j) (∏ a ∈ S, (X + C (a : ZMod p))) := by
  refine intro_prod S _ (fun a ha => ?_)
  have haL : a ≤ L := by
    have := hS ha
    simp only [Finset.mem_Icc] at this
    omega
  exact ((intro_n_X_add_C hpn (hpoly a haL)).pow i).mul_exp ((intro_char r _).pow j)

/-- The key step of the AKS correctness proof: if `n` satisfies the AKS conditions for the
parameter `r` and `p` is a prime factor of `n`, then `n` is a power of `p`. -/
theorem exists_pow_of_conditions {n r : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hn : 2 ≤ n) (hr1 : 1 ≤ r) (hrn : r < n)
    (hcop : ∀ a, 1 ≤ a → a ≤ r → Nat.gcd a n = 1)
    (hord : 4 * blog n ^ 2 < orderOf (n : ZMod r))
    (hpoly : ∀ a ≤ 2 * blog n * Nat.sqrt (Nat.totient r), PolyCond n r a) :
    ∃ k, n = p ^ k := by
  classical
  by_contra hnp
  haveI : NeZero r := ⟨by omega⟩
  -- `p` is larger than `r`
  have hpr : r < p := by
    by_contra hle
    push_neg at hle
    have h1 : Nat.gcd p n = 1 := hcop p hp.one_lt.le hle
    rw [Nat.gcd_eq_left hpn] at h1
    exact hp.one_lt.ne' h1
  have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
  -- coprimality
  have hcopn : Nat.Coprime n r := Nat.coprime_comm.mp (hcop r hr1 le_rfl)
  have hpdvdr : ¬ (p ∣ r) := fun hd => absurd (Nat.le_of_dvd hr1 hd) (by omega)
  have hcoppr : Nat.Coprime p r := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpdvdr
  -- a primitive `r`-th root of unity in the algebraic closure of `𝔽ₚ`
  obtain ⟨ζ, hζ⟩ : ∃ z : AC p, IsPrimitiveRoot z r := exists_primitiveRoot_AC hpdvdr
  have hζr : ζ ^ r = 1 := hζ.pow_eq_one
  -- the group generated by `n` and `p` in `(ZMod r)ˣ`
  set b := blog n with hb
  have hb1 : 1 ≤ b := by simp [hb, blog]
  have hnlt : n < 2 ^ b := Nat.lt_pow_succ_log_self (by norm_num) n
  set un : (ZMod r)ˣ := ZMod.unitOfCoprime n hcopn with hun
  set up : (ZMod r)ˣ := ZMod.unitOfCoprime p hcoppr with hup
  set H : Subgroup (ZMod r)ˣ := Subgroup.closure {un, up} with hH
  set t := Nat.card H with ht
  have hunH : un ∈ H := Subgroup.subset_closure (by simp)
  have hupH : up ∈ H := Subgroup.subset_closure (by simp)
  have htpos : 0 < t := Nat.card_pos
  have htphi : t ≤ Nat.totient r := by
    have hdvd : Nat.card H ∣ Nat.card (ZMod r)ˣ := Subgroup.card_subgroup_dvd_card H
    have hcard : Nat.card (ZMod r)ˣ = Nat.totient r := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    rw [hcard] at hdvd
    exact Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) hdvd
  have hordle : orderOf ((n : ZMod r)) ≤ t := by
    have h1 : orderOf (⟨un, hunH⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard _
    have h2 : orderOf (⟨un, hunH⟩ : H) = orderOf un := (Subgroup.orderOf_coe _).symm
    have h3 : orderOf un = orderOf ((n : ZMod r)) := by
      rw [← ZMod.coe_unitOfCoprime n hcopn, ← hun, orderOf_units]
    rw [h2, h3] at h1
    exact Nat.le_of_dvd htpos h1
  have htK : 4 * b ^ 2 < t := lt_of_lt_of_le hord hordle
  set s := Nat.sqrt t with hs
  set L := 2 * b * s with hL
  have hsq : s * s ≤ t := Nat.sqrt_le t
  have h2bs : 2 * b ≤ s := Nat.le_sqrt.mpr (by nlinarith)
  have hs1 : 1 ≤ s := by omega
  have hLt : L < t := by
    rcases eq_or_lt_of_le h2bs with heq | hlt
    · rw [hL, ← heq]; nlinarith
    · rw [hL]; nlinarith
  have hLr : L ≤ r := by
    have h1 : L ≤ s * s := by rw [hL]; nlinarith
    have := Nat.totient_le r
    omega
  have hLp : L < p := by omega
  have hpolyL : ∀ a ≤ L, PolyCond n r a := by
    intro a ha
    refine hpoly a (le_trans ha ?_)
    have : s ≤ Nat.sqrt (Nat.totient r) := Nat.sqrt_le_sqrt htphi
    exact Nat.mul_le_mul_left _ this
  have hnbig : n ^ (2 * s) < 2 ^ L := by
    calc n ^ (2 * s) < (2 ^ b) ^ (2 * s) := by
          exact Nat.pow_lt_pow_left hnlt (by omega)
      _ = 2 ^ L := by rw [← pow_mul, hL]; ring_nf
  -- the family of polynomials and the set of its values at `ζ`
  set fam : Finset ℕ → (ZMod p)[X] := fun S => ∏ a ∈ S, (X + C (a : ZMod p)) with hfam
  set V : Finset (AC p) := (Finset.Icc 1 L).powerset.image (fun S => aeval ζ (fam S)) with hV
  -- the set of roots used for the injectivity argument
  set HF : Finset (ZMod r)ˣ := Finset.filter (fun u => u ∈ H) Finset.univ with hHF
  have hHFcard : HF.card = t := by
    rw [hHF, ht, Nat.card_eq_fintype_card, Fintype.card_subtype]
  set W : Finset (AC p) := HF.image (fun u : (ZMod r)ˣ => ζ ^ ((u : ZMod r)).val) with hW
  have hWcard : W.card = t := by
    rw [hW, Finset.card_image_of_injOn, hHFcard]
    intro u _ v _ huv
    have hlt1 : ((u : ZMod r)).val < r := ZMod.val_lt _
    have hlt2 : ((v : ZMod r)).val < r := ZMod.val_lt _
    have hvv := hζ.pow_inj hlt1 hlt2 huv
    have : ((u : ZMod r)) = ((v : ZMod r)) := ZMod.val_injective r hvv
    exact Units.ext this
  have hWmem : ∀ w ∈ W, ∃ i j : ℕ, w = ζ ^ (n ^ i * p ^ j) := by
    intro w hw
    rw [hW, Finset.mem_image] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rw [hHF, Finset.mem_filter] at hu
    obtain ⟨-, hu⟩ := hu
    obtain ⟨a, c, hac⟩ := Subgroup.mem_closure_pair.mp hu
    obtain ⟨i, hi⟩ := exists_nat_zpow un a
    obtain ⟨j, hj⟩ := exists_nat_zpow up c
    rw [hi, hj] at hac
    refine ⟨i, j, ?_⟩
    have hval : ((u : ZMod r)).val ≡ n ^ i * p ^ j [MOD r] := by
      have h1 : ((((u : ZMod r)).val : ℕ) : ZMod r) = ((n ^ i * p ^ j : ℕ) : ZMod r) := by
        rw [ZMod.natCast_zmod_val]
        rw [← hac]
        push_cast
        simp [hun, hup, ZMod.coe_unitOfCoprime]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
    exact pow_eq_pow_of_modEq hζr hval
  -- the main counting contradiction
  have key : ∀ i₁ j₁ i₂ j₂ : ℕ, i₁ ≤ s → j₁ ≤ s →
      n ^ i₂ * p ^ j₂ < n ^ i₁ * p ^ j₁ →
      (n ^ i₁ * p ^ j₁) ≡ (n ^ i₂ * p ^ j₂) [MOD r] → False := by
    intro i₁ j₁ i₂ j₂ hi₁ hj₁ hlt hcong
    have hVle : V.card ≤ n ^ i₁ * p ^ j₁ := by
      refine card_le_of_pow_eq V hlt ?_
      intro v hv
      rw [hV, Finset.mem_image] at hv
      obtain ⟨S, hS, rfl⟩ := hv
      rw [Finset.mem_powerset] at hS
      rw [intro_prod_family hpn hpolyL hS i₁ j₁ ζ hζr,
        intro_prod_family hpn hpolyL hS i₂ j₂ ζ hζr,
        pow_eq_pow_of_modEq hζr hcong]
    have hVcard : V.card = 2 ^ L := by
      rw [hV, Finset.card_image_of_injOn, Finset.card_powerset, Nat.card_Icc]
      · simp
      · intro S₁ h₁ S₂ h₂ hEq
        rw [Finset.coe_powerset] at h₁ h₂
        simp only [Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at h₁ h₂
        have hdeg : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 L → (fam S).natDegree ≤ L := by
          intro S hS
          refine le_trans (natDegree_prod_le _ _) ?_
          have hsum : ∑ a ∈ S, (X + C (a : ZMod p)).natDegree ≤ S.card := by
            have h1 : ∑ a ∈ S, (X + C (a : ZMod p)).natDegree ≤ ∑ _a ∈ S, (1 : ℕ) := by
              apply Finset.sum_le_sum
              intro a _
              exact le_of_eq (natDegree_X_add_C (a : ZMod p))
            simpa using h1
          have hcards : S.card ≤ L := by
            calc S.card ≤ (Finset.Icc 1 L).card := Finset.card_le_card hS
              _ = L := by simp
          omega
        have hroots : ∀ w ∈ W, aeval w (fam S₁) = aeval w (fam S₂) := by
          intro w hw
          obtain ⟨i, j, rfl⟩ := hWmem w hw
          have e1 := intro_prod_family hpn hpolyL h₁ i j ζ hζr
          have e2 := intro_prod_family hpn hpolyL h₂ i j ζ hζr
          have hEq' : aeval ζ (fam S₁) = aeval ζ (fam S₂) := hEq
          calc aeval (ζ ^ (n ^ i * p ^ j)) (fam S₁)
              = (aeval ζ (fam S₁)) ^ (n ^ i * p ^ j) := e1.symm
            _ = (aeval ζ (fam S₂)) ^ (n ^ i * p ^ j) := by rw [hEq']
            _ = aeval (ζ ^ (n ^ i * p ^ j)) (fam S₂) := e2
        have := poly_eq_of_many_roots (hdeg S₁ h₁) (hdeg S₂ h₂) W (by omega) hroots
        exact prod_X_add_C_inj hLp h₁ h₂ this
    have hle2 : n ^ i₁ * p ^ j₁ ≤ n ^ (2 * s) := by
      calc n ^ i₁ * p ^ j₁ ≤ n ^ s * n ^ s := by
            exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hi₁)
              (le_trans (Nat.pow_le_pow_left hpn' _) (Nat.pow_le_pow_right (by omega) hj₁))
        _ = n ^ (2 * s) := by rw [← pow_add]; ring_nf
    omega
  -- pigeonhole
  have hmaps : Set.MapsTo (fun q : ℕ × ℕ => un ^ q.1 * up ^ q.2)
      ((Finset.range (s + 1) ×ˢ Finset.range (s + 1) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ))
      (HF : Set (ZMod r)ˣ) := by
    intro q _
    simp only [hHF, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    exact H.mul_mem (H.pow_mem hunH _) (H.pow_mem hupH _)
  have hcardlt : HF.card <
      (Finset.range (s + 1) ×ˢ Finset.range (s + 1) : Finset (ℕ × ℕ)).card := by
    rw [hHFcard, Finset.card_product, Finset.card_range]
    have h2 : t < (s + 1) ^ 2 := Nat.lt_succ_sqrt' t
    nlinarith
  obtain ⟨q1, hq1, q2, hq2, hqne, hqeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardlt hmaps
  simp only [Finset.mem_product, Finset.mem_range] at hq1 hq2
  -- the two exponents are distinct natural numbers, congruent mod `r`
  have hcong : (n ^ q1.1 * p ^ q1.2) ≡ (n ^ q2.1 * p ^ q2.2) [MOD r] := by
    have h1 : ((n ^ q1.1 * p ^ q1.2 : ℕ) : ZMod r) = ((n ^ q2.1 * p ^ q2.2 : ℕ) : ZMod r) := by
      have := congrArg (fun u : (ZMod r)ˣ => (u : ZMod r)) hqeq
      push_cast at this ⊢
      simpa [hun, hup, ZMod.coe_unitOfCoprime] using this
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
  have hne : n ^ q1.1 * p ^ q1.2 ≠ n ^ q2.1 * p ^ q2.2 := by
    intro heqm
    have hnpow : ∀ i₁ j₁ i₂ j₂ : ℕ, i₁ < i₂ → n ^ i₁ * p ^ j₁ = n ^ i₂ * p ^ j₂ → False := by
      intro i₁ j₁ i₂ j₂ hii heq
      have hn0 : 0 < n ^ i₁ := pow_pos (by omega) _
      have hsplit : n ^ i₂ = n ^ i₁ * n ^ (i₂ - i₁) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit, mul_assoc] at heq
      have hcancel : p ^ j₁ = n ^ (i₂ - i₁) * p ^ j₂ := by
        exact Nat.eq_of_mul_eq_mul_left hn0 heq
      have hdvd : n ∣ p ^ j₁ := by
        rw [hcancel]
        refine dvd_mul_of_dvd_left ?_ _
        exact dvd_pow_self n (by omega)
      obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      exact hnp ⟨k, hk⟩
    rcases lt_trichotomy q1.1 q2.1 with h | h | h
    · exact hnpow _ _ _ _ h heqm
    · have hn0 : 0 < n ^ q1.1 := pow_pos (by omega) _
      have heqm' : n ^ q1.1 * p ^ q1.2 = n ^ q1.1 * p ^ q2.2 := by rw [heqm, h]
      have hpp2 : p ^ q1.2 = p ^ q2.2 := Nat.eq_of_mul_eq_mul_left hn0 heqm'
      have := Nat.pow_right_injective hp.two_le hpp2
      exact hqne (Prod.ext h this)
    · exact hnpow _ _ _ _ h heqm.symm
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key q2.1 q2.2 q1.1 q1.2 (by omega) (by omega) hlt hcong.symm
  · exact key q1.1 q1.2 q2.1 q2.2 (by omega) (by omega) hlt hcong

/-- **Correctness of the AKS criterion.**  If `n ≥ 2` is not a perfect power, has no factor
`≤ r`, satisfies `r < n`, the order of `n` mod `r` exceeds `4 (log₂ n + 1)^2`, and all the AKS
polynomial congruences hold, then `n` is prime. -/
theorem prime_of_conditions {n r : ℕ} (hn : 2 ≤ n) (hr1 : 1 ≤ r) (hrn : r < n)
    (hcop : ∀ a, 1 ≤ a → a ≤ r → Nat.gcd a n = 1)
    (hord : 4 * blog n ^ 2 < orderOf (n : ZMod r))
    (hpp : ¬ IsPerfectPower n)
    (hpoly : ∀ a ≤ 2 * blog n * Nat.sqrt (Nat.totient r), PolyCond n r a) :
    n.Prime := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := exists_pow_of_conditions hp hpn hn hr1 hrn hcop hord hpoly
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · simp at hk; omega
    · rw [pow_one] at hk; rwa [← hk] at hp
  · exact absurd ⟨p, k, hk2, hk.symm⟩ hpp

end AKS
end CS

import RequestProject.AKS.Intro

/-!
# Auxiliary algebraic lemmas for the AKS correctness proof
-/

open Polynomial

namespace CS
namespace AKS

variable {p : ℕ} [Fact p.Prime]

/-- If `p ∤ r` then the algebraic closure of `𝔽ₚ` contains a primitive `r`-th root of unity. -/
lemma exists_primitiveRoot_AC {r : ℕ} (hr : ¬ (p ∣ r)) : ∃ z : AC p, IsPrimitiveRoot z r := by
  haveI : NeZero (r : AC p) := by
    constructor
    intro h
    exact hr ((CharP.cast_eq_zero_iff (AC p) p r).mp h)
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ r

/-- Powers of an `r`-th root of unity only depend on the exponent modulo `r`. -/
lemma pow_eq_pow_of_modEq {M : Type*} [CommMonoid M] {r : ℕ} {z : M} (h1 : z ^ r = 1) {i j : ℕ}
    (hij : i ≡ j [MOD r]) : z ^ i = z ^ j := by
  have h2 : z ^ (i % r) = z ^ (j % r) := by rw [hij]
  calc z ^ i = z ^ (r * (i / r) + i % r) := by rw [Nat.div_add_mod]
    _ = (z ^ r) ^ (i / r) * z ^ (i % r) := by rw [pow_add, pow_mul]
    _ = z ^ (i % r) := by rw [h1, one_pow, one_mul]
    _ = z ^ (j % r) := h2
    _ = (z ^ r) ^ (j / r) * z ^ (j % r) := by rw [h1, one_pow, one_mul]
    _ = z ^ (r * (j / r) + j % r) := by rw [pow_add, pow_mul]
    _ = z ^ j := by rw [Nat.div_add_mod]

/-- In a finite group every integer power is a natural power. -/
lemma exists_nat_zpow {G : Type*} [Group G] [Finite G] (g : G) (z : ℤ) :
    ∃ k : ℕ, g ^ z = g ^ k := by
  have hd : 0 < orderOf g := orderOf_pos g
  set d := orderOf g with hdd
  set N : ℕ := z.natAbs with hN
  have hN1 : (N : ℤ) ≤ (d : ℤ) * N := le_mul_of_one_le_left (by positivity) (by exact_mod_cast hd)
  have hN2 : -z ≤ (N : ℤ) := by omega
  have hnn : 0 ≤ z + d * N := by linarith
  refine ⟨(z + d * N).toNat, ?_⟩
  have hz : ((z + d * N).toNat : ℤ) = z + d * N := Int.toNat_of_nonneg hnn
  rw [← zpow_natCast g ((z + d * N).toNat), hz, zpow_add g z ((d : ℤ) * N), zpow_mul,
    zpow_natCast g d, hdd, pow_orderOf_eq_one, one_zpow, mul_one]

/-- A finite set of field elements all satisfying `v ^ m₁ = v ^ m₂` with `m₂ < m₁` has at most
`m₁` elements: they are all roots of the nonzero polynomial `X ^ m₁ - X ^ m₂`. -/
lemma card_le_of_pow_eq {F : Type*} [Field F] (V : Finset F) {m₁ m₂ : ℕ} (h : m₂ < m₁)
    (hV : ∀ v ∈ V, v ^ m₁ = v ^ m₂) : V.card ≤ m₁ := by
  classical
  set Q : F[X] := X ^ m₁ - X ^ m₂ with hQ
  have hcoeff : Q.coeff m₁ = 1 := by
    simp [hQ, coeff_X_pow, h.ne']
  have hQ0 : Q ≠ 0 := by
    intro hz
    rw [hz] at hcoeff
    simp at hcoeff
  have hdeg : Q.natDegree ≤ m₁ := by
    rw [hQ]
    refine le_trans (natDegree_sub_le _ _) ?_
    simp only [natDegree_X_pow]
    omega
  have hsub : V.val ⊆ Q.roots := by
    intro v hv
    have hv' : v ∈ V := Finset.mem_val.mp hv
    rw [mem_roots hQ0]
    simp only [IsRoot.def, hQ, eval_sub, eval_pow, eval_X]
    rw [hV v hv', sub_self]
  exact le_trans (card_le_degree_of_subset_roots hsub) hdeg

/-- Two polynomials of degree at most `L` over `𝔽ₚ` agreeing at more than `L` points of the
algebraic closure are equal. -/
lemma poly_eq_of_many_roots {f g : (ZMod p)[X]} {L : ℕ} (hf : f.natDegree ≤ L)
    (hg : g.natDegree ≤ L) (W : Finset (AC p)) (hW : L < W.card)
    (h : ∀ w ∈ W, aeval w f = aeval w g) : f = g := by
  classical
  by_contra hne
  have hfg : f - g ≠ 0 := sub_ne_zero.mpr hne
  set D : (AC p)[X] := (f - g).map (algebraMap (ZMod p) (AC p)) with hD
  have hD0 : D ≠ 0 := by
    rw [hD, Polynomial.map_ne_zero_iff (algebraMap (ZMod p) (AC p)).injective]
    exact hfg
  have hDdeg : D.natDegree ≤ L := by
    rw [hD, natDegree_map_eq_of_injective (algebraMap (ZMod p) (AC p)).injective]
    exact le_trans (natDegree_sub_le f g) (max_le hf hg)
  have hsub : W.val ⊆ D.roots := by
    intro w hw
    have hw' : w ∈ W := Finset.mem_val.mp hw
    rw [mem_roots hD0]
    have : aeval w (f - g) = 0 := by
      rw [map_sub, h w hw', sub_self]
    simpa [hD, IsRoot.def, eval_map, ← aeval_def] using this
  have := card_le_degree_of_subset_roots hsub
  omega

/-- The products `∏_{a ∈ S} (X + a)` over subsets `S` of `[1, L]` are pairwise distinct,
provided `L < p`. -/
lemma prod_X_add_C_inj {L : ℕ} (hLp : L < p) {S T : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 L) (hT : T ⊆ Finset.Icc 1 L)
    (h : (∏ a ∈ S, (X + C (a : ZMod p))) = ∏ a ∈ T, (X + C (a : ZMod p))) : S = T := by
  classical
  have hcast : ∀ x ∈ Finset.Icc 1 L, ∀ y ∈ Finset.Icc 1 L,
      (x : ZMod p) = (y : ZMod p) → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_Icc] at hx hy
    have := (ZMod.natCast_eq_natCast_iff x y p).mp hxy
    have hx' : x < p := by omega
    have hy' : y < p := by omega
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hy'] at this
  have key : ∀ (U : Finset ℕ), U ⊆ Finset.Icc 1 L → ∀ a ∈ Finset.Icc 1 L,
      ((∏ b ∈ U, (X + C (b : ZMod p))).eval (-(a : ZMod p)) = 0 ↔ a ∈ U) := by
    intro U hU a ha
    rw [eval_prod]
    rw [Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨b, hb, hb0⟩
      simp only [eval_add, eval_X, eval_C] at hb0
      have : (b : ZMod p) = (a : ZMod p) := by linear_combination hb0
      rwa [hcast b (hU hb) a ha this] at hb
    · intro haU
      exact ⟨a, haU, by simp⟩
  ext a
  by_cases ha : a ∈ Finset.Icc 1 L
  · rw [← key S hS a ha, ← key T hT a ha, h]
  · constructor
    · intro haS; exact absurd (hS haS) ha
    · intro haT; exact absurd (hT haT) ha

/-- The AKS polynomial congruence modulo `n` gives introspectiveness of `n`
for `X + a` over any prime factor `p` of `n`. -/
lemma intro_n_X_add_C {n r a : ℕ} (hpn : p ∣ n) (h : PolyCond n r a) :
    Intro p r n (X + C (a : ZMod p)) := by
  classical
  haveI : CharP (ZMod p) p := ZMod.charP p
  rw [PolyCond] at h
  set φ : ZMod n →+* ZMod p := ZMod.castHom hpn (ZMod p) with hφ
  have hmap : ((X : (ZMod p)[X]) ^ r - 1) ∣
      ((X + C (a : ZMod p)) ^ n - (X ^ n + C (a : ZMod p))) := by
    have := Polynomial.map_dvd φ h
    simpa [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X, Polynomial.map_C, hφ, map_natCast] using this
  intro z hz
  obtain ⟨c, hc⟩ := hmap
  have : (z + (a : AC p)) ^ n - (z ^ n + (a : AC p)) = 0 := by
    have := congrArg (fun q => Polynomial.aeval z q) hc
    simp only [map_sub, map_add, map_pow, aeval_X, aeval_C, map_one, map_mul] at this
    rw [hz] at this
    simpa using this
  have h2 : (z + (a : AC p)) ^ n = z ^ n + (a : AC p) := by linear_combination this
  simpa using h2

end AKS
end CS

import Mathlib

/-!
# The AKS primality test: definitions

This file sets up the AKS ("PRIMES is in P") algorithm of Agrawal, Kayal and Saxena
as a predicate on natural numbers, together with its parameters.
-/

open Polynomial

namespace CS
namespace AKS

/-- `blog n = ⌊log₂ n⌋ + 1`, the bit length of `n`; an integer upper bound for `log₂ n`. -/
def blog (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- `n` is a perfect power, i.e. `n = a ^ b` with `b > 1`. -/
def IsPerfectPower (n : ℕ) : Prop := ∃ a b : ℕ, 1 < b ∧ a ^ b = n

/-- `r` is a *good* AKS parameter for `n`: no `n ^ k - 1` with `1 ≤ k ≤ 4 (log₂ n + 1)^2`
is divisible by `r`.  Equivalently (when `r` is coprime to `n`) the multiplicative order of
`n` modulo `r` exceeds `4 (log₂ n + 1)^2`. -/
def GoodR (n r : ℕ) : Prop := ∀ k, 1 ≤ k → k ≤ 4 * blog n ^ 2 → ¬ (r ∣ n ^ k - 1)

/-- The AKS parameter `r`: the least positive `r` which is good for `n`. -/
noncomputable def rAKS (n : ℕ) : ℕ := sInf {r | 1 ≤ r ∧ GoodR n r}

/-- The number of values `a` tested in the main loop of the algorithm. -/
noncomputable def ell (n : ℕ) : ℕ := 2 * blog n * Nat.sqrt (Nat.totient (rAKS n))

/-- The AKS polynomial congruence `(X + a)^n ≡ X^n + a  (mod X^r - 1, n)`. -/
def PolyCond (n r a : ℕ) : Prop :=
  (X ^ r - 1 : (ZMod n)[X]) ∣ ((X + C (a : ZMod n)) ^ n - (X ^ n + C (a : ZMod n)))

/-- The AKS test.  For `n` no larger than the (poly-logarithmically bounded) parameter
`rAKS n` the test is plain trial division; otherwise it consists of the perfect-power test,
the gcd test for `a ≤ rAKS n`, and the `ell n + 1` polynomial congruences. -/
noncomputable def Test (n : ℕ) : Prop :=
  if n ≤ rAKS n then (∀ a, 2 ≤ a → a < n → ¬ a ∣ n)
  else ¬ IsPerfectPower n ∧ (∀ a, 1 ≤ a → a ≤ rAKS n → Nat.gcd a n = 1) ∧
        (∀ a ≤ ell n, PolyCond n (rAKS n) a)

end AKS
end CS

