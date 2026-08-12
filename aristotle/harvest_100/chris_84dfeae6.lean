/-
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.AKS.Algorithm
import RequestProject.AKS.Cost

/-!
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000

namespace CS

/-- **PRIMES is in P** (Agrawal–Kayal–Saxena).

`AKS.aksBool : ℕ → Bool` is an explicit, fully computable implementation of the AKS primality
test.  On input `n` it checks that `n ≥ 2`, that `n` is not a perfect power, that no `a ≤ r`
shares a nontrivial factor with `n`, and — unless `n ≤ r` — that the congruences
`(X + a)^n = X^n + a` hold in `(ZMod n)[X]/(X^r - 1)` for all `1 ≤ a ≤ ℓ`, where `r = AKS.rAlg n`
is the least modulus for which the multiplicative order of `n` exceeds `(bit length)^4` and
`ℓ = AKS.ellAlg n`.  The congruences are evaluated by repeated squaring in a computable
coefficient-vector model of the quotient ring.

`AKS.aksI : ℕ → Bool × ℕ` is the same algorithm instrumented with a counter: it is a structural
copy of every function involved, threading a count of the primitive operations performed
(see `RequestProject/AKS/Cost.lean` for the cost assigned to each leaf primitive: `r * r`
coefficient multiplications for one cyclic convolution, `bits n` for one `Nat.gcd`, and so on).
Costs are therefore measured in arithmetic operations on numbers of `O(log n)` bits, not in
bit operations.

The statement below records:

* **the instrumented algorithm computes the same answer** as the plain one;
* **correctness**: `AKS.aksBool` decides primality exactly;
* **polynomial running time**: on every input `n ≥ 2` the algorithm performs at most
  `(bit length of n) ^ 45` primitive operations;
* **polynomial size of the parameters**: `r ≤ 2 · (bit length)^12` and `ℓ ≤ 4 · (bit length)^7 + 2`.
-/
theorem aks_primes_in_p :
    (∀ n : ℕ, (AKS.aksI n).1 = AKS.aksBool n) ∧
    (∀ n : ℕ, AKS.aksBool n = true ↔ Nat.Prime n) ∧
    (∀ n : ℕ, 2 ≤ n → (AKS.aksI n).2 ≤ AKS.bits n ^ 45) ∧
    (∀ n : ℕ, 2 ≤ n → AKS.rAlg n ≤ 2 * AKS.bits n ^ 12) ∧
    (∀ n : ℕ, 2 ≤ n → AKS.ellAlg n ≤ 4 * AKS.bits n ^ 7 + 2) := by
  refine ⟨AKS.aksI_fst, AKS.aksBool_iff_prime, fun n hn => AKS.aksI_snd_le hn, ?_,
    fun n hn => AKS.ellAlg_le hn⟩
  intro n hn
  rw [AKS.rAlg_eq hn]
  exact AKS.rOf_le n hn

end CS

/-
A computable model of the ring `(ZMod n)[X] / (X^r - 1)`: coefficient vectors indexed by
`ZMod r`, with cyclic convolution as multiplication.
-/
import Mathlib

open Polynomial

namespace AKS

/-- Coefficient vectors: `f : ZMod r → ZMod n` represents `∑ i, f i * X ^ i.val`. -/
abbrev Vec (n r : ℕ) := ZMod r → ZMod n

variable {n r : ℕ}

/-- The polynomial represented by a coefficient vector. -/
noncomputable def toPoly [NeZero r] (f : Vec n r) : (ZMod n)[X] :=
  ∑ i : ZMod r, C (f i) * X ^ (ZMod.val i)

/-- The quotient ring `(ZMod n)[X] / (X ^ r - 1)`. -/
abbrev QuotRing (n r : ℕ) := (ZMod n)[X] ⧸ Ideal.span {(X ^ r - 1 : (ZMod n)[X])}

/-- The canonical map to the quotient ring. -/
noncomputable def mkQ (n r : ℕ) : (ZMod n)[X] →+* QuotRing n r :=
  Ideal.Quotient.mk _

theorem mkQ_eq_iff (u v : (ZMod n)[X]) :
    mkQ n r u = mkQ n r v ↔ (X ^ r - 1 : (ZMod n)[X]) ∣ u - v := by
  rw [mkQ, Ideal.Quotient.eq, Ideal.mem_span_singleton]

theorem mkQ_X_pow_r : mkQ n r (X ^ r) = 1 := by
  have h : (X ^ r - 1 : (ZMod n)[X]) ∣ X ^ r - 1 := dvd_rfl
  have := (mkQ_eq_iff (n := n) (r := r) (X ^ r) 1).mpr h
  simpa using this

theorem mkQ_X_pow_mod (u : ℕ) : mkQ n r (X ^ u) = mkQ n r (X ^ (u % r)) := by
  conv_lhs => rw [← Nat.div_add_mod u r]
  rw [pow_add, pow_mul, map_mul, map_pow, mkQ_X_pow_r, one_pow, one_mul]

theorem mkQ_X_pow_congr {u v : ℕ} (h : u % r = v % r) :
    mkQ n r (X ^ u) = mkQ n r (X ^ v) := by
  rw [mkQ_X_pow_mod u, mkQ_X_pow_mod v, h]

/-- The vector for the monomial `X ^ e`. -/
def cmonomial [NeZero r] (n : ℕ) (e : ℕ) : Vec n r := fun kk => if kk = (e : ZMod r) then 1 else 0

/-- The vector for the constant `a`. -/
def cconst [NeZero r] (n : ℕ) (a : ZMod n) : Vec n r := fun kk => if kk = 0 then a else 0

/-- Pointwise addition of vectors. -/
def cadd (f g : Vec n r) : Vec n r := fun kk => f kk + g kk

/-- Cyclic convolution of vectors. -/
def cmul [NeZero r] (f g : Vec n r) : Vec n r := fun kk => ∑ i : ZMod r, f i * g (kk - i)

/-- The unit vector. -/
def cone [NeZero r] (n : ℕ) : Vec n r := cmonomial n 0

/-- Fast exponentiation of vectors. -/
def cpow [NeZero r] (f : Vec n r) (m : ℕ) : Vec n r :=
  if m = 0 then cone n
  else
    let t := cpow f (m / 2)
    let t2 := cmul t t
    if m % 2 = 1 then cmul t2 f else t2
  termination_by m
  decreasing_by omega

/-- The element of the quotient ring represented by a coefficient vector. -/
noncomputable def toQ [NeZero r] (f : Vec n r) : QuotRing n r := mkQ n r (toPoly f)

section Lemmas

variable [NeZero r]

theorem toPoly_cmonomial (e : ℕ) :
    toPoly (cmonomial (r := r) n e) = X ^ (ZMod.val ((e : ℕ) : ZMod r)) := by
  classical
  simp only [toPoly, cmonomial]
  rw [Finset.sum_eq_single ((e : ℕ) : ZMod r)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem toQ_cmonomial (e : ℕ) : toQ (cmonomial (r := r) n e) = mkQ n r (X ^ e) := by
  rw [toQ, toPoly_cmonomial, ZMod.val_natCast, ← mkQ_X_pow_mod]

theorem toPoly_cconst (a : ZMod n) : toPoly (cconst (r := r) n a) = C a := by
  classical
  simp only [toPoly, cconst]
  rw [Finset.sum_eq_single (0 : ZMod r)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem toPoly_cadd (f g : Vec n r) : toPoly (cadd f g) = toPoly f + toPoly g := by
  rw [toPoly, toPoly, toPoly, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [cadd, C_add, add_mul]

theorem toQ_cadd (f g : Vec n r) : toQ (cadd f g) = toQ f + toQ g := by
  rw [toQ, toQ, toQ, toPoly_cadd, map_add]

theorem toQ_cmul (f g : Vec n r) : toQ (cmul f g) = toQ f * toQ g := by
  classical
  have hprod : toPoly f * toPoly g
      = ∑ i : ZMod r, ∑ j : ZMod r, C (f i * g j) * X ^ (ZMod.val i + ZMod.val j) := by
    rw [toPoly, toPoly, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [C_mul, pow_add]
    ring
  have hlhs : toQ (cmul f g)
      = ∑ kk : ZMod r, ∑ i : ZMod r, mkQ n r (C (f i * g (kk - i)) * X ^ (ZMod.val kk)) := by
    simp only [toQ, toPoly, cmul]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun kk _ => ?_)
    rw [← map_sum, ← Finset.sum_mul, ← map_sum]
  have hrhs : toQ f * toQ g
      = ∑ i : ZMod r, ∑ j : ZMod r, mkQ n r (C (f i * g j) * X ^ (ZMod.val (i + j))) := by
    rw [toQ, toQ, ← map_mul, hprod, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [map_mul]
    congr 1
    refine mkQ_X_pow_congr ?_
    rw [ZMod.val_add, Nat.mod_mod]
  rw [hlhs, hrhs, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Fintype.sum_equiv (Equiv.subRight i) _ _ (fun kk => ?_)
  simp only [Equiv.subRight_apply]
  have hkk : i + (kk - i) = kk := by ring
  rw [hkk]

theorem toQ_cone : toQ (cone (r := r) n) = 1 := by
  rw [cone, toQ_cmonomial]
  simp

theorem toQ_cpow (f : Vec n r) (m : ℕ) : toQ (cpow f m) = (toQ f) ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [cpow]
    by_cases hm : m = 0
    · simp [hm, toQ_cone]
    · simp only [hm, if_false]
      have hhalf : toQ (cpow f (m / 2)) = (toQ f) ^ (m / 2) := ih (m / 2) (by omega)
      by_cases hpar : m % 2 = 1
      · simp only [hpar, if_true]
        rw [toQ_cmul, toQ_cmul, hhalf, ← pow_add, ← pow_succ]
        congr 1
        omega
      · simp only [hpar, if_false]
        rw [toQ_cmul, hhalf, ← pow_add]
        congr 1
        omega

/-- Coefficient extraction. -/
theorem coeff_toPoly (f : Vec n r) (i : ZMod r) :
    (toPoly f).coeff (ZMod.val i) = f i := by
  classical
  rw [toPoly, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro hcon
    exact hb (ZMod.val_injective r hcon.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem degree_toPoly_lt (f : Vec n r) : (toPoly f).degree < (r : ℕ) := by
  rw [toPoly]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (by exact WithBot.bot_lt_coe r)).mpr ?_
  intro i _
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast ZMod.val_lt i

/-- A polynomial of degree `< r` divisible by `X ^ r - 1` vanishes. -/
theorem eq_zero_of_dvd_of_degree_lt [Fact (1 < n)] {P : (ZMod n)[X]}
    (hdvd : (X ^ r - 1 : (ZMod n)[X]) ∣ P)
    (hdeg : P.degree < (r : ℕ)) : P = 0 := by
  obtain ⟨c, hc⟩ := hdvd
  have hmonic : (X ^ r - 1 : (ZMod n)[X]).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : ZMod n) (NeZero.ne r)
  by_cases hc0 : c = 0
  · rw [hc, hc0, mul_zero]
  · exfalso
    have hdeg1 : (X ^ r - 1 : (ZMod n)[X]).degree = (r : ℕ) := by
      simpa using Polynomial.degree_X_pow_sub_C (n := r) (Nat.pos_of_ne_zero (NeZero.ne r))
        (1 : ZMod n)
    have hlead : ((X ^ r - 1 : (ZMod n)[X]).leadingCoeff) * c.leadingCoeff ≠ 0 := by
      rw [hmonic.leadingCoeff, one_mul]
      exact Polynomial.leadingCoeff_ne_zero.mpr hc0
    have hdegmul : ((X ^ r - 1 : (ZMod n)[X]) * c).degree
        = (X ^ r - 1 : (ZMod n)[X]).degree + c.degree := Polynomial.degree_mul' hlead
    rw [hc, hdegmul, hdeg1, Polynomial.degree_eq_natDegree hc0, ← Nat.cast_add] at hdeg
    have : r + c.natDegree < r := by exact_mod_cast hdeg
    omega

theorem toQ_injective [Fact (1 < n)] : Function.Injective (toQ (n := n) (r := r)) := by
  intro f g hfg
  have hdvd : (X ^ r - 1 : (ZMod n)[X]) ∣ toPoly f - toPoly g :=
    (mkQ_eq_iff _ _).mp hfg
  have hdeg : (toPoly f - toPoly g).degree < (r : ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt (degree_toPoly_lt f) (degree_toPoly_lt g))
  have hzero : toPoly f - toPoly g = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  funext i
  have := congrArg (fun P => Polynomial.coeff P (ZMod.val i)) hzero
  simp only [Polynomial.coeff_sub, Polynomial.coeff_zero, coeff_toPoly] at this
  linear_combination this

end Lemmas

end AKS

/-
Elementary numerical estimates used in the AKS proof.
-/
import Mathlib

namespace AKS

theorem sq_le_sqrt {k t : ℕ} (h : k ^ 4 < t) : k ^ 2 ≤ Nat.sqrt t := by
  have h1 : Nat.sqrt ((k ^ 2) ^ 2) ≤ Nat.sqrt t := Nat.sqrt_le_sqrt (by nlinarith)
  rwa [Nat.sqrt_eq'] at h1

theorem mul_bound {k rho : ℕ} (hk : 3 ≤ k) (h : k ^ 2 ≤ rho) : 2 * rho * k + 3 ≤ rho * rho := by
  nlinarith [sq_nonneg k, sq_nonneg rho]

/-- With `t > k^4` and `k ≥ 3` we have `2 √t k + 2 < t`. -/
theorem arith_deg {k t : ℕ} (hk : 3 ≤ k) (ht : k ^ 4 < t) :
    2 * Nat.sqrt t * k + 2 < t := by
  have h1 : k ^ 2 ≤ Nat.sqrt t := sq_le_sqrt ht
  have h2 := mul_bound hk h1
  have h3 : Nat.sqrt t ^ 2 ≤ t := Nat.sqrt_le' t
  nlinarith

/-- With `t > k^4`, `t ≤ φ(rr) < rr` and `k ≥ 3` we have `2 √(φ rr) k + 2 < rr`. -/
theorem arith_ell {k t rr : ℕ} (hk : 3 ≤ k) (ht : k ^ 4 < t)
    (htr : t ≤ Nat.totient rr) (hlt : Nat.totient rr < rr) :
    2 * Nat.sqrt (Nat.totient rr) * k + 2 < rr := by
  have h1 : k ^ 2 ≤ Nat.sqrt (Nat.totient rr) := sq_le_sqrt (lt_of_lt_of_le ht htr)
  have h2 := mul_bound hk h1
  have h3 : Nat.sqrt (Nat.totient rr) ^ 2 ≤ Nat.totient rr := Nat.sqrt_le' _
  nlinarith

end AKS

/-
The hard direction of the AKS criterion: an accepted number is prime.
-/
import RequestProject.AKS.Counting
import RequestProject.AKS.Arith
import RequestProject.AKS.Sound

open Polynomial

namespace AKS

/-- If `p ^ i * n ^ j = p ^ i' * n ^ j'` with `j' < j` then `n` is a power of `p`. -/
theorem pow_of_lt {p n i j i' j' : ℕ} (hp : p.Prime) (hn : 2 ≤ n) (hjj : j' < j)
    (heq : p ^ i * n ^ j = p ^ i' * n ^ j') : ∃ e, n = p ^ e := by
  have h1 : n ^ j = n ^ j' * n ^ (j - j') := by
    rw [← pow_add, Nat.add_sub_cancel' hjj.le]
  rw [h1] at heq
  have hpos : 0 < n ^ j' := Nat.pow_pos (by omega)
  have h2 : p ^ i * n ^ (j - j') = p ^ i' := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc n ^ j' * (p ^ i * n ^ (j - j')) = p ^ i * (n ^ j' * n ^ (j - j')) := by ring
      _ = p ^ i' * n ^ j' := heq
      _ = n ^ j' * p ^ i' := by ring
  have hne0 : j - j' ≠ 0 := by omega
  have h3 : n ∣ p ^ i' := by
    rw [← h2]
    exact Dvd.dvd.mul_left (dvd_pow_self n hne0) _
  obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow hp).mp h3
  exact ⟨e, he⟩

/-- If two distinct pairs of exponents give the same number, `n` is a power of `p`. -/
theorem pow_of_ne {p n i j i' j' : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    (hne : (i, j) ≠ (i', j')) (heq : p ^ i * n ^ j = p ^ i' * n ^ j') : ∃ e, n = p ^ e := by
  rcases lt_trichotomy j j' with hj | hj | hj
  · exact pow_of_lt hp hn hj heq.symm
  · subst hj
    have hpos : 0 < n ^ j := Nat.pow_pos (by omega)
    have : p ^ i = p ^ i' := Nat.eq_of_mul_eq_mul_right hpos heq
    have : i = i' := Nat.pow_right_injective hp.two_le this
    exact absurd (by simp [this]) hne
  · exact pow_of_lt hp hn hj heq

/-- The polynomial condition modulo `n` implies introspectivity of `n` modulo a prime
divisor `p` of `n`. -/
theorem intro_n_of_poly {n p r a : ℕ} (hpn : p ∣ n)
    (h : (X ^ r - 1 : (ZMod n)[X]) ∣ (X + C (a : ZMod n)) ^ n - (X ^ n + C (a : ZMod n))) :
    Intro p r n (X + C (a : ZMod p)) := by
  have hmap := _root_.map_dvd (Polynomial.mapRingHom (ZMod.castHom hpn (ZMod p))) h
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_one,
    map_natCast] at hmap
  unfold Intro
  have hexp : expand (ZMod p) n (X + C (a : ZMod p)) = X ^ n + C (a : ZMod p) := by
    simp [Polynomial.expand_X]
  rw [hexp]
  simp only [Polynomial.map_natCast] at hmap
  simpa using hmap

/-- `p` is introspective for `X + a` over `ZMod p`. -/
theorem intro_p_self {p r a : ℕ} (hp : p.Prime) :
    Intro p r p (X + C (a : ZMod p)) := by
  unfold Intro
  have hexp : expand (ZMod p) p (X + C (a : ZMod p)) = X ^ p + C (a : ZMod p) := by
    simp [Polynomial.expand_X]
  rw [hexp, add_pow_prime_eq p hp, sub_self]
  exact dvd_zero _

theorem two_le_bits {n : ℕ} (hn : 2 ≤ n) : 2 ≤ bits n := by
  rw [bits]
  by_contra hcon
  push_neg at hcon
  have h1 : Nat.size n ≤ 1 := by omega
  rw [Nat.size_le] at h1
  omega

theorem lt_two_pow_bits (n : ℕ) : n < 2 ^ bits n := Nat.lt_size_self n

theorem prime_of_accepts {n : ℕ} (hacc : AKSAccepts n) : n.Prime := by
  classical
  obtain ⟨hn2, hpp, hgcd, hcase⟩ := hacc
  set r := rOf n with hrdef
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hpn' : p ≤ n := Nat.minFac_le (by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  have hgcdp : p ≤ r → n = p := by
    intro hle
    have h := hgcd p hp.one_lt.le hle
    rw [Nat.gcd_eq_left hpn] at h
    rcases h with h1 | h1
    · exact absurd h1 hp.ne_one
    · exact h1.symm
  by_cases hnr : n ≤ r
  · have hnp : n = p := hgcdp (le_trans hpn' hnr)
    rw [hnp]; exact hp
  have hrn : r < n := by omega
  -- The main case: `r < n`.
  have hpoly := hcase.resolve_left (not_le.mpr hrn)
  have hpr : r < p := by
    by_contra hcon
    push_neg at hcon
    have := hgcdp hcon
    omega
  have hord : thr n < orderOf ((n : ZMod r)) := thr_lt_orderOf n hn2
  set k := bits n with hkdef
  have hk2 : 2 ≤ k := two_le_bits hn2
  have hnk : n < 2 ^ k := lt_two_pow_bits n
  have hthr : thr n = k ^ 4 := rfl
  -- `r ≥ 2`
  have hr2 : 2 ≤ r := by
    rcases Nat.lt_or_ge r 2 with hlt | hge
    · exfalso
      interval_cases r
      · have hk4pos : 0 < k ^ 4 := by positivity
        have hfin : IsOfFinOrder ((n : ZMod 0)) := orderOf_pos_iff.mp (by
          rw [hthr] at hord; omega)
        obtain ⟨mm, hm, hmm⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
        have hz : ((n : ℤ)) ^ mm = 1 := hmm
        have hz' : ((n ^ mm : ℕ) : ℤ) = 1 := by push_cast; exact hz
        have h1 : n ^ mm = 1 := by exact_mod_cast hz'
        rcases Nat.pow_eq_one.mp h1 with h | h <;> omega
      · have hk4pos : 0 < k ^ 4 := by positivity
        have h1 : ((n : ZMod 1)) = 1 := Subsingleton.elim _ _
        rw [h1, orderOf_one, hthr] at hord
        omega
    · exact hge
  haveI : NeZero r := ⟨by omega⟩
  -- coprimality
  have hcop : Nat.Coprime n r := by
    have hfin : IsOfFinOrder ((n : ZMod r)) := orderOf_pos_iff.mp (by omega)
    exact (ZMod.isUnit_iff_coprime n r).mp hfin.isUnit
  have hcopp : Nat.Coprime p r := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  -- the field with a primitive `r`-th root of unity
  set F := AlgebraicClosure (ZMod p) with hFdef
  haveI : NeZero ((r : ℕ) : F) := by
    constructor
    have h1 : ((r : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    have h2 : ((r : ℕ) : F) = algebraMap (ZMod p) F ((r : ℕ) : ZMod p) := by push_cast; ring
    rw [h2]
    simpa using fun h => h1 ((algebraMap (ZMod p) F).injective (by simpa using h))
  obtain ⟨ζ, hζroot⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic r F) (by
    rw [Polynomial.degree_cyclotomic]
    have hpos : 0 < r.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast hpos.ne')
  have hζ : IsPrimitiveRoot ζ r := Polynomial.isRoot_cyclotomic_iff.mp hζroot
  -- the group generated by `p` and `n` modulo `r`
  set G : Finset (ZMod r) :=
    Finset.univ.filter (fun x : ZMod r => ∃ i j : ℕ, x = ((p ^ i * n ^ j : ℕ) : ZMod r)) with hGdef
  set t := G.card with htdef
  have hmemG : ∀ i j : ℕ, ((p ^ i * n ^ j : ℕ) : ZMod r) ∈ G := by
    intro i j
    simp only [hGdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, j, rfl⟩
  -- `t` is at least the order of `n` mod `r`
  have htord : orderOf ((n : ZMod r)) ≤ t := by
    set d := orderOf ((n : ZMod r)) with hddef
    have himg : (Finset.range d).image (fun i => ((n : ZMod r)) ^ i) ⊆ G := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, _, rfl⟩ := hx
      have : ((n : ZMod r)) ^ i = ((p ^ 0 * n ^ i : ℕ) : ZMod r) := by push_cast; ring
      rw [this]
      exact hmemG 0 i
    have hcard : ((Finset.range d).image (fun i => ((n : ZMod r)) ^ i)).card = d := by
      refine Finset.card_image_of_injOn ?_ |>.trans (Finset.card_range d)
      intro x hx y hy hxy
      simp only [Finset.coe_range, Set.mem_Iio] at hx hy
      exact pow_injOn_Iio_orderOf (x := (n : ZMod r)) hx hy hxy
    calc d = _ := hcard.symm
      _ ≤ t := Finset.card_le_card himg
  have htk : k ^ 4 < t := lt_of_lt_of_le (hthr ▸ hord) htord
  -- `t ≤ φ(r)`
  have httot : t ≤ Nat.totient r := by
    have hsub : G ⊆ Finset.univ.image (fun u : (ZMod r)ˣ => (u : ZMod r)) := by
      intro x hx
      simp only [hGdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨i, j, rfl⟩ := hx
      have hu : IsUnit (((p ^ i * n ^ j : ℕ) : ZMod r)) := by
        have h1 : IsUnit ((p : ZMod r)) := (ZMod.isUnit_iff_coprime p r).mpr hcopp
        have h2 : IsUnit ((n : ZMod r)) := (ZMod.isUnit_iff_coprime n r).mpr hcop
        have : ((p ^ i * n ^ j : ℕ) : ZMod r) = (p : ZMod r) ^ i * (n : ZMod r) ^ j := by
          push_cast; ring
        rw [this]
        exact (h1.pow i).mul (h2.pow j)
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨hu.unit, hu.unit_spec⟩
    calc t ≤ (Finset.univ.image (fun u : (ZMod r)ˣ => (u : ZMod r))).card :=
          Finset.card_le_card hsub
      _ = Fintype.card (ZMod r)ˣ := by
          rw [Finset.card_image_of_injective _ (fun a b h => Units.ext h), Finset.card_univ]
      _ = Nat.totient r := ZMod.card_units_eq_totient r
  have htotlt : Nat.totient r < r := Nat.totient_lt r (by omega)
  -- `k ≥ 3`
  have hk3 : 3 ≤ k := by
    rcases Nat.lt_or_ge k 3 with hlt | hge
    · exfalso
      have hk : k = 2 := by omega
      have h1 : k ^ 4 = 16 := by rw [hk]; norm_num
      have h2 : (2 : ℕ) ^ k = 4 := by rw [hk]; norm_num
      omega
    · exact hge
  -- the parameters
  set sigma := Nat.sqrt t with hsigmadef
  set m := 2 * sigma * k with hmdef
  have hmt : m + 2 < t := arith_deg hk3 htk
  have hell : ell n = 2 * Nat.sqrt (Nat.totient r) * k + 2 := rfl
  have hmell : m + 2 ≤ ell n := by
    rw [hell, hmdef]
    have : sigma ≤ Nat.sqrt (Nat.totient r) := Nat.sqrt_le_sqrt httot
    exact Nat.add_le_add_right (Nat.mul_le_mul_right k (Nat.mul_le_mul_left 2 this)) 2
  have hellp : ell n < p := by
    have := arith_ell hk3 htk httot htotlt
    rw [hell]
    omega
  -- introspectivity for the tested polynomials
  have hintroP : ∀ a : ℕ, 1 ≤ a → a ≤ ell n → Intro p r p (X + C (a : ZMod p)) :=
    fun a _ _ => intro_p_self hp
  have hintroN : ∀ a : ℕ, 1 ≤ a → a ≤ ell n → Intro p r n (X + C (a : ZMod p)) :=
    fun a h1 h2 => intro_n_of_poly hpn (hpoly a h1 h2)
  have hintroU : ∀ (i j : ℕ) (a : ℕ), 1 ≤ a → a ≤ ell n →
      Intro p r (p ^ i * n ^ j) (X + C (a : ZMod p)) := by
    intro i j a h1 h2
    exact ((hintroP a h1 h2).pow i).mul_nat ((hintroN a h1 h2).pow j)
  -- the set `B` of tested values, avoiding the (at most one) value with `ζ + a = 0`
  set B : Finset ℕ := (Finset.Icc 1 (m + 2)).filter
    (fun a => ζ + (algebraMap (ZMod p) F) (a : ZMod p) ≠ 0) with hBdef
  have hBsub : ∀ a ∈ B, 1 ≤ a ∧ a ≤ m + 2 := by
    intro a ha
    simp only [hBdef, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ha.1
  have hBp : ∀ a ∈ B, a < p := by
    intro a ha
    have := (hBsub a ha).2
    omega
  have hBne : ∀ a ∈ B, ζ + (algebraMap (ZMod p) F) (a : ZMod p) ≠ 0 := by
    intro a ha
    simp only [hBdef, Finset.mem_filter] at ha
    exact ha.2
  have hBsubset : B ⊆ Finset.Icc 1 (m + 2) := Finset.filter_subset _ _
  have hBcard : m + 1 ≤ B.card := by
    have hbad : ((Finset.Icc 1 (m + 2)) \ B).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro a ha b hb
      rw [Finset.mem_sdiff, hBdef, Finset.mem_filter, not_and_or, not_not] at ha hb
      have ha1 := Finset.mem_Icc.mp ha.1
      have hb1 := Finset.mem_Icc.mp hb.1
      have ha2 : ζ + (algebraMap (ZMod p) F) ((a : ℕ) : ZMod p) = 0 := by
        rcases ha.2 with h | h
        · exact absurd ha.1 h
        · exact h
      have hb2 : ζ + (algebraMap (ZMod p) F) ((b : ℕ) : ZMod p) = 0 := by
        rcases hb.2 with h | h
        · exact absurd hb.1 h
        · exact h
      have hab : ((a : ZMod p)) = ((b : ZMod p)) := by
        refine (algebraMap (ZMod p) F).injective ?_
        linear_combination ha2 - hb2
      have hva := congrArg ZMod.val hab
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hva
      exact hva
    have hsplit := Finset.card_sdiff_add_card_eq_card hBsubset
    rw [Nat.card_Icc] at hsplit
    omega
  have hBcard' : B.card < t := by
    have h1 : B.card ≤ (Finset.Icc 1 (m + 2)).card := Finset.card_le_card hBsubset
    rw [Nat.card_Icc] at h1
    omega
  -- the main dichotomy
  by_cases hpow : ∃ e, n = p ^ e
  · obtain ⟨e, he⟩ := hpow
    rcases Nat.lt_or_ge e 2 with hlt | hge
    · interval_cases e
      · simp at he; omega
      · rw [pow_one] at he; rw [he]; exact hp
    · exact absurd he (hpp p e hge)
  · exfalso
    -- pigeonhole in `G`
    have hcardS : G.card < ((Finset.range (sigma + 1)) ×ˢ (Finset.range (sigma + 1))).card := by
      rw [Finset.card_product, Finset.card_range]
      have := Nat.lt_succ_sqrt' t
      calc G.card = t := rfl
        _ < (sigma + 1) ^ 2 := by rw [hsigmadef]; exact Nat.lt_succ_sqrt' t
        _ = (sigma + 1) * (sigma + 1) := by ring
    obtain ⟨x, hx, y, hy, hxy, hfxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardS
      (f := fun ij : ℕ × ℕ => ((p ^ ij.1 * n ^ ij.2 : ℕ) : ZMod r))
      (by intro ij _; exact hmemG ij.1 ij.2)
    simp only [Finset.mem_product, Finset.mem_range] at hx hy
    -- the two introspective numbers
    set u₁ := p ^ x.1 * n ^ x.2 with hu₁def
    set u₂ := p ^ y.1 * n ^ y.2 with hu₂def
    have hune : u₁ ≠ u₂ := by
      intro heq
      exact hpow (pow_of_ne hp hn2 hxy heq)
    -- an upper bound on both
    have hbound : ∀ (i j : ℕ), i ≤ sigma → j ≤ sigma → p ^ i * n ^ j < 2 ^ m := by
      intro i j hi hj
      have h1 : p ^ i * n ^ j ≤ n ^ sigma * n ^ sigma := by
        exact Nat.mul_le_mul (le_trans (Nat.pow_le_pow_left hpn' i)
          (Nat.pow_le_pow_right (by omega) hi)) (Nat.pow_le_pow_right (by omega) hj)
      have h2 : n ^ sigma * n ^ sigma = n ^ (2 * sigma) := by rw [← pow_add]; ring_nf
      have hsigmapos : 0 < sigma := by
        rw [hsigmadef]
        have : 0 < t := by omega
        exact Nat.sqrt_pos.mpr (by omega)
      have h3 : n ^ (2 * sigma) < (2 ^ k) ^ (2 * sigma) :=
        Nat.pow_lt_pow_left hnk (by omega)
      have h4 : (2 ^ k) ^ (2 * sigma) = 2 ^ m := by
        rw [← pow_mul, hmdef]; ring_nf
      omega
    -- apply the counting lemma to the larger of the two
    have hkey : ∀ (i j i' j' : ℕ), i ≤ sigma → j ≤ sigma → i' ≤ sigma → j' ≤ sigma →
        p ^ i' * n ^ j' < p ^ i * n ^ j →
        ((p ^ i' * n ^ j' : ℕ) : ZMod r) = ((p ^ i * n ^ j : ℕ) : ZMod r) → False := by
      intro i j i' j' hi hj hi' hj' hlt hcong
      have hmain := two_pow_card_le (t := t) (u₁ := p ^ i * n ^ j) (u₂ := p ^ i' * n ^ j')
        hp hr2 hζ B hBp hBne G (le_refl t)
        (by
          intro x hx
          simp only [hGdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          obtain ⟨i₀, j₀, rfl⟩ := hx
          refine ⟨p ^ i₀ * n ^ j₀, rfl, ?_⟩
          intro a ha
          exact hintroU i₀ j₀ a (hBsub a ha).1 (le_trans (hBsub a ha).2 hmell))
        hBcard'
        (fun a ha => hintroU i j a (hBsub a ha).1 (le_trans (hBsub a ha).2 hmell))
        (fun a ha => hintroU i' j' a (hBsub a ha).1 (le_trans (hBsub a ha).2 hmell))
        hlt hcong.symm
      have h1 : 2 ^ (m + 1) ≤ 2 ^ B.card := Nat.pow_le_pow_right (by norm_num) hBcard
      have h2 : p ^ i * n ^ j < 2 ^ m := hbound i j hi hj
      have h3 : 2 ^ m < 2 ^ (m + 1) := by
        apply Nat.pow_lt_pow_right (by norm_num); omega
      omega
    rcases lt_trichotomy u₁ u₂ with hlt | heq | hlt
    · exact hkey y.1 y.2 x.1 x.2 (Nat.lt_succ_iff.mp hy.1) (Nat.lt_succ_iff.mp hy.2)
        (Nat.lt_succ_iff.mp hx.1) (Nat.lt_succ_iff.mp hx.2) hlt hfxy
    · exact hune heq
    · exact hkey x.1 x.2 y.1 y.2 (Nat.lt_succ_iff.mp hx.1) (Nat.lt_succ_iff.mp hx.2)
        (Nat.lt_succ_iff.mp hy.1) (Nat.lt_succ_iff.mp hy.2) hlt hfxy.symm

/-- The AKS criterion is correct. -/
theorem accepts_iff_prime (n : ℕ) : AKSAccepts n ↔ n.Prime :=
  ⟨prime_of_accepts, accepts_of_prime⟩

end AKS

/-
The easy direction: a prime is accepted by the AKS criterion.
-/
import RequestProject.AKS.Defs

open Polynomial

namespace AKS

/-- Freshman's dream: over `ZMod p` with `p` prime, `(X + a)^p = X^p + a`. -/
theorem add_pow_prime_eq (p : ℕ) (hp : p.Prime) (a : ZMod p) :
    (X + C a) ^ p = X ^ p + C a := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [add_pow_char]
  congr 1
  rw [← C_pow, ZMod.pow_card]

theorem accepts_of_prime {n : ℕ} (hp : n.Prime) : AKSAccepts n := by
  refine ⟨hp.two_le, ?_, ?_, Or.inr ?_⟩
  · intro a b hb h
    have := (hp.pow_eq_iff (a := a) (k := b)).mp h.symm
    omega
  · intro a _ _
    rcases (Nat.gcd_dvd_right a n) with ⟨c, hc⟩
    exact hp.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right a n)
  · intro a _ _
    rw [add_pow_prime_eq n hp, sub_self]
    exact dvd_zero _

end AKS

/-
Computable ingredients of the AKS algorithm: multiplicative order, integer roots and the
perfect-power test.
-/
import Mathlib
import RequestProject.AKS.Defs

namespace AKS

/-! ### Multiplicative order -/

/-- Computable multiplicative order of `n` modulo `r` (`0` if `n` is not invertible). -/
def ordMod (n r : ℕ) : ℕ :=
  ((Finset.Icc 1 r).filter (fun i => ((n : ZMod r)) ^ i = 1)).min.getD 0

theorem orderOf_le_mod (r : ℕ) [NeZero r] (x : ZMod r) : orderOf x ≤ r := by
  have hinj : Set.InjOn (fun i => x ^ i) (Set.Iio (orderOf x)) := pow_injOn_Iio_orderOf
  have hcard : ((Finset.range (orderOf x)).image (fun i => x ^ i)).card = orderOf x := by
    rw [Finset.card_image_of_injOn (by simpa [Finset.coe_range] using hinj), Finset.card_range]
  calc orderOf x = _ := hcard.symm
    _ ≤ Fintype.card (ZMod r) := Finset.card_le_univ _
    _ = r := ZMod.card r

theorem ordMod_eq_orderOf (n r : ℕ) [NeZero r] : ordMod n r = orderOf ((n : ZMod r)) := by
  classical
  set x : ZMod r := (n : ZMod r) with hx
  set S := (Finset.Icc 1 r).filter (fun i => x ^ i = 1) with hS
  have hmemS : ∀ i, i ∈ S ↔ (1 ≤ i ∧ i ≤ r) ∧ x ^ i = 1 := by
    intro i
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
  rcases hmin : S.min with _ | m
  · -- `S` is empty
    have hSempty : S = ∅ := Finset.min_eq_top.mp hmin
    have : orderOf x = 0 := by
      by_contra hcon
      have hpos : 0 < orderOf x := Nat.pos_of_ne_zero hcon
      have hmem : orderOf x ∈ S := by
        rw [hmemS]
        exact ⟨⟨hpos, orderOf_le_mod r x⟩, pow_orderOf_eq_one x⟩
      rw [hSempty] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    rw [ordMod, ← hS, hmin, this]
    rfl
  · have hmemm : m ∈ S := Finset.mem_of_min hmin
    have hm := (hmemS m).mp hmemm
    have hpos : 0 < orderOf x := by
      rw [orderOf_pos_iff]
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm.1.1, hm.2⟩
    have hle : orderOf x ≤ m := orderOf_le_of_pow_eq_one hm.1.1 hm.2
    have hmem2 : orderOf x ∈ S := by
      rw [hmemS]
      exact ⟨⟨hpos, orderOf_le_mod r x⟩, pow_orderOf_eq_one x⟩
    have hge : m ≤ orderOf x := Finset.min_le_of_eq hmem2 hmin
    rw [ordMod, ← hS, hmin]
    simp only [Option.getD_some]
    omega

/-! ### Integer roots -/

/-- Auxiliary binary search for the integer `b`-th root of `n`. -/
def rootAux (b n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then lo
      else
        let mid := (lo + hi) / 2
        if mid ^ b ≤ n then rootAux b n fuel mid hi else rootAux b n fuel lo mid

/-- The integer `b`-th root of `n`: the largest `a` with `a ^ b ≤ n`. -/
def natRoot (b n : ℕ) : ℕ := rootAux b n (n + 2) 0 (n + 1)

theorem rootAux_spec (b n : ℕ) :
    ∀ (fuel lo hi : ℕ), hi - lo ≤ fuel → lo ^ b ≤ n → n < hi ^ b →
      (rootAux b n fuel lo hi) ^ b ≤ n ∧ n < (rootAux b n fuel lo hi + 1) ^ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi hgap hlo hhi
      exfalso
      have hle : hi ≤ lo := by omega
      have : hi ^ b ≤ lo ^ b := Nat.pow_le_pow_left hle b
      omega
  | succ fuel ih =>
      intro lo hi hgap hlo hhi
      rw [rootAux]
      by_cases hcase : hi ≤ lo + 1
      · simp only [hcase, if_true]
        refine ⟨hlo, ?_⟩
        have hlt : lo < hi := by
          by_contra hcon
          push_neg at hcon
          have : hi ^ b ≤ lo ^ b := Nat.pow_le_pow_left hcon b
          omega
        have : hi = lo + 1 := by omega
        rwa [this] at hhi
      · simp only [hcase, if_false]
        push_neg at hcase
        set mid := (lo + hi) / 2 with hmid
        have hlomid : lo < mid := by omega
        have hmidhi : mid < hi := by omega
        by_cases hmidle : mid ^ b ≤ n
        · simp only [hmidle, if_true]
          exact ih mid hi (by omega) hmidle hhi
        · simp only [hmidle, if_false]
          exact ih lo mid (by omega) hlo (by omega)

theorem natRoot_spec {b : ℕ} (hb : 1 ≤ b) (n : ℕ) :
    (natRoot b n) ^ b ≤ n ∧ n < (natRoot b n + 1) ^ b := by
  refine rootAux_spec b n (n + 2) 0 (n + 1) (by omega) ?_ ?_
  · rw [zero_pow (by omega)]
    exact Nat.zero_le n
  · calc n < n + 1 := by omega
      _ = (n + 1) ^ 1 := by ring
      _ ≤ (n + 1) ^ b := Nat.pow_le_pow_right (by omega) hb

theorem natRoot_eq {b n a : ℕ} (hb : 1 ≤ b) (h : n = a ^ b) : natRoot b n = a := by
  obtain ⟨h1, h2⟩ := natRoot_spec hb n
  by_contra hcon
  rcases Nat.lt_or_ge (natRoot b n) a with hlt | hge
  · have : (natRoot b n + 1) ^ b ≤ a ^ b := Nat.pow_le_pow_left (by omega) b
    omega
  · have hgt : a < natRoot b n := by omega
    have : (a + 1) ^ b ≤ (natRoot b n) ^ b := Nat.pow_le_pow_left (by omega) b
    have h3 : a ^ b < (a + 1) ^ b := by
      refine Nat.pow_lt_pow_left (by omega) (by omega)
    omega

/-! ### Perfect powers -/

/-- Computable test for `n` being a perfect power `a ^ b` with `b ≥ 2`. -/
def isPerfectPower (n : ℕ) : Bool :=
  ((List.range (bits n + 1)).filter (fun b => 2 ≤ b)).any (fun b => (natRoot b n) ^ b == n)

theorem isPerfectPower_iff {n : ℕ} (hn : 2 ≤ n) :
    isPerfectPower n = true ↔ ∃ a b : ℕ, 2 ≤ b ∧ n = a ^ b := by
  constructor
  · intro h
    rw [isPerfectPower, List.any_eq_true] at h
    obtain ⟨b, hb, heq⟩ := h
    rw [List.mem_filter] at hb
    have hb2 : 2 ≤ b := by simpa using hb.2
    exact ⟨natRoot b n, b, hb2, (beq_iff_eq.mp heq).symm⟩
  · rintro ⟨a, b, hb, rfl⟩
    have ha : 2 ≤ a := by
      rcases Nat.lt_or_ge a 2 with hlt | hge
      · interval_cases a
        · rw [zero_pow (by omega : b ≠ 0)] at hn; omega
        · rw [one_pow] at hn; omega
      · exact hge
    have hblt : b < bits (a ^ b) := by
      have h1 : (2:ℕ) ^ b ≤ a ^ b := Nat.pow_le_pow_left ha b
      have h2 : a ^ b < 2 ^ bits (a ^ b) := Nat.lt_size_self _
      have : (2:ℕ) ^ b < 2 ^ bits (a ^ b) := lt_of_le_of_lt h1 h2
      exact (Nat.pow_lt_pow_iff_right (by omega)).mp this
    rw [isPerfectPower, List.any_eq_true]
    refine ⟨b, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨List.mem_range.mpr (by omega), by simpa using hb⟩
    · simp [natRoot_eq (by omega : 1 ≤ b) (rfl : a ^ b = a ^ b)]

end AKS

/-
The AKS algorithm as an explicit computable boolean-valued procedure, together with a proof
that it decides primality.
-/
import Mathlib
import RequestProject.AKS.Defs
import RequestProject.AKS.Complete
import RequestProject.AKS.RBound
import RequestProject.AKS.Quot
import RequestProject.AKS.Compute

open Polynomial

namespace AKS

/-! ### The modulus `r` is computable -/

theorem one_le_rOf {n : ℕ} (hn : 2 ≤ n) : 1 ≤ rOf n := by
  rcases Nat.eq_zero_or_pos (rOf n) with h0 | h
  · exfalso
    have hmem := thr_lt_orderOf n hn
    rw [h0] at hmem
    have hz : orderOf ((n : ZMod 0)) = 0 := by
      rw [orderOf_eq_zero_iff]
      intro hfin
      obtain ⟨k, hk, hk1⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
      have hcast : ((n ^ k : ℕ) : ℤ) = 1 := by push_cast; exact_mod_cast hk1
      have hnk : n ^ k = 1 := by exact_mod_cast hcast
      have h2 : (2:ℕ) ^ k ≤ n ^ k := Nat.pow_le_pow_left hn k
      have h3 : (2:ℕ) ≤ 2 ^ k := by
        calc (2:ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
      omega
    omega
  · exact h

/-- Linear search for the least modulus with large multiplicative order. -/
def rSearchAux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | fuel + 1, r => if thr n < ordMod n r then r else rSearchAux n fuel (r + 1)

/-- The computable version of `rOf`. -/
def rAlg (n : ℕ) : ℕ := rSearchAux n (2 * (bits n) ^ 12 + 1) 1

theorem rSearchAux_eq {n : ℕ} (hn : 2 ≤ n) :
    ∀ (fuel r : ℕ), 1 ≤ r → r ≤ rOf n → rOf n ≤ r + fuel → rSearchAux n fuel r = rOf n := by
  intro fuel
  induction fuel with
  | zero =>
      intro r _ hle hge
      have : r = rOf n := by omega
      rw [rSearchAux, this]
  | succ fuel ih =>
      intro r hr1 hle hge
      haveI : NeZero r := ⟨by omega⟩
      rw [rSearchAux]
      by_cases hcase : thr n < ordMod n r
      · rw [if_pos hcase]
        rw [ordMod_eq_orderOf] at hcase
        have : rOf n ≤ r := Nat.sInf_le hcase
        omega
      · rw [if_neg hcase]
        rw [ordMod_eq_orderOf] at hcase
        have hne : r ≠ rOf n := by
          intro h
          exact hcase (h ▸ thr_lt_orderOf n hn)
        exact ih (r + 1) (by omega) (by omega) (by omega)

theorem rAlg_eq {n : ℕ} (hn : 2 ≤ n) : rAlg n = rOf n :=
  rSearchAux_eq hn _ 1 le_rfl (one_le_rOf hn) (by have := rOf_le n hn; omega)

/-- The computable version of `ell`. -/
def ellAlg (n : ℕ) : ℕ := 2 * Nat.sqrt (Nat.totient (rAlg n)) * bits n + 2

theorem ellAlg_eq {n : ℕ} (hn : 2 ≤ n) : ellAlg n = ell n := by
  rw [ellAlg, ell, rAlg_eq hn]

/-- The number of polynomial congruences tested is polynomially bounded in the bit length. -/
theorem ellAlg_le {n : ℕ} (hn : 2 ≤ n) : ellAlg n ≤ 4 * bits n ^ 7 + 2 := by
  have hr : rAlg n ≤ 2 * bits n ^ 12 := by
    rw [rAlg_eq hn]; exact rOf_le n hn
  have htot : Nat.totient (rAlg n) ≤ 2 * bits n ^ 12 :=
    le_trans (Nat.totient_le _) hr
  have hsq : Nat.sqrt (Nat.totient (rAlg n)) ≤ 2 * bits n ^ 6 := by
    have hle : Nat.totient (rAlg n) ≤ (2 * bits n ^ 6) * (2 * bits n ^ 6) := by
      refine le_trans htot ?_
      have : 2 * bits n ^ 12 ≤ 4 * bits n ^ 12 := by omega
      calc 2 * bits n ^ 12 ≤ 4 * bits n ^ 12 := this
        _ = (2 * bits n ^ 6) * (2 * bits n ^ 6) := by ring
    calc Nat.sqrt (Nat.totient (rAlg n)) ≤ Nat.sqrt ((2 * bits n ^ 6) * (2 * bits n ^ 6)) :=
          Nat.sqrt_le_sqrt hle
      _ = 2 * bits n ^ 6 := Nat.sqrt_eq _
  calc ellAlg n = 2 * Nat.sqrt (Nat.totient (rAlg n)) * bits n + 2 := rfl
    _ ≤ 2 * (2 * bits n ^ 6) * bits n + 2 := by
        have := Nat.mul_le_mul_right (bits n) (Nat.mul_le_mul_left 2 hsq)
        omega
    _ = 4 * bits n ^ 7 + 2 := by ring

/-! ### The polynomial congruence test -/

/-- The test `(X + a)^n = X^n + a` in the computable model of `(ZMod n)[X]/(X^r-1)`. -/
def polyTestC (n r : ℕ) [NeZero r] (a : ℕ) : Bool :=
  decide (cpow (cadd (cmonomial (r := r) n 1) (cconst (r := r) n (a : ZMod n))) n =
    cadd (cmonomial (r := r) n n) (cconst (r := r) n (a : ZMod n)))

/-- The polynomial congruence test, as a function of `r` (`false` for `r = 0`). -/
def polyTest (n r a : ℕ) : Bool :=
  match r with
  | 0 => false
  | r' + 1 => polyTestC n (r' + 1) a

theorem toQ_cconst {n r : ℕ} [NeZero r] (a : ZMod n) :
    toQ (cconst (r := r) n a) = mkQ n r (C a) := by
  rw [toQ, toPoly_cconst]

theorem polyTestC_iff {n r : ℕ} [NeZero r] [Fact (1 < n)] (a : ℕ) :
    polyTestC n r a = true ↔
      (X ^ r - 1 : (ZMod n)[X]) ∣ (X + C (a : ZMod n)) ^ n - (X ^ n + C (a : ZMod n)) := by
  rw [polyTestC, decide_eq_true_iff]
  have key : (cpow (cadd (cmonomial (r := r) n 1) (cconst (r := r) n (a : ZMod n))) n =
      cadd (cmonomial (r := r) n n) (cconst (r := r) n (a : ZMod n))) ↔
      mkQ n r ((X + C (a : ZMod n)) ^ n) = mkQ n r (X ^ n + C (a : ZMod n)) := by
    constructor
    · intro h
      have h2 := congrArg (toQ (n := n) (r := r)) h
      rw [toQ_cpow, toQ_cadd, toQ_cadd, toQ_cmonomial, toQ_cmonomial, toQ_cconst,
        ← map_add, ← map_pow, ← map_add, pow_one] at h2
      exact h2
    · intro h
      refine toQ_injective ?_
      rw [toQ_cpow, toQ_cadd, toQ_cadd, toQ_cmonomial, toQ_cmonomial, toQ_cconst,
        ← map_add, ← map_pow, ← map_add, pow_one]
      exact h
  rw [key, mkQ_eq_iff]

theorem polyTest_iff {n r : ℕ} (hr : r ≠ 0) (hn : 1 < n) (a : ℕ) :
    polyTest n r a = true ↔
      (X ^ r - 1 : (ZMod n)[X]) ∣ (X + C (a : ZMod n)) ^ n - (X ^ n + C (a : ZMod n)) := by
  haveI : Fact (1 < n) := ⟨hn⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  haveI : NeZero (r' + 1) := ⟨by omega⟩
  rw [polyTest]
  exact polyTestC_iff a

/-! ### The full algorithm -/

/-- The AKS primality test as a computable boolean function. -/
def aksBool (n : ℕ) : Bool :=
  2 ≤ n &&
  !isPerfectPower n &&
  ((List.range (rAlg n + 1)).all fun a =>
    a == 0 || Nat.gcd a n == 1 || Nat.gcd a n == n) &&
  (n ≤ rAlg n ||
    (List.range (ellAlg n + 1)).all fun a => a == 0 || polyTest n (rAlg n) a)

theorem aksBool_iff_accepts (n : ℕ) : aksBool n = true ↔ AKSAccepts n := by
  rw [aksBool]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    Bool.or_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h2, hpp⟩, hgcd⟩, hlast⟩
    have hr0 : rOf n ≠ 0 := by have := one_le_rOf h2; omega
    rw [rAlg_eq h2] at hgcd hlast
    rw [ellAlg_eq h2] at hlast
    refine ⟨h2, ?_, ?_, ?_⟩
    · intro a b hb hcon
      have hT : isPerfectPower n = true := (isPerfectPower_iff h2).mpr ⟨a, b, hb, hcon⟩
      rw [hpp] at hT
      exact Bool.noConfusion hT
    · intro a ha1 har
      rcases hgcd a (by omega) with (h | h) | h
      · omega
      · exact Or.inl h
      · exact Or.inr h
    · rcases hlast with hle | hall
      · exact Or.inl hle
      · refine Or.inr ?_
        intro a ha1 hae
        rcases hall a (by omega) with h | h
        · omega
        · exact (polyTest_iff (n := n) (r := rOf n) hr0 (by omega) a).mp h
  · rintro ⟨h2, hpp, hgcd, hlast⟩
    have hr0 : rOf n ≠ 0 := by have := one_le_rOf h2; omega
    rw [rAlg_eq h2, ellAlg_eq h2]
    refine ⟨⟨⟨h2, ?_⟩, ?_⟩, ?_⟩
    · rcases Bool.eq_false_or_eq_true (isPerfectPower n) with h | h
      · obtain ⟨a, b, hb, heq⟩ := (isPerfectPower_iff h2).mp h
        exact absurd heq (hpp a b hb)
      · exact h
    · intro a ha
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · exact Or.inl (Or.inl rfl)
      · rcases hgcd a hapos (by omega) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    · rcases hlast with hle | hall
      · exact Or.inl hle
      · refine Or.inr ?_
        intro a ha
        rcases Nat.eq_zero_or_pos a with rfl | hapos
        · exact Or.inl rfl
        · exact Or.inr ((polyTest_iff (n := n) (r := rOf n) hr0 (by omega) a).mpr
            (hall a hapos (by omega)))

/-- **Correctness of the AKS algorithm**: the computable test `aksBool` decides primality. -/
theorem aksBool_iff_prime (n : ℕ) : aksBool n = true ↔ n.Prime :=
  (aksBool_iff_accepts n).trans (accepts_iff_prime n)

end AKS

/-
A Chebyshev-type lower bound for `lcm (1, ..., B)`, obtained from the fact that the central
binomial coefficient divides it.
-/
import Mathlib

namespace AKS

/-- The least common multiple of `1, 2, ..., B`. -/
def lcmUpTo (B : ℕ) : ℕ := (Finset.Icc 1 B).lcm id

theorem lcmUpTo_pos (B : ℕ) : 0 < lcmUpTo B := by
  rcases Nat.eq_zero_or_pos (lcmUpTo B) with h | h
  · exfalso
    rw [lcmUpTo, Finset.lcm_eq_zero_iff] at h
    obtain ⟨x, hx, hx0⟩ := h
    simp only [Finset.mem_Icc] at hx
    simp only [id] at hx0
    omega
  · exact h

theorem dvd_lcmUpTo {m B : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ B) : m ∣ lcmUpTo B :=
  Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨h1, h2⟩)

/-- The central binomial coefficient `C(2q, q)` divides `lcm (1, ..., 2q)`. -/
theorem centralBinom_dvd_lcmUpTo {q : ℕ} (hq : 0 < q) :
    Nat.centralBinom q ∣ lcmUpTo (2 * q) := by
  rw [← Nat.factorization_le_iff_dvd (Nat.centralBinom_ne_zero q) (lcmUpTo_pos _).ne']
  intro P
  by_cases hP : P.Prime
  · set e := (Nat.centralBinom q).factorization P with he
    by_cases he0 : e = 0
    · simp [he0]
    · have hle : P ^ e ≤ 2 * q := by
        rw [he, Nat.centralBinom_eq_two_mul_choose]
        exact Nat.pow_factorization_choose_le (by omega)
      have hdvd : P ^ e ∣ lcmUpTo (2 * q) :=
        dvd_lcmUpTo (Nat.one_le_pow _ _ hP.pos) hle
      have := (hP.pow_dvd_iff_le_factorization (lcmUpTo_pos _).ne').mp hdvd
      simpa using this
  · simp [Nat.factorization_eq_zero_of_not_prime _ hP]

/-- A Chebyshev-type lower bound: `4 ^ q < q * lcm (1, ..., 2q)` for `q ≥ 4`. -/
theorem four_pow_lt_mul_lcmUpTo {q : ℕ} (hq : 4 ≤ q) : 4 ^ q < q * lcmUpTo (2 * q) := by
  have h1 : 4 ^ q < q * Nat.centralBinom q := Nat.four_pow_lt_mul_centralBinom q hq
  have h2 : Nat.centralBinom q ≤ lcmUpTo (2 * q) :=
    Nat.le_of_dvd (lcmUpTo_pos _) (centralBinom_dvd_lcmUpTo (by omega))
  calc 4 ^ q < q * Nat.centralBinom q := h1
    _ ≤ q * lcmUpTo (2 * q) := Nat.mul_le_mul_left q h2

end AKS

/-
The polynomial bound on the AKS modulus `r`.
-/
import RequestProject.AKS.Defs
import RequestProject.AKS.Lcm

namespace AKS

/-- Every `r ≤ B` divides `n ^ c * ∏_{i ≤ s} (n^i - 1)`, provided no `r ≤ B` has
multiplicative order of `n` exceeding `s` and `c` is large enough. -/
theorem dvd_prod_of_no_large_order {n s c B : ℕ} (hn : 2 ≤ n)
    (H : ∀ r : ℕ, r ≤ B → orderOf ((n : ZMod r)) ≤ s)
    (hc : ∀ e : ℕ, 2 ^ e ≤ B → e ≤ c)
    {r : ℕ} (hr1 : 1 ≤ r) (hrB : r ≤ B) :
    r ∣ n ^ c * ∏ i ∈ Finset.Icc 1 s, (n ^ i - 1) := by
  have h2 : ∀ i, 1 ≤ i → 2 ≤ n ^ i := by
    intro i hi
    calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ n ^ i := Nat.pow_le_pow_left hn 1 |>.trans (Nat.pow_le_pow_right (by omega) hi)
  have hprodpos : 0 < ∏ i ∈ Finset.Icc 1 s, (n ^ i - 1) := by
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have := h2 i hi.1
    omega
  set N := n ^ c * ∏ i ∈ Finset.Icc 1 s, (n ^ i - 1) with hN
  have hNpos : 0 < N := Nat.mul_pos (Nat.pow_pos (by omega)) hprodpos
  rw [← Nat.factorization_le_iff_dvd (by omega) hNpos.ne']
  intro P
  by_cases hP : P.Prime
  · set e := r.factorization P with he
    by_cases he0 : e = 0
    · simp [he0]
    · haveI : Fact P.Prime := ⟨hP⟩
      have hPe_dvd_r : P ^ e ∣ r := Nat.ordProj_dvd r P
      have hPeB : P ^ e ≤ B := le_trans (Nat.le_of_dvd (by omega) hPe_dvd_r) hrB
      have hPe2 : (2:ℕ) ^ e ≤ P ^ e := Nat.pow_le_pow_left hP.two_le e
      have hec : e ≤ c := hc e (le_trans hPe2 hPeB)
      have hdvdN : P ^ e ∣ N := by
        by_cases hPn : P ∣ n
        · have h1 : P ^ e ∣ n ^ e := pow_dvd_pow_of_dvd hPn e
          have h2' : n ^ e ∣ n ^ c := pow_dvd_pow n hec
          exact Dvd.dvd.mul_right (h1.trans h2') _
        · have hPe_pos : 0 < P ^ e := Nat.pow_pos hP.pos
          have hPege : 2 ≤ P ^ e := by
            calc 2 ≤ 2 ^ e := by
                  have : 1 ≤ e := by omega
                  calc (2:ℕ) = 2 ^ 1 := by norm_num
                    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) this
              _ ≤ P ^ e := hPe2
          haveI : NeZero (P ^ e) := ⟨by omega⟩
          have hcop : Nat.Coprime n (P ^ e) :=
            (((hP.coprime_iff_not_dvd).mpr hPn).symm).pow_right e
          have hunit : IsUnit ((n : ZMod (P ^ e))) := (ZMod.isUnit_iff_coprime n _).mpr hcop
          set d := orderOf ((n : ZMod (P ^ e))) with hd
          have hdpos : 0 < d := by
            rw [hd, orderOf_pos_iff]
            obtain ⟨u, hu⟩ := hunit
            refine isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf u, ?_, ?_⟩
            · exact orderOf_pos u
            · rw [← hu, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
          have hds : d ≤ s := H (P ^ e) hPeB
          have hpow : ((n : ZMod (P ^ e))) ^ d = 1 := pow_orderOf_eq_one _
          have hmod : (n ^ d : ℕ) ≡ 1 [MOD P ^ e] := by
            have : ((n ^ d : ℕ) : ZMod (P ^ e)) = ((1 : ℕ) : ZMod (P ^ e)) := by
              push_cast; simpa using hpow
            exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
          have hdvd1 : P ^ e ∣ n ^ d - 1 :=
            (Nat.modEq_iff_dvd' (by have := h2 d hdpos; omega)).mp hmod.symm
          refine hdvd1.trans (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ ?_) _)
          simp only [Finset.mem_Icc]
          omega
      exact (hP.pow_dvd_iff_le_factorization hNpos.ne').mp hdvdN
  · simp [Nat.factorization_eq_zero_of_not_prime _ hP]

/-- Key estimate: `k ^ 12 ≤ 2 ^ (12 * k)`. -/
theorem pow_twelve_le (k : ℕ) : k ^ 12 ≤ 2 ^ (12 * k) := by
  have h : k < 2 ^ k := Nat.lt_two_pow_self
  calc k ^ 12 ≤ (2 ^ k) ^ 12 := Nat.pow_le_pow_left h.le 12
    _ = 2 ^ (12 * k) := by rw [← pow_mul]; ring_nf

/-- There is a modulus `r ≤ 2 * (bits n) ^ 12` with `ord_r(n) > thr n`. -/
theorem exists_r_le (n : ℕ) (hn : 2 ≤ n) :
    ∃ r : ℕ, r ≤ 2 * (bits n) ^ 12 ∧ thr n < orderOf ((n : ZMod r)) := by
  classical
  set k := bits n with hk
  have hk2 : 2 ≤ k := by
    rw [hk, bits]
    by_contra hcon
    push_neg at hcon
    have h1 : Nat.size n ≤ 1 := by omega
    rw [Nat.size_le] at h1
    omega
  have hnk : n < 2 ^ k := Nat.lt_size_self n
  set s := thr n with hs
  have hsk : s = k ^ 4 := rfl
  set q := k ^ 12 with hq
  set B := 2 * q with hB
  by_contra hcon
  push_neg at hcon
  have H : ∀ r : ℕ, r ≤ B → orderOf ((n : ZMod r)) ≤ s := fun r hr => hcon r hr
  -- every `r ≤ B` divides `N`
  set c := 13 * k with hc
  have hcbound : ∀ e : ℕ, 2 ^ e ≤ B → e ≤ c := by
    intro e he
    have h1 : B ≤ 2 ^ c := by
      calc B = 2 * k ^ 12 := rfl
        _ ≤ 2 * 2 ^ (12 * k) := by
            exact Nat.mul_le_mul_left 2 (pow_twelve_le k)
        _ = 2 ^ (12 * k + 1) := by rw [pow_succ]; ring
        _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := le_trans he h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  set N := n ^ c * ∏ i ∈ Finset.Icc 1 s, (n ^ i - 1) with hN
  have h2 : ∀ i, 1 ≤ i → 2 ≤ n ^ i := by
    intro i hi
    calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ n ^ i := Nat.pow_le_pow_left hn 1 |>.trans (Nat.pow_le_pow_right (by omega) hi)
  have hprodpos : 0 < ∏ i ∈ Finset.Icc 1 s, (n ^ i - 1) := by
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have := h2 i hi.1
    omega
  have hNpos : 0 < N := Nat.mul_pos (Nat.pow_pos (by omega)) hprodpos
  have hlcm_dvd : lcmUpTo B ∣ N := by
    rw [lcmUpTo]
    refine Finset.lcm_dvd ?_
    intro r hr
    simp only [Finset.mem_Icc] at hr
    exact dvd_prod_of_no_large_order hn H hcbound hr.1 hr.2
  have hlcm_le : lcmUpTo B ≤ N := Nat.le_of_dvd hNpos hlcm_dvd
  -- lower bound
  have hq4 : 4 ≤ q := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 12 := by norm_num
      _ ≤ k ^ 12 := Nat.pow_le_pow_left hk2 12
  have hlow : 4 ^ q < q * N := lt_of_lt_of_le (four_pow_lt_mul_lcmUpTo hq4)
    (Nat.mul_le_mul_left q hlcm_le)
  -- upper bound on `N`
  have hsum : ∑ i ∈ Finset.Icc 1 s, i ≤ s * s := by
    calc ∑ i ∈ Finset.Icc 1 s, i ≤ ∑ _i ∈ Finset.Icc 1 s, s := by
          refine Finset.sum_le_sum ?_
          intro i hi
          simp only [Finset.mem_Icc] at hi
          exact hi.2
      _ = (Finset.Icc 1 s).card * s := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ s * s := by rw [Nat.card_Icc]; exact Nat.mul_le_mul_right s (by omega)
  have hprodle : (∏ i ∈ Finset.Icc 1 s, (n ^ i - 1)) ≤ n ^ (s * s) := by
    calc (∏ i ∈ Finset.Icc 1 s, (n ^ i - 1)) ≤ ∏ i ∈ Finset.Icc 1 s, n ^ i := by
          refine Finset.prod_le_prod' ?_
          intro i
          omega
      _ = n ^ (∑ i ∈ Finset.Icc 1 s, i) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ n ^ (s * s) := Nat.pow_le_pow_right (by omega) hsum
  have hNle : N ≤ n ^ (c + s * s) := by
    rw [hN, pow_add]
    exact Nat.mul_le_mul_left _ hprodle
  have hNle2 : N < 2 ^ (k * (c + s * s)) := by
    calc N ≤ n ^ (c + s * s) := hNle
      _ < (2 ^ k) ^ (c + s * s) := by
          refine Nat.pow_lt_pow_left hnk ?_
          have : 0 < c := by omega
          omega
      _ = 2 ^ (k * (c + s * s)) := by rw [← pow_mul]
  -- combine
  have hqle : q ≤ 2 ^ (12 * k) := pow_twelve_le k
  have h4q : (4:ℕ) ^ q = 2 ^ (2 * q) := by
    rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hfinal : (2:ℕ) ^ (2 * q) < 2 ^ (12 * k + k * (c + s * s)) := by
    calc (2:ℕ) ^ (2 * q) = 4 ^ q := h4q.symm
      _ < q * N := hlow
      _ < 2 ^ (12 * k) * 2 ^ (k * (c + s * s)) :=
          Nat.mul_lt_mul_of_le_of_lt hqle hNle2 (Nat.pow_pos (by norm_num))
      _ = 2 ^ (12 * k + k * (c + s * s)) := by rw [← pow_add]
  have hexp : 2 * q < 12 * k + k * (c + s * s) :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hfinal
  -- but this is false
  rw [hq, hc, hsk] at hexp
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · have hkeq : k = 2 := by omega
    rw [hkeq] at hexp
    norm_num at hexp
  · have h8 : (12:ℕ) ≤ k ^ 8 := le_trans (by norm_num) (Nat.pow_le_pow_left hge 8)
    have h7 : (13:ℕ) ≤ k ^ 7 := le_trans (by norm_num) (Nat.pow_le_pow_left hge 7)
    have h3 : (27:ℕ) ≤ k ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hge 3)
    have key : 12 * k + k * (13 * k + k ^ 4 * k ^ 4) ≤ 2 * k ^ 12 := by
      calc 12 * k + k * (13 * k + k ^ 4 * k ^ 4) = 12 * k + 13 * k ^ 2 + k ^ 9 := by ring
        _ ≤ k ^ 8 * k + k ^ 7 * k ^ 2 + k ^ 9 := by gcongr
        _ = 3 * k ^ 9 := by ring
        _ ≤ (2 * k ^ 3) * k ^ 9 := Nat.mul_le_mul_right _ (by omega)
        _ = 2 * k ^ 12 := by ring
    omega

/-- The AKS modulus is polynomially bounded: `rOf n ≤ 2 * (bits n) ^ 12`. -/
theorem rOf_le (n : ℕ) (hn : 2 ≤ n) : rOf n ≤ 2 * (bits n) ^ 12 := by
  obtain ⟨r, hrle, hr⟩ := exists_r_le n hn
  exact le_trans (Nat.sInf_le hr) hrle

end AKS

/-
The counting heart of the AKS proof: if many numbers are introspective for the
polynomials `X + a` (`a ∈ B`) and two introspective numbers `u₂ < u₁` are congruent
modulo `r`, then `2 ^ |B| ≤ u₁ - u₂`.
-/
import RequestProject.AKS.Introspective

open Polynomial

namespace AKS

variable {p r : ℕ}

/-- Introspectivity passes to products of polynomials indexed by a finset. -/
theorem Intro.prod {m : ℕ} (S : Finset ℕ) (f : ℕ → (ZMod p)[X])
    (h : ∀ a ∈ S, Intro p r m (f a)) : Intro p r m (∏ a ∈ S, f a) := by
  classical
  induction S using Finset.induction with
  | empty => simp [Intro]
  | insert a S ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self _ _)).mul_poly
        (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem Intro.pow {m : ℕ} {f : (ZMod p)[X]} (h : Intro p r m f) (i : ℕ) :
    Intro p r (m ^ i) f := by
  induction i with
  | zero => simpa using intro_one (p := p) (r := r) f
  | succ i ih => rw [pow_succ]; exact ih.mul_nat h

section Counting

variable {F : Type*} [Field F] [Algebra (ZMod p) F]

/-- The polynomial `∏_{a ∈ S} (X + a)` over `ZMod p`. -/
noncomputable def prodPoly (p : ℕ) (S : Finset ℕ) : (ZMod p)[X] :=
  ∏ a ∈ S, (X + C (a : ZMod p))

theorem aeval_prodPoly (ζ : F) (S : Finset ℕ) :
    Polynomial.aeval ζ (prodPoly p S) = ∏ a ∈ S, (ζ + (algebraMap (ZMod p) F) (a : ZMod p)) := by
  simp [prodPoly]

theorem natDegree_prodPoly (S : Finset ℕ) [Fact p.Prime] :
    (prodPoly p S).natDegree = S.card := by
  classical
  rw [prodPoly, Polynomial.natDegree_prod]
  · simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
  · intro a _
    exact Polynomial.X_add_C_ne_zero _

theorem pow_eq_pow_mod {M : Type*} [Monoid M] (ζ : M) {r : ℕ} (h : ζ ^ r = 1) (u : ℕ) :
    ζ ^ u = ζ ^ (u % r) := by
  conv_lhs => rw [← Nat.div_add_mod u r]
  rw [pow_add, pow_mul, h, one_pow, one_mul]

/-- The main counting lemma. -/
theorem two_pow_card_le {t u₁ u₂ : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    {ζ : F} (hζ : IsPrimitiveRoot ζ r)
    (B : Finset ℕ) (hBp : ∀ a ∈ B, a < p)
    (hBne : ∀ a ∈ B, ζ + (algebraMap (ZMod p) F) (a : ZMod p) ≠ 0)
    (G : Finset (ZMod r)) (hGcard : t ≤ G.card)
    (hG : ∀ x : ZMod r, x ∈ G → ∃ u : ℕ, ((u : ℕ) : ZMod r) = x ∧
            ∀ a ∈ B, Intro p r u (X + C (a : ZMod p)))
    (hdeg : B.card < t)
    (hu₁ : ∀ a ∈ B, Intro p r u₁ (X + C (a : ZMod p)))
    (hu₂ : ∀ a ∈ B, Intro p r u₂ (X + C (a : ZMod p)))
    (hlt : u₂ < u₁) (hcong : ((u₁ : ℕ) : ZMod r) = ((u₂ : ℕ) : ZMod r)) :
    2 ^ B.card ≤ u₁ - u₂ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero r := ⟨by omega⟩
  have hζr : ζ ^ r = 1 := hζ.pow_eq_one
  set φ : ZMod p →+* F := algebraMap (ZMod p) F with hφ
  set v : Finset ℕ → F := fun S => ∏ a ∈ S, (ζ + φ (a : ZMod p)) with hv
  have hveq : ∀ S : Finset ℕ, Polynomial.aeval ζ (prodPoly p S) = v S := fun S =>
    aeval_prodPoly ζ S
  have hintroProd : ∀ (u : ℕ), (∀ a ∈ B, Intro p r u (X + C (a : ZMod p))) → ∀ S ⊆ B,
      Intro p r u (prodPoly p S) := by
    intro u hu S hS
    exact Intro.prod S _ (fun a ha => hu a (hS ha))
  -- the key evaluation identity
  have hkey : ∀ (u : ℕ), (∀ a ∈ B, Intro p r u (X + C (a : ZMod p))) → ∀ S ⊆ B,
      Polynomial.aeval (ζ ^ u) (prodPoly p S) = (v S) ^ u := by
    intro u hu S hS
    rw [← hveq S]
    exact ((hintroProd u hu S hS).aeval hζr).symm
  -- Step 1: the map `v` is injective on subsets of `B`
  have hsub : ∀ S ⊆ B, ∀ S' ⊆ B, v S = v S' → S ⊆ S' := by
    intro S hS S' hS' hvv a₀ ha₀S
    by_contra ha₀S'
    set Q : (ZMod p)[X] := prodPoly p S - prodPoly p S' with hQ
    have hcastinj : ∀ a ∈ B, ∀ b ∈ B, ((a : ZMod p) = (b : ZMod p)) → a = b := by
      intro a ha b hb hab
      have := congrArg ZMod.val hab
      rwa [ZMod.val_natCast_of_lt (hBp a ha), ZMod.val_natCast_of_lt (hBp b hb)] at this
    have hQne : Q ≠ 0 := by
      intro h0
      have h1 : Polynomial.eval (-(a₀ : ZMod p)) (prodPoly p S) = 0 := by
        rw [prodPoly, Polynomial.eval_prod]
        exact Finset.prod_eq_zero ha₀S (by simp)
      have h2 : Polynomial.eval (-(a₀ : ZMod p)) (prodPoly p S') ≠ 0 := by
        rw [prodPoly, Polynomial.eval_prod]
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro a ha
        simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        intro hcon
        have : (a : ZMod p) = (a₀ : ZMod p) := by linear_combination hcon
        exact ha₀S' ((hcastinj a (hS' ha) a₀ (hS ha₀S) this) ▸ ha)
      have : Polynomial.eval (-(a₀ : ZMod p)) Q = 0 := by rw [h0]; simp
      rw [hQ, Polynomial.eval_sub, h1, zero_sub, neg_eq_zero] at this
      exact h2 this
    have hdegQ : Q.natDegree ≤ B.card := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      simp only [natDegree_prodPoly]
      exact max_le (Finset.card_le_card hS) (Finset.card_le_card hS')
    set Qf : F[X] := Q.map φ with hQf
    have hQfne : Qf ≠ 0 := by
      rw [hQf, Ne, Polynomial.map_eq_zero_iff φ.injective]
      exact hQne
    have hdegQf : Qf.natDegree ≤ B.card := by
      rw [hQf, Polynomial.natDegree_map_eq_of_injective φ.injective]
      exact hdegQ
    -- the `t` roots
    set T : Finset F := G.image (fun x => ζ ^ (ZMod.val x)) with hT
    have hTcard : T.card = G.card := by
      refine Finset.card_image_of_injOn ?_
      intro x _ y _ hxy
      exact ZMod.val_injective r (hζ.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) hxy)
    have hTroots : T ⊆ Qf.roots.toFinset := by
      intro y hy
      simp only [hT, Finset.mem_image] at hy
      obtain ⟨x, hxG, rfl⟩ := hy
      obtain ⟨u, hu1, hu2⟩ := hG x hxG
      have hval : ZMod.val x = u % r := by rw [← hu1, ZMod.val_natCast]
      have hpow : ζ ^ (ZMod.val x) = ζ ^ u := by rw [hval, ← pow_eq_pow_mod ζ hζr u]
      have hzero : Polynomial.aeval (ζ ^ u) Q = 0 := by
        rw [hQ, map_sub, hkey u hu2 S hS, hkey u hu2 S' hS', hvv, sub_self]
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hQfne]
      rw [Polynomial.IsRoot, hQf, Polynomial.eval_map, ← Polynomial.aeval_def, hpow]
      exact hzero
    have : t ≤ B.card := by
      calc t ≤ G.card := hGcard
        _ = T.card := hTcard.symm
        _ ≤ Qf.roots.toFinset.card := Finset.card_le_card hTroots
        _ ≤ Multiset.card Qf.roots := Multiset.toFinset_card_le _
        _ ≤ Qf.natDegree := Polynomial.card_roots' _
        _ ≤ B.card := hdegQf
    omega
  have hinj : Set.InjOn v (B.powerset : Set (Finset ℕ)) := by
    intro S hS S' hS' hvv
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hS hS'
    exact Finset.Subset.antisymm (hsub S hS S' hS' hvv) (hsub S' hS' S hS hvv.symm)
  -- Step 2: every value is a root of `Y ^ (u₁ - u₂) - 1`
  set D := u₁ - u₂ with hDdef
  have hD : 0 < D := by omega
  have hvne : ∀ S ⊆ B, v S ≠ 0 := by
    intro S hS
    exact Finset.prod_ne_zero_iff.mpr (fun a ha => hBne a (hS ha))
  have hζeq : ζ ^ u₁ = ζ ^ u₂ := by
    have h1 : u₁ % r = u₂ % r := by
      have := congrArg ZMod.val hcong
      rwa [ZMod.val_natCast, ZMod.val_natCast] at this
    rw [pow_eq_pow_mod ζ hζr u₁, pow_eq_pow_mod ζ hζr u₂, h1]
  have hpowD : ∀ S ⊆ B, (v S) ^ D = 1 := by
    intro S hS
    have e1 : (v S) ^ u₁ = (v S) ^ u₂ := by
      rw [← hkey u₁ hu₁ S hS, ← hkey u₂ hu₂ S hS, hζeq]
    have : (v S) ^ u₂ * (v S) ^ D = (v S) ^ u₂ * 1 := by
      rw [mul_one, ← pow_add]
      rw [show u₂ + D = u₁ by omega]
      exact e1
    exact mul_left_cancel₀ (pow_ne_zero _ (hvne S hS)) this
  -- Step 3: count
  have hsubset : (B.powerset.image v) ⊆ (X ^ D - C (1 : F)).roots.toFinset := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_powerset] at hy
    obtain ⟨S, hS, rfl⟩ := hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hD 1)]
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, hpowD S hS, sub_self]
  calc 2 ^ B.card = B.powerset.card := by rw [Finset.card_powerset]
    _ = (B.powerset.image v).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (X ^ D - C (1 : F)).roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ Multiset.card (X ^ D - C (1 : F)).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ D - C (1 : F)).natDegree := Polynomial.card_roots' _
    _ = D := Polynomial.natDegree_X_pow_sub_C

end Counting

end AKS

/-
Definitions for the Agrawal-Kayal-Saxena primality criterion.
-/
import Mathlib

open Polynomial

namespace AKS

/-- Bit length of `n`: the least `k` with `n < 2 ^ k`. -/
def bits (n : ℕ) : ℕ := Nat.size n

/-- The threshold used in the choice of `r`: we require `ord_r(n) > (bits n)^4`. -/
def thr (n : ℕ) : ℕ := (bits n) ^ 4

/-- For every `n ≥ 2` and every bound `s` there is a modulus `r` for which the multiplicative
order of `n` mod `r` exceeds `s`.  (Take a prime `q` larger than `n ∏_{i ≤ s} (n^i - 1)`.) -/
theorem exists_order_gt (n s : ℕ) (hn : 2 ≤ n) : ∃ r : ℕ, s < orderOf ((n : ZMod r)) := by
  set N : ℕ := n * ∏ i ∈ Finset.Icc 1 s, (n ^ i - 1) with hN
  have h2 : ∀ i, 1 ≤ i → 2 ≤ n ^ i := by
    intro i hi
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ ≤ n ^ i := Nat.pow_le_pow_left hn 1 |>.trans (Nat.pow_le_pow_right (by omega) hi)
  have hprodpos : 0 < ∏ i ∈ Finset.Icc 1 s, (n ^ i - 1) := by
    apply Finset.prod_pos
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have := h2 i hi.1
    omega
  have hNpos : 0 < N := Nat.mul_pos (by omega) hprodpos
  obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes (N + 1)
  haveI : Fact q.Prime := ⟨hq⟩
  refine ⟨q, ?_⟩
  by_contra hle
  push_neg at hle
  set d := orderOf ((n : ZMod q)) with hd
  have hqn : ¬ (q ∣ n) := by
    intro h
    have h1 : q ≤ n := Nat.le_of_dvd (by omega) h
    have h2 : n ≤ N := Nat.le_mul_of_pos_right _ hprodpos
    omega
  have hunit : (n : ZMod q) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff] using hqn
  have hdpos : 0 < d := by
    rw [hd, orderOf_pos_iff]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨q - 1, by have := hq.two_le; omega,
      ZMod.pow_card_sub_one_eq_one hunit⟩
  have hpow : ((n : ZMod q)) ^ d = 1 := pow_orderOf_eq_one _
  have hmod : (n ^ d : ℕ) ≡ 1 [MOD q] := by
    have : ((n ^ d : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by push_cast; simpa using hpow
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  have hdvd : q ∣ n ^ d - 1 := (Nat.modEq_iff_dvd' (by have := h2 d hdpos; omega)).mp hmod.symm
  have hqNdvd : q ∣ N := hdvd.trans (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (by
    simp only [Finset.mem_Icc]; omega)) n)
  have := Nat.le_of_dvd hNpos hqNdvd
  omega

theorem exists_r (n : ℕ) (hn : 2 ≤ n) : ∃ r : ℕ, thr n < orderOf ((n : ZMod r)) :=
  exists_order_gt n (thr n) hn

/-- The modulus `r` used by the algorithm: the least `r` such that the multiplicative order of
`n` modulo `r` exceeds `thr n`. -/
noncomputable def rOf (n : ℕ) : ℕ := sInf {r : ℕ | thr n < orderOf ((n : ZMod r))}

theorem thr_lt_orderOf (n : ℕ) (hn : 2 ≤ n) : thr n < orderOf ((n : ZMod (rOf n))) :=
  Nat.sInf_mem (exists_r n hn)

/-- The number of polynomial congruences tested by the algorithm. -/
noncomputable def ell (n : ℕ) : ℕ := 2 * Nat.sqrt (Nat.totient (rOf n)) * bits n + 2

/-- The AKS acceptance predicate: `n ≥ 2`, `n` is not a perfect power, no `a ≤ r` has a
nontrivial common factor with `n`, and either `n ≤ r` or all the polynomial congruences
`(X + a)^n = X^n + a` hold in `(ZMod n)[X] / (X^r - 1)`. -/
noncomputable def AKSAccepts (n : ℕ) : Prop :=
  2 ≤ n ∧
  (∀ a b : ℕ, 2 ≤ b → n ≠ a ^ b) ∧
  (∀ a : ℕ, 1 ≤ a → a ≤ rOf n → Nat.gcd a n = 1 ∨ Nat.gcd a n = n) ∧
  (n ≤ rOf n ∨ ∀ a : ℕ, 1 ≤ a → a ≤ ell n →
     (X ^ rOf n - 1 : (ZMod n)[X]) ∣ (X + C (a : ZMod n)) ^ n - (X ^ n + C (a : ZMod n)))

end AKS

/-
Introspective numbers and polynomials.
-/
import RequestProject.AKS.Defs

open Polynomial

namespace AKS

/-- `m` is *introspective* for the polynomial `f` over `ZMod p` modulo `X ^ r - 1`, i.e.
`f(X)^m ≡ f(X^m) mod (X^r - 1)`. -/
def Intro (p r m : ℕ) (f : (ZMod p)[X]) : Prop :=
  (X ^ r - 1 : (ZMod p)[X]) ∣ f ^ m - expand (ZMod p) m f

variable {p r : ℕ}

theorem intro_one (f : (ZMod p)[X]) : Intro p r 1 f := by
  simp [Intro]

/-- `X^r - 1` divides `X^(m*r) - 1`. -/
theorem dvd_X_pow_mul_sub_one (m : ℕ) :
    (X ^ r - 1 : (ZMod p)[X]) ∣ X ^ (m * r) - 1 := by
  have := sub_dvd_pow_sub_pow (X ^ r : (ZMod p)[X]) 1 m
  simpa [← pow_mul, mul_comm] using this

/-- Introspectivity is preserved by the substitution `X ↦ X^m`. -/
theorem dvd_expand_of_dvd {q : (ZMod p)[X]} (m : ℕ)
    (h : (X ^ r - 1 : (ZMod p)[X]) ∣ q) :
    (X ^ r - 1 : (ZMod p)[X]) ∣ expand (ZMod p) m q := by
  obtain ⟨c, hc⟩ := h
  rw [hc, map_mul]
  have : (expand (ZMod p) m) (X ^ r - 1 : (ZMod p)[X]) = X ^ (m * r) - 1 := by
    simp [pow_mul]
  rw [this]
  exact Dvd.dvd.mul_right (dvd_X_pow_mul_sub_one m) _

theorem Intro.mul_poly {m : ℕ} {f g : (ZMod p)[X]}
    (hf : Intro p r m f) (hg : Intro p r m g) : Intro p r m (f * g) := by
  unfold Intro at *
  have : (f * g) ^ m - expand (ZMod p) m (f * g)
      = f ^ m * (g ^ m - expand (ZMod p) m g)
        + (expand (ZMod p) m g) * (f ^ m - expand (ZMod p) m f) := by
    rw [map_mul]; ring
  rw [this]
  exact dvd_add (Dvd.dvd.mul_left hg _) (Dvd.dvd.mul_left hf _)

theorem Intro.mul_nat {m m' : ℕ} {f : (ZMod p)[X]}
    (hm : Intro p r m f) (hm' : Intro p r m' f) : Intro p r (m * m') f := by
  unfold Intro at *
  have key : f ^ (m * m') - expand (ZMod p) (m * m') f
      = ((f ^ m) ^ m' - (expand (ZMod p) m f) ^ m')
        + ((expand (ZMod p) m ((f ^ m' - expand (ZMod p) m' f)))) := by
    rw [map_sub, map_pow, expand_expand, pow_mul]
    ring
  rw [key]
  refine dvd_add ?_ (dvd_expand_of_dvd m hm')
  exact dvd_trans hm (sub_dvd_pow_sub_pow _ _ _)

/-- Evaluating an introspective congruence at an `r`-th root of unity. -/
theorem Intro.aeval {F : Type*} [CommRing F] [Algebra (ZMod p) F] {ζ : F} (hζ : ζ ^ r = 1)
    {m : ℕ} {f : (ZMod p)[X]} (h : Intro p r m f) :
    (Polynomial.aeval ζ f) ^ m = Polynomial.aeval (ζ ^ m) f := by
  obtain ⟨c, hc⟩ := h
  have h0 : Polynomial.aeval ζ ((X : (ZMod p)[X]) ^ r - 1) = 0 := by
    simp [hζ]
  have hexp : Polynomial.aeval ζ (expand (ZMod p) m f) = Polynomial.aeval (ζ ^ m) f := by
    simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_expand,
      Polynomial.expand_eval]
  have := congrArg (Polynomial.aeval ζ) hc
  simp only [map_sub, map_mul, map_pow, h0, zero_mul, hexp] at this
  linear_combination this

end AKS

/-
An instrumented (step-counting) version of the AKS algorithm.

Every function below returns, besides its value, a count of the primitive operations performed.
The counting is *derived*: each instrumented function is a structural copy of the corresponding
function of `RequestProject.AKS.Algorithm`, carrying an extra counter, and we prove that its value
component is literally the value computed by the original function.  Only the *leaf* primitives
are assigned a cost by fiat (a primitive cannot have its cost derived):

* a cyclic convolution `cmul` of two coefficient vectors of length `r` costs `r * r`
  (one coefficient multiplication in `ZMod n` per pair of coefficients);
* an addition `cadd` of two such vectors, and a test of equality between two such vectors,
  cost `r` each;
* one step of the search for `r` (computing `ordMod n r`) costs `r`;
* one `Nat.gcd a n` costs `bits n`;
* the perfect-power test costs `(bits n) ^ 4`;
* every iteration of a loop costs one extra unit of bookkeeping.

All costs are therefore measured in arithmetic operations on numbers of `O(log n)` bits.
-/
import Mathlib
import RequestProject.AKS.Algorithm

open Polynomial

namespace AKS

/-! ### Bit lengths -/

theorem bits_div_two_succ_le {m : ℕ} (hm : m ≠ 0) : bits (m / 2) + 1 ≤ bits m := by
  have h1 : m < 2 ^ bits m := lt_two_pow_bits m
  have hpos : 1 ≤ bits m := by
    rcases Nat.eq_zero_or_pos (bits m) with h | h
    · rw [h] at h1; omega
    · exact h
  obtain ⟨k, hk⟩ : ∃ k, bits m = k + 1 := ⟨bits m - 1, by omega⟩
  have h2 : m / 2 < 2 ^ k := by
    rw [hk, pow_succ] at h1
    omega
  have h3 : bits (m / 2) ≤ k := Nat.size_le.mpr h2
  omega

/-! ### Generic instrumented loops -/

/-- An instrumented `List.all`: no early exit, so the cost is an upper bound for the
short-circuiting version. -/
def allI (f : ℕ → Bool × ℕ) : List ℕ → Bool × ℕ
  | [] => (true, 0)
  | a :: l =>
      let x := f a
      let y := allI f l
      (x.1 && y.1, x.2 + y.2 + 1)

theorem allI_fst (f : ℕ → Bool × ℕ) (l : List ℕ) :
    (allI f l).1 = l.all (fun a => (f a).1) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [allI, ih]

theorem allI_snd_le (f : ℕ → Bool × ℕ) (B : ℕ) :
    ∀ l : List ℕ, (∀ a ∈ l, (f a).2 ≤ B) → (allI f l).2 ≤ l.length * (B + 1) := by
  intro l
  induction l with
  | nil => intro _; simp [allI]
  | cons a l ih =>
      intro h
      have h1 : (f a).2 ≤ B := h a (by simp)
      have h2 : (allI f l).2 ≤ l.length * (B + 1) :=
        ih (fun b hb => h b (by simp [hb]))
      simp only [allI, List.length_cons]
      have : (f a).2 + (allI f l).2 + 1 ≤ B + l.length * (B + 1) + 1 := by omega
      calc (f a).2 + (allI f l).2 + 1 ≤ B + l.length * (B + 1) + 1 := this
        _ = (l.length + 1) * (B + 1) := by ring

/-! ### Instrumented exponentiation in the quotient ring -/

variable {n r : ℕ}

/-- Instrumented repeated squaring. -/
def cpowI [NeZero r] (f : Vec n r) (m : ℕ) : Vec n r × ℕ :=
  if m = 0 then (cone n, 0)
  else
    let t := cpowI f (m / 2)
    let t2 : Vec n r × ℕ := (cmul t.1 t.1, t.2 + r * r)
    if m % 2 = 1 then (cmul t2.1 f, t2.2 + r * r) else t2
  termination_by m
  decreasing_by omega

theorem cpowI_fst [NeZero r] (f : Vec n r) (m : ℕ) : (cpowI f m).1 = cpow f m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [cpowI, cpow]
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, if_false]
      have hh := ih (m / 2) (by omega)
      by_cases hpar : m % 2 = 1 <;> simp [hpar, hh]

theorem cpowI_snd_le [NeZero r] (f : Vec n r) (m : ℕ) :
    (cpowI f m).2 ≤ 2 * bits m * (r * r) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [cpowI]
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, if_false]
      have hh := ih (m / 2) (by omega)
      have hb := bits_div_two_succ_le hm
      have hmono : 2 * bits (m / 2) * (r * r) + 2 * (r * r) ≤ 2 * bits m * (r * r) := by
        have : (2 * bits (m / 2) + 2) * (r * r) ≤ (2 * bits m) * (r * r) :=
          Nat.mul_le_mul_right _ (by omega)
        calc 2 * bits (m / 2) * (r * r) + 2 * (r * r)
            = (2 * bits (m / 2) + 2) * (r * r) := by ring
          _ ≤ (2 * bits m) * (r * r) := this
      by_cases hpar : m % 2 = 1 <;> simp only [hpar, if_true, if_false] <;> omega

/-! ### Instrumented polynomial congruence test -/

/-- Instrumented version of `polyTestC`. -/
def polyTestCI (n r : ℕ) [NeZero r] (a : ℕ) : Bool × ℕ :=
  let p := cpowI (cadd (cmonomial (r := r) n 1) (cconst (r := r) n (a : ZMod n))) n
  (decide (p.1 = cadd (cmonomial (r := r) n n) (cconst (r := r) n (a : ZMod n))), p.2 + 3 * r)

/-- Instrumented version of `polyTest`. -/
def polyTestI (n r a : ℕ) : Bool × ℕ :=
  match r with
  | 0 => (false, 0)
  | r' + 1 => polyTestCI n (r' + 1) a

theorem polyTestI_fst (n r a : ℕ) : (polyTestI n r a).1 = polyTest n r a := by
  match r with
  | 0 => rfl
  | r' + 1 =>
      haveI : NeZero (r' + 1) := ⟨by omega⟩
      rw [polyTestI, polyTest, polyTestC, polyTestCI, cpowI_fst]

theorem polyTestI_snd_le (n r a : ℕ) :
    (polyTestI n r a).2 ≤ 2 * bits n * (r * r) + 3 * r := by
  match r with
  | 0 => simp [polyTestI]
  | r' + 1 =>
      haveI : NeZero (r' + 1) := ⟨by omega⟩
      rw [polyTestI, polyTestCI]
      have := cpowI_snd_le (r := r' + 1)
        (cadd (cmonomial (r := r' + 1) n 1) (cconst (r := r' + 1) n (a : ZMod n))) n
      simpa using Nat.add_le_add_right this (3 * (r' + 1))

/-! ### Instrumented search for `r` -/

/-- Instrumented version of `rSearchAux`. -/
def rSearchAuxI (n : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, r => (r, 0)
  | fuel + 1, r =>
      if thr n < ordMod n r then (r, r + 1)
      else
        let t := rSearchAuxI n fuel (r + 1)
        (t.1, t.2 + r + 1)

theorem rSearchAuxI_fst (n : ℕ) : ∀ (fuel r : ℕ), (rSearchAuxI n fuel r).1 = rSearchAux n fuel r := by
  intro fuel
  induction fuel with
  | zero => intro r; rfl
  | succ fuel ih =>
      intro r
      rw [rSearchAuxI, rSearchAux]
      by_cases h : thr n < ordMod n r
      · simp [h]
      · simp [h, ih]

theorem rSearchAuxI_snd_le (n : ℕ) :
    ∀ (fuel r B : ℕ), r + fuel ≤ B → (rSearchAuxI n fuel r).2 ≤ fuel * (B + 1) + B + 1 := by
  intro fuel
  induction fuel with
  | zero => intro r B _; simp [rSearchAuxI]
  | succ fuel ih =>
      intro r B hB
      rw [rSearchAuxI]
      by_cases h : thr n < ordMod n r
      · simp only [h, if_true]
        have : r ≤ B := by omega
        calc r + 1 ≤ B + 1 := by omega
          _ ≤ (fuel + 1) * (B + 1) + B + 1 := by nlinarith
      · simp only [h, if_false]
        have hrec := ih (r + 1) B (by omega)
        have hrB : r ≤ B := by omega
        calc (rSearchAuxI n fuel (r + 1)).2 + r + 1
            ≤ (fuel * (B + 1) + B + 1) + B + 1 := by omega
          _ ≤ (fuel + 1) * (B + 1) + B + 1 := by nlinarith

/-- Instrumented version of `rAlg`. -/
def rAlgI (n : ℕ) : ℕ × ℕ := rSearchAuxI n (2 * (bits n) ^ 12 + 1) 1

theorem rAlgI_fst (n : ℕ) : (rAlgI n).1 = rAlg n := rSearchAuxI_fst n _ 1

theorem rAlgI_snd_le (n : ℕ) :
    (rAlgI n).2 ≤ (2 * (bits n) ^ 12 + 1) * (2 * (bits n) ^ 12 + 3) + 2 * (bits n) ^ 12 + 3 :=
  rSearchAuxI_snd_le n _ 1 (2 * (bits n) ^ 12 + 2) (by omega)

/-! ### The instrumented algorithm -/

/-- The AKS test, instrumented with a count of the primitive operations it performs. -/
def aksI (n : ℕ) : Bool × ℕ :=
  let R := rAlgI n
  let g := allI (fun a => (a == 0 || Nat.gcd a n == 1 || Nat.gcd a n == n, bits n))
    (List.range (R.1 + 1))
  let l : Bool × ℕ :=
    if n ≤ R.1 then (true, 1)
    else allI (fun a => if a = 0 then (true, 1) else polyTestI n R.1 a)
      (List.range (ellAlg n + 1))
  (2 ≤ n && !isPerfectPower n && g.1 && l.1,
    R.2 + (bits n) ^ 4 + g.2 + l.2 + 1)

theorem aksI_fst (n : ℕ) : (aksI n).1 = aksBool n := by
  rw [aksI, aksBool]
  simp only [rAlgI_fst, allI_fst]
  congr 1
  by_cases h : n ≤ rAlg n
  · simp [h]
  · have hf : (fun a => (if a = 0 then ((true : Bool), 1) else polyTestI n (rAlg n) a).1)
        = (fun a => (a == 0 || polyTest n (rAlg n) a)) := by
      funext a
      by_cases ha : a = 0
      · simp [ha]
      · simp [ha, polyTestI_fst]
    simp only [h, if_false, allI_fst, hf]
    simp

/-! ### The cost is polynomial in the bit length -/

theorem cost_step {k c d e m : ℕ} (hk : 2 ≤ k) (hc : c ≤ 2 ^ d) (hm : d + e ≤ m) :
    c * k ^ e ≤ k ^ m := by
  calc c * k ^ e ≤ 2 ^ d * k ^ e := Nat.mul_le_mul_right _ hc
    _ ≤ k ^ d * k ^ e := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hk d)
    _ = k ^ (d + e) := (pow_add k d e).symm
    _ ≤ k ^ m := Nat.pow_le_pow_right (by omega) hm

theorem aksI_snd_le {n : ℕ} (hn : 2 ≤ n) : (aksI n).2 ≤ bits n ^ 45 := by
  set k := bits n with hkdef
  have hk : 2 ≤ k := two_le_bits hn
  have hk1 : 1 ≤ k := by omega
  have hpow : ∀ e : ℕ, 1 ≤ k ^ e := fun e => Nat.one_le_pow _ _ (by omega)
  have hr : rAlg n ≤ 2 * k ^ 12 := by rw [rAlg_eq hn]; exact rOf_le n hn
  have hell : ellAlg n ≤ 4 * k ^ 7 + 2 := ellAlg_le hn
  -- the search for `r`
  have hR2 : (rAlgI n).2 ≤ k ^ 30 := by
    refine le_trans (rAlgI_snd_le n) ?_
    have h1 : (2 * k ^ 12 + 1) * (2 * k ^ 12 + 3) ≤ (4 * k ^ 12) * (8 * k ^ 12) := by
      have := hpow 12
      exact Nat.mul_le_mul (by omega) (by omega)
    have h2 : (4 * k ^ 12) * (8 * k ^ 12) = 32 * k ^ 24 := by ring
    have h3 : 2 * k ^ 12 + 3 ≤ 8 * k ^ 24 := by
      have h4 : k ^ 12 ≤ k ^ 24 := Nat.pow_le_pow_right hk1 (by omega)
      have := hpow 24
      omega
    calc (2 * k ^ 12 + 1) * (2 * k ^ 12 + 3) + 2 * k ^ 12 + 3
        ≤ 32 * k ^ 24 + 8 * k ^ 24 := by omega
      _ = 40 * k ^ 24 := by ring
      _ ≤ k ^ 30 := cost_step (d := 6) hk (by norm_num) (by omega)
  -- the gcd loop
  have hg2 : (allI (fun a => (a == 0 || Nat.gcd a n == 1 || Nat.gcd a n == n, k))
      (List.range (rAlg n + 1))).2 ≤ k ^ 16 := by
    refine le_trans (allI_snd_le _ k _ (fun a _ => le_rfl)) ?_
    rw [List.length_range]
    have h1 : (rAlg n + 1) * (k + 1) ≤ (4 * k ^ 12) * (2 * k ^ 1) := by
      have := hpow 12
      refine Nat.mul_le_mul (by omega) (by simp; omega)
    calc (rAlg n + 1) * (k + 1) ≤ (4 * k ^ 12) * (2 * k ^ 1) := h1
      _ = 8 * k ^ 13 := by ring
      _ ≤ k ^ 16 := cost_step (d := 3) hk (by norm_num) (by omega)
  -- the loop over the polynomial congruences
  have hl2 : (allI (fun a => if a = 0 then ((true : Bool), 1) else polyTestI n (rAlg n) a)
      (List.range (ellAlg n + 1))).2 ≤ k ^ 40 := by
    set B : ℕ := 16 * k ^ 25 with hB
    have hbound : ∀ a ∈ List.range (ellAlg n + 1),
        (if a = 0 then ((true : Bool), 1) else polyTestI n (rAlg n) a).2 ≤ B := by
      intro a _
      by_cases ha : a = 0
      · simp only [ha, if_pos]
        have := hpow 25
        omega
      · simp only [ha, if_false]
        refine le_trans (polyTestI_snd_le n (rAlg n) a) ?_
        rw [← hkdef]
        have hrr : rAlg n * rAlg n ≤ (2 * k ^ 12) * (2 * k ^ 12) := Nat.mul_le_mul hr hr
        have hrr2 : rAlg n * rAlg n ≤ 4 * k ^ 24 := by
          calc rAlg n * rAlg n ≤ (2 * k ^ 12) * (2 * k ^ 12) := hrr
            _ = 4 * k ^ 24 := by ring
        have h1 : 2 * k * (rAlg n * rAlg n) ≤ 2 * k * (4 * k ^ 24) :=
          Nat.mul_le_mul_left _ hrr2
        have h2 : 2 * k * (4 * k ^ 24) = 8 * k ^ 25 := by ring
        have h3 : 3 * rAlg n ≤ 6 * k ^ 12 := by omega
        have h4 : k ^ 12 ≤ k ^ 25 := Nat.pow_le_pow_right hk1 (by omega)
        omega
    refine le_trans (allI_snd_le _ B _ hbound) ?_
    rw [List.length_range]
    have h1 : (ellAlg n + 1) * (B + 1) ≤ (8 * k ^ 7) * (32 * k ^ 25) := by
      have h7 := hpow 7
      have h25 := hpow 25
      refine Nat.mul_le_mul (by omega) (by omega)
    calc (ellAlg n + 1) * (B + 1) ≤ (8 * k ^ 7) * (32 * k ^ 25) := h1
      _ = 256 * k ^ 32 := by ring
      _ ≤ k ^ 40 := cost_step (d := 8) hk (by norm_num) (by omega)
  have hlast : (if n ≤ rAlg n then ((true : Bool), 1)
      else allI (fun a => if a = 0 then ((true : Bool), 1) else polyTestI n (rAlg n) a)
        (List.range (ellAlg n + 1))).2 ≤ k ^ 40 := by
    by_cases h : n ≤ rAlg n
    · simpa [h] using hpow 40
    · simpa [h] using hl2
  have hk4 : k ^ 4 ≤ k ^ 40 := Nat.pow_le_pow_right hk1 (by omega)
  have hk30 : k ^ 30 ≤ k ^ 40 := Nat.pow_le_pow_right hk1 (by omega)
  have hk16 : k ^ 16 ≤ k ^ 40 := Nat.pow_le_pow_right hk1 (by omega)
  have hfin : 8 * k ^ 40 ≤ k ^ 45 := cost_step (d := 3) hk (by norm_num) (by omega)
  have hexp : (aksI n).2 = (rAlgI n).2 + k ^ 4
      + (allI (fun a => (a == 0 || Nat.gcd a n == 1 || Nat.gcd a n == n, k))
          (List.range (rAlg n + 1))).2
      + (if n ≤ rAlg n then ((true : Bool), 1)
          else allI (fun a => if a = 0 then ((true : Bool), 1) else polyTestI n (rAlg n) a)
            (List.range (ellAlg n + 1))).2 + 1 := by
    rw [aksI]
    simp only [rAlgI_fst, hkdef]
  rw [hexp]
  have h39 := hpow 40
  omega

end AKS

