import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/
lemma centralBinom_sq_le (m : ℕ) : (Nat.centralBinom m) ^ 2 * (m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp [Nat.centralBinom]
  | succ m ih =>
      have hrec : (m + 1) * (m + 1).centralBinom = 2 * (2 * m + 1) * m.centralBinom :=
        Nat.succ_mul_centralBinom_succ m
      -- multiply the goal by `(m+1)^3`
      have key : ((m + 1) * (m + 1).centralBinom) ^ 2 * (m + 2) * (m + 1)
          ≤ 16 ^ (m + 1) * (m + 1) ^ 3 := by
        rw [hrec]
        have h1 : (2 * (2 * m + 1) * m.centralBinom) ^ 2 * (m + 2) * (m + 1)
            = (4 * (2 * m + 1) ^ 2 * (m + 2)) * ((m.centralBinom ^ 2) * (m + 1)) := by ring
        rw [h1]
        have h2 : (4 * (2 * m + 1) ^ 2 * (m + 2)) * ((m.centralBinom ^ 2) * (m + 1))
            ≤ (4 * (2 * m + 1) ^ 2 * (m + 2)) * 16 ^ m := Nat.mul_le_mul_left _ ih
        refine h2.trans ?_
        have h3 : 4 * (2 * m + 1) ^ 2 * (m + 2) ≤ 16 * (m + 1) ^ 3 := by nlinarith
        calc (4 * (2 * m + 1) ^ 2 * (m + 2)) * 16 ^ m
            ≤ (16 * (m + 1) ^ 3) * 16 ^ m := Nat.mul_le_mul_right _ h3
          _ = 16 ^ (m + 1) * (m + 1) ^ 3 := by ring
      have hpos : 0 < (m + 1) ^ 2 := by positivity
      have : ((m + 1).centralBinom ^ 2 * (m + 2)) * (m + 1) ^ 3
          ≤ 16 ^ (m + 1) * (m + 1) ^ 3 := by
        calc ((m + 1).centralBinom ^ 2 * (m + 2)) * (m + 1) ^ 3
            = ((m + 1) * (m + 1).centralBinom) ^ 2 * (m + 2) * (m + 1) := by ring
          _ ≤ 16 ^ (m + 1) * (m + 1) ^ 3 := key
      have h4 : 0 < (m + 1) ^ 3 := by positivity
      exact Nat.le_of_mul_le_mul_right this h4

lemma choose_two_mul_succ_le (m : ℕ) : (2 * m + 1).choose m ≤ 2 * Nat.centralBinom m := by
  cases m with
  | zero => simp [Nat.centralBinom]
  | succ j =>
      have h : (2 * (j + 1) + 1).choose (j + 1) = (2 * (j + 1)).choose j
          + (2 * (j + 1)).choose (j + 1) := by
        have : 2 * (j + 1) + 1 = (2 * (j + 1)) + 1 := rfl
        rw [this, Nat.choose_succ_succ]
      rw [h]
      have hmid : (2 * (j + 1)).choose j ≤ (2 * (j + 1)).choose (j + 1) := by
        have := Nat.choose_le_middle j (2 * (j + 1))
        simpa [Nat.mul_div_cancel_left] using this
      have hcb : (2 * (j + 1)).choose (j + 1) = Nat.centralBinom (j + 1) := by
        rw [Nat.centralBinom]
      omega

/-- The sum of the first `m + D + 1` binomial coefficients `C(2m+1, i)`. -/
lemma sum_choose_le (m D : ℕ) :
    ∑ i ∈ range (m + D + 1), (2 * m + 1).choose i ≤ 4 ^ m + D * ((2 * m + 1).choose m) := by
  have hsplit : range (m + D + 1) = range (m + 1) ∪ Ico (m + 1) (m + D + 1) := by
    rw [Finset.range_eq_Ico]
    exact (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
  have hdisj : Disjoint (range (m + 1)) (Ico (m + 1) (m + D + 1)) := by
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive 0 (m + 1) (m + D + 1)
  rw [hsplit, Finset.sum_union hdisj, Nat.sum_range_choose_halfway]
  have hbound : ∀ i ∈ Ico (m + 1) (m + D + 1), (2 * m + 1).choose i ≤ (2 * m + 1).choose m := by
    intro i _
    have h := Nat.choose_le_middle i (2 * m + 1)
    have h2 : (2 * m + 1) / 2 = m := by omega
    rwa [h2] at h
  have := Finset.sum_le_card_nsmul (Ico (m + 1) (m + D + 1))
    (fun i => (2 * m + 1).choose i) ((2 * m + 1).choose m) hbound
  simp only [Nat.card_Ico, smul_eq_mul] at this
  have hc : m + D + 1 - (m + 1) = D := by omega
  rw [hc] at this
  omega

/-- The key numerical consequence of the central binomial estimate. -/
lemma choose_mul_lt {m D : ℕ} (h9 : 9 * D ^ 2 ≤ m) :
    3 * (D * ((2 * m + 1).choose m)) < 2 * 4 ^ m := by
  have hch : (2 * m + 1).choose m ≤ 2 * Nat.centralBinom m := choose_two_mul_succ_le m
  have hcb : (Nat.centralBinom m) ^ 2 * (m + 1) ≤ 16 ^ m := centralBinom_sq_le m
  have h16 : 0 < (16 : ℕ) ^ m := by positivity
  have hsq : (3 * (D * ((2 * m + 1).choose m))) ^ 2 < (2 * 4 ^ m) ^ 2 := by
    have h1 : (3 * (D * ((2 * m + 1).choose m))) ^ 2
        ≤ 9 * D ^ 2 * (4 * (Nat.centralBinom m) ^ 2) := by
      have h2 : ((2 * m + 1).choose m) ^ 2 ≤ 4 * (Nat.centralBinom m) ^ 2 := by
        calc ((2 * m + 1).choose m) ^ 2 ≤ (2 * Nat.centralBinom m) ^ 2 :=
              Nat.pow_le_pow_left hch 2
          _ = 4 * (Nat.centralBinom m) ^ 2 := by ring
      calc (3 * (D * ((2 * m + 1).choose m))) ^ 2
          = 9 * D ^ 2 * ((2 * m + 1).choose m) ^ 2 := by ring
        _ ≤ 9 * D ^ 2 * (4 * (Nat.centralBinom m) ^ 2) := Nat.mul_le_mul_left _ h2
    have h3 : (9 * D ^ 2 * (4 * (Nat.centralBinom m) ^ 2)) * (m + 1) ≤ 4 * m * 16 ^ m := by
      calc (9 * D ^ 2 * (4 * (Nat.centralBinom m) ^ 2)) * (m + 1)
          = (4 * (9 * D ^ 2)) * ((Nat.centralBinom m) ^ 2 * (m + 1)) := by ring
        _ ≤ (4 * (9 * D ^ 2)) * 16 ^ m := Nat.mul_le_mul_left _ hcb
        _ ≤ (4 * m) * 16 ^ m := Nat.mul_le_mul_right _ (by omega)
    have h4 : (2 * 4 ^ m) ^ 2 * (m + 1) = 4 * (m + 1) * 16 ^ m := by
      have h5 : (4 : ℕ) ^ m * 4 ^ m = 16 ^ m := by
        rw [← mul_pow]; norm_num
      calc (2 * 4 ^ m) ^ 2 * (m + 1) = 4 * (m + 1) * (4 ^ m * 4 ^ m) := by ring
        _ = 4 * (m + 1) * 16 ^ m := by rw [h5]
    have h5 : (3 * (D * ((2 * m + 1).choose m))) ^ 2 * (m + 1) < (2 * 4 ^ m) ^ 2 * (m + 1) := by
      calc (3 * (D * ((2 * m + 1).choose m))) ^ 2 * (m + 1)
          ≤ (9 * D ^ 2 * (4 * (Nat.centralBinom m) ^ 2)) * (m + 1) := Nat.mul_le_mul_right _ h1
        _ ≤ 4 * m * 16 ^ m := h3
        _ < 4 * (m + 1) * 16 ^ m := by
            have h6 : 4 * m < 4 * (m + 1) := by omega
            exact (Nat.mul_lt_mul_right h16).2 h6
        _ = (2 * 4 ^ m) ^ 2 * (m + 1) := h4.symm
    exact lt_of_mul_lt_mul_right h5 (Nat.zero_le _)
  exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hsq

/-- The final counting contradiction. -/
lemma final_arith {X Y P : ℕ} (h1 : 4 * P ≤ X) (h2 : 3 * Y < 2 * X)
    (h3 : 2 * X ≤ X + Y + P) : False := by omega

/-- Counting subsets of `Fin n` of size at most `D`. -/
lemma card_filter_card_le (n D : ℕ) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D)).card
      = ∑ i ∈ range (D + 1), n.choose i := by
  classical
  have hEq : ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D))
      = (range (D + 1)).biUnion (fun i => Finset.powersetCard i Finset.univ) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · intro h; exact ⟨S.card, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩; omega
  rw [hEq, Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.card_powersetCard]
    simp
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_powersetCard]
    rintro S ⟨-, rfl⟩ ⟨-, h⟩
    exact hij h

end CS

import Mathlib

/-!
# Auxiliary lemmas

* an elementary growth estimate: `K * t ^ e ≤ 2 ^ t` for suitable arbitrarily large `t`;
* the existence of a finite field of characteristic `q` containing a nontrivial `p`-th root
  of unity, for distinct primes `p` and `q`.
-/

namespace CS

lemma sq_le_two_pow {u : ℕ} (hu : 4 ≤ u) : u ^ 2 ≤ 2 ^ u := by
  induction u with
  | zero => omega
  | succ v ih =>
      rcases Nat.lt_or_ge v 4 with hv | hv
      · interval_cases v <;> simp_all
      · have h1 : v ^ 2 ≤ 2 ^ v := ih (by omega)
        have h2 : 2 * v + 1 ≤ v ^ 2 := by nlinarith
        have : (v + 1) ^ 2 = v ^ 2 + (2 * v + 1) := by ring
        calc (v + 1) ^ 2 = v ^ 2 + (2 * v + 1) := this
          _ ≤ 2 ^ v + 2 ^ v := Nat.add_le_add h1 (le_trans h2 h1)
          _ = 2 ^ (v + 1) := by ring

/-- Exponentials beat polynomials: there are arbitrarily large `t` with `K * t ^ e ≤ 2 ^ t`. -/
lemma exists_large_pow_le (K e t₀ : ℕ) (he : 1 ≤ e) : ∃ t, t₀ ≤ t ∧ K * t ^ e ≤ 2 ^ t := by
  set u := K + e + 4 + t₀ with hu
  refine ⟨e * u + K, ?_, ?_⟩
  · calc t₀ ≤ u := by omega
      _ ≤ e * u := Nat.le_mul_of_pos_left u he
      _ ≤ e * u + K := Nat.le_add_right _ _
  · have h1 : e * u + K ≤ (e + 1) * u := by
      have : K ≤ u := by omega
      nlinarith
    have h2 : (e + 1) * u ≤ 2 ^ u := by
      have h3 : (e + 1) * u ≤ u * u := Nat.mul_le_mul_right u (by omega)
      have h4 : u * u = u ^ 2 := by ring
      exact le_trans h3 (h4 ▸ sq_le_two_pow (by omega))
    have h5 : (e * u + K) ^ e ≤ 2 ^ (u * e) := by
      calc (e * u + K) ^ e ≤ ((e + 1) * u) ^ e := Nat.pow_le_pow_left h1 e
        _ ≤ (2 ^ u) ^ e := Nat.pow_le_pow_left h2 e
        _ = 2 ^ (u * e) := by rw [← pow_mul]
    have h6 : K ≤ 2 ^ K := Nat.le_of_lt Nat.lt_two_pow_self
    calc K * (e * u + K) ^ e ≤ 2 ^ K * 2 ^ (u * e) := Nat.mul_le_mul h6 h5
      _ = 2 ^ (e * u + K) := by rw [← pow_add]; ring_nf

/-- Choice of the parameters in the Razborov–Smolensky argument: a number of inputs
`n = 2m+1` and a number `l` of random subsets such that the approximation error is small
and the resulting degree `((q-1) l) ^ d` is at most `√m / 3`. -/
lemma exists_params (p q d c : ℕ) (hp : 2 ≤ p) (hd : 1 ≤ d) (hc : 1 ≤ c) :
    ∃ t l m : ℕ, 1 ≤ l ∧ m = 2 ^ t ∧
      (∀ k : ℕ, k ≤ c * (2 * m + 1 + p + 1) ^ c → 8 * p * k * 2 ^ p ≤ 2 ^ l) ∧
      9 * (((q - 1) * l) ^ d) ^ 2 ≤ m := by
  set A := 8 * p * 2 ^ p * c with hA
  set Bc := (q - 1) * (A + 4 * c) with hBc
  obtain ⟨t, ht0, htbig⟩ := exists_large_pow_le (9 * Bc ^ (2 * d)) (2 * d) (p + 4) (by omega)
  have hct : 1 ≤ c * (t + 3) := by
    have : 1 * 1 ≤ c * (t + 3) := Nat.mul_le_mul hc (by omega)
    omega
  refine ⟨t, A + c * (t + 3), 2 ^ t, by omega, rfl, ?_, ?_⟩
  · intro k hk
    have hNb : 2 * 2 ^ t + 1 + p + 1 ≤ 2 ^ (t + 2) := by
      have h1 : t + 1 < 2 ^ (t + 1) := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ (t + 2) = 2 ^ (t + 1) + 2 ^ (t + 1) := by ring
      have h3 : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
      omega
    have hkb : k ≤ c * 2 ^ (c * (t + 2)) := by
      refine le_trans hk ?_
      have h2 : (2 * 2 ^ t + 1 + p + 1) ^ c ≤ (2 ^ (t + 2)) ^ c := Nat.pow_le_pow_left hNb c
      calc c * (2 * 2 ^ t + 1 + p + 1) ^ c ≤ c * (2 ^ (t + 2)) ^ c := Nat.mul_le_mul_left _ h2
        _ = c * 2 ^ (c * (t + 2)) := by rw [← pow_mul, mul_comm (t + 2) c]
    calc 8 * p * k * 2 ^ p ≤ 8 * p * (c * 2 ^ (c * (t + 2))) * 2 ^ p :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hkb)
      _ = A * 2 ^ (c * (t + 2)) := by rw [hA]; ring
      _ ≤ 2 ^ A * 2 ^ (c * (t + 2)) := Nat.mul_le_mul_right _ (Nat.le_of_lt Nat.lt_two_pow_self)
      _ = 2 ^ (A + c * (t + 2)) := by rw [← pow_add]
      _ ≤ 2 ^ (A + c * (t + 3)) := by
          refine Nat.pow_le_pow_right (by omega) ?_
          have : c * (t + 2) ≤ c * (t + 3) := Nat.mul_le_mul_left _ (by omega)
          omega
  · have h1 : (q - 1) * (A + c * (t + 3)) ≤ Bc * t := by
      have h2 : A + c * (t + 3) ≤ (A + 4 * c) * t := by nlinarith [ht0]
      calc (q - 1) * (A + c * (t + 3)) ≤ (q - 1) * ((A + 4 * c) * t) :=
            Nat.mul_le_mul_left _ h2
        _ = Bc * t := by rw [hBc]; ring
    have h2 : ((q - 1) * (A + c * (t + 3))) ^ d ≤ Bc ^ d * t ^ d := by
      calc ((q - 1) * (A + c * (t + 3))) ^ d ≤ (Bc * t) ^ d := Nat.pow_le_pow_left h1 d
        _ = Bc ^ d * t ^ d := by rw [mul_pow]
    calc 9 * (((q - 1) * (A + c * (t + 3))) ^ d) ^ 2 ≤ 9 * (Bc ^ d * t ^ d) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 2)
      _ = 9 * Bc ^ (2 * d) * t ^ (2 * d) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm d 2, mul_assoc]
      _ ≤ 2 ^ t := htbig

/-- For distinct primes `p` and `q` there is a finite field of characteristic `q` containing a
`p`-th root of unity different from `1`. -/
lemma exists_root_of_unity (p q : ℕ) [hqf : Fact q.Prime] (hp : p.Prime) (hpq : p ≠ q) :
    ∃ ζ : GaloisField q (p - 1), ζ ^ p = 1 ∧ ζ ≠ 1 := by
  have hq : q.Prime := hqf.out
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  haveI : Fintype (GaloisField q (p - 1)) := Fintype.ofFinite _
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hcard : Nat.card (GaloisField q (p - 1)) = q ^ (p - 1) := GaloisField.card q (p - 1) hp1
  have hcop : Nat.Coprime q p := (Nat.coprime_primes hq hp).2 (Ne.symm hpq)
  have hmod : q ^ (p - 1) ≡ 1 [MOD p] := by
    have h := Nat.ModEq.pow_totient hcop
    rwa [Nat.totient_prime hp] at h
  have hdvd : p ∣ q ^ (p - 1) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq.pos)).mp hmod.symm
  have hunits : Fintype.card (GaloisField q (p - 1))ˣ = q ^ (p - 1) - 1 := by
    have h1 : Nat.card (GaloisField q (p - 1))ˣ = Nat.card (GaloisField q (p - 1)) - 1 :=
      Nat.card_units _
    rw [Nat.card_eq_fintype_card] at h1
    rw [h1, hcard]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (GaloisField q (p - 1))ˣ) p
    (by rw [hunits]; exact hdvd)
  refine ⟨(u : GaloisField q (p - 1)), ?_, ?_⟩
  · have h : u ^ p = 1 := by
      have h0 := pow_orderOf_eq_one u
      rwa [hu] at h0
    have := congrArg (Units.val (α := GaloisField q (p - 1))) h
    simpa using this
  · intro h
    have h1 : u = 1 := Units.ext h
    rw [h1, orderOf_one] at hu
    exact hp.one_lt.ne hu

end CS

import RequestProject.Deg
import RequestProject.Circuits

/-!
# Razborov's approximation of circuits by low degree polynomials

Every gate of a depth `d`, size `k` circuit with `MOD q` gates can be approximated over
`ZMod q` by a function of degree at most `((q-1) * l) ^ d`, with a common set of bad inputs
of size at most `k * 2 ^ n / 2 ^ l`.
-/

namespace CS

open Finset

section Field

variable {q : ℕ} [hq : Fact q.Prime]

/-- The `ZMod q`-value of a Boolean. -/
def bit (q : ℕ) (b : Bool) : ZMod q := if b then 1 else 0

/-- `Ez z = z ^ (q-1)` is the indicator of `z ≠ 0`. -/
def Ez (q : ℕ) (z : ZMod q) : ZMod q := z ^ (q - 1)

lemma Ez_zero : Ez q 0 = 0 := by
  have h : q - 1 ≠ 0 := by have := hq.out.two_le; omega
  simp [Ez, zero_pow h]

lemma Ez_of_ne_zero {z : ZMod q} (h : z ≠ 0) : Ez q z = 1 := ZMod.pow_card_sub_one_eq_one h

lemma Ez_eq_ite (z : ZMod q) : Ez q z = if z = 0 then 0 else 1 := by
  by_cases h : z = 0
  · simp [h, Ez_zero]
  · simp [h, Ez_of_ne_zero h]

/-- Half of the subsets of a set of field elements, not all zero, have nonzero sum. -/
lemma card_zero_sum_le {m : ℕ} (a : Fin m → ZMod q) {i₀ : Fin m} (h : a i₀ ≠ 0) :
    2 * ((Finset.univ : Finset (Finset (Fin m))).filter
      (fun S => ∑ i ∈ S, a i = 0)).card ≤ 2 ^ m := by
  classical
  set Z := (Finset.univ : Finset (Finset (Fin m))).filter (fun S => ∑ i ∈ S, a i = 0) with hZ
  set Z' := (Finset.univ : Finset (Finset (Fin m))).filter (fun S => ¬ (∑ i ∈ S, a i = 0))
    with hZ'
  have hsum : Z.card + Z'.card = 2 ^ m := by
    rw [hZ, hZ', Finset.card_filter_add_card_filter_not]
    simp
  have hmemZ : ∀ S : Finset (Fin m), S ∈ Z ↔ ∑ i ∈ S, a i = 0 := by
    intro S; rw [hZ, Finset.mem_filter]; simp
  have hmemZ' : ∀ S : Finset (Fin m), S ∈ Z' ↔ ¬ (∑ i ∈ S, a i = 0) := by
    intro S; rw [hZ', Finset.mem_filter]; simp
  have hle : Z.card ≤ Z'.card := by
    refine Finset.card_le_card_of_injOn
      (fun S => if i₀ ∈ S then S.erase i₀ else insert i₀ S) ?_ ?_
    · intro S hS
      have hS' : ∑ i ∈ S, a i = 0 := (hmemZ S).1 (by simpa using hS)
      have hgoal : (if i₀ ∈ S then S.erase i₀ else insert i₀ S) ∈ Z' := by
        rw [hmemZ']
        by_cases hi : i₀ ∈ S
        · rw [if_pos hi]
          intro hcon
          have h2 : ∑ i ∈ S, a i = a i₀ + ∑ i ∈ S.erase i₀, a i :=
            (Finset.add_sum_erase _ _ hi).symm
          rw [hS', hcon, add_zero] at h2
          exact h h2.symm
        · rw [if_neg hi, Finset.sum_insert hi, hS', add_zero]
          exact h
      simpa using hgoal
    · intro S _ T _ hST
      simp only at hST
      by_cases hiS : i₀ ∈ S <;> by_cases hiT : i₀ ∈ T
      · rw [if_pos hiS, if_pos hiT] at hST
        have h3 := congrArg (insert i₀) hST
        rwa [Finset.insert_erase hiS, Finset.insert_erase hiT] at h3
      · rw [if_pos hiS, if_neg hiT] at hST
        exfalso
        have h3 : i₀ ∈ insert i₀ T := Finset.mem_insert_self _ _
        rw [← hST] at h3
        exact (Finset.notMem_erase i₀ S) h3
      · rw [if_neg hiS, if_pos hiT] at hST
        exfalso
        have h3 : i₀ ∈ insert i₀ S := Finset.mem_insert_self _ _
        rw [hST] at h3
        exact (Finset.notMem_erase i₀ T) h3
      · rw [if_neg hiS, if_neg hiT] at hST
        have h1 : S = (insert i₀ S).erase i₀ := (Finset.erase_insert hiS).symm
        have h2 : T = (insert i₀ T).erase i₀ := (Finset.erase_insert hiT).symm
        rw [h1, h2, hST]
  omega

variable {n : ℕ}

/-- The value an `OR` gate should take. -/
noncomputable def orTarget {m : ℕ} (y : Fin m → Cube n → ZMod q) (x : Cube n) : ZMod q :=
  if ∀ i, y i x = 0 then 0 else 1

/-- Razborov's approximation of an `OR` gate by a low degree polynomial, for a given choice
of `l` subsets of the inputs. -/
noncomputable def orPoly {m l : ℕ} (y : Fin m → Cube n → ZMod q) (c : Fin l → Finset (Fin m)) :
    Cube n → ZMod q :=
  fun x => 1 - ∏ j : Fin l, (1 - Ez q (∑ i ∈ c j, y i x))

lemma orPoly_apply {m l : ℕ} (y : Fin m → Cube n → ZMod q) (c : Fin l → Finset (Fin m))
    (x : Cube n) :
    orPoly y c x = if ∀ j, ∑ i ∈ c j, y i x = 0 then 0 else 1 := by
  classical
  unfold orPoly
  by_cases h : ∀ j, ∑ i ∈ c j, y i x = 0
  · rw [if_pos h]
    have : ∀ j : Fin l, (1 - Ez q (∑ i ∈ c j, y i x)) = 1 := by
      intro j; rw [h j, Ez_zero, sub_zero]
    rw [Finset.prod_congr rfl (fun j _ => this j)]
    simp
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ j)]
    · simp
    · rw [Ez_of_ne_zero hj, sub_self]

lemma orPoly_mem_Deg {m l d : ℕ} (y : Fin m → Cube n → ZMod q) (c : Fin l → Finset (Fin m))
    (hy : ∀ i, y i ∈ Deg (ZMod q) n d) : orPoly y c ∈ Deg (ZMod q) n (l * ((q - 1) * d)) := by
  classical
  have hfun : orPoly y c
      = 1 - ∏ j : Fin l, (1 - (fun x => (∑ i ∈ c j, y i x) ^ (q - 1))) := by
    funext x
    simp only [orPoly, Ez, Pi.sub_apply, Pi.one_apply, Finset.prod_apply]
  rw [hfun]
  refine Submodule.sub_mem _ (one_mem_Deg _) ?_
  have hstep : ∀ j : Fin l,
      (1 - (fun x => (∑ i ∈ c j, y i x) ^ (q - 1)) : Cube n → ZMod q)
        ∈ Deg (ZMod q) n ((q - 1) * d) := by
    intro j
    refine Submodule.sub_mem _ (one_mem_Deg _) ?_
    have hsum : (fun x => ∑ i ∈ c j, y i x) ∈ Deg (ZMod q) n d := by
      have : (fun x => ∑ i ∈ c j, y i x) = ∑ i ∈ c j, y i := by
        funext x; simp [Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ (fun i _ => hy i)
    have hpow := pow_mem_Deg hsum (q - 1)
    have heq : (fun x => (∑ i ∈ c j, y i x) ^ (q - 1))
        = (fun x => ∑ i ∈ c j, y i x) ^ (q - 1) := by
      funext x; simp [Pi.pow_apply]
    rw [heq]
    exact hpow
  have := prod_mem_Deg (Finset.univ : Finset (Fin l))
    (fun j => (1 - (fun x => (∑ i ∈ c j, y i x) ^ (q - 1)) : Cube n → ZMod q))
    (fun _ => (q - 1) * d) (fun j _ => hstep j)
  simpa using this

/-- The number of choices for which a given input is badly approximated is small. -/
lemma card_bad_choices {m l : ℕ} (a : Fin m → ZMod q) :
    ((Finset.univ : Finset (Fin l → Finset (Fin m))).filter
        (fun c => (if ∀ j, ∑ i ∈ c j, a i = 0 then (0 : ZMod q) else 1)
          ≠ (if ∀ i, a i = 0 then (0 : ZMod q) else 1))).card * 2 ^ l ≤ (2 ^ m) ^ l := by
  classical
  by_cases hall : ∀ i, a i = 0
  · have hempty : ((Finset.univ : Finset (Fin l → Finset (Fin m))).filter
        (fun c => (if ∀ j, ∑ i ∈ c j, a i = 0 then (0 : ZMod q) else 1)
          ≠ (if ∀ i, a i = 0 then (0 : ZMod q) else 1))) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 ?_
      intro c _
      have h1 : ∀ j, ∑ i ∈ c j, a i = 0 := by
        intro j
        exact Finset.sum_eq_zero (fun i _ => hall i)
      simp [hall]
    rw [hempty]
    simp
  · push_neg at hall
    obtain ⟨i₀, hi₀⟩ := hall
    set Z := (Finset.univ : Finset (Finset (Fin m))).filter
      (fun S => ∑ i ∈ S, a i = 0) with hZ
    have hset : ((Finset.univ : Finset (Fin l → Finset (Fin m))).filter
        (fun c => (if ∀ j, ∑ i ∈ c j, a i = 0 then (0 : ZMod q) else 1)
          ≠ (if ∀ i, a i = 0 then (0 : ZMod q) else 1)))
        = Fintype.piFinset (fun _ : Fin l => Z) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, hZ]
      constructor
      · intro hc j
        by_contra hcon
        apply hc
        have hnot : ¬ (∀ j, ∑ i ∈ c j, a i = 0) := by
          intro hcc
          exact hcon (by simp [hcc j])
        rw [if_neg hnot, if_neg (by push_neg; exact ⟨i₀, hi₀⟩)]
      · intro hc
        have h1 : ∀ j, ∑ i ∈ c j, a i = 0 := by
          intro j
          have := hc j
          simpa using this
        rw [if_pos h1, if_neg (by push_neg; exact ⟨i₀, hi₀⟩)]
        exact zero_ne_one
    rw [hset, Fintype.card_piFinset]
    have hZcard : 2 * Z.card ≤ 2 ^ m := card_zero_sum_le a hi₀
    calc (∏ _j : Fin l, Z.card) * 2 ^ l = (2 * Z.card) ^ l := by
          rw [Finset.prod_const]
          simp [mul_pow, mul_comm]
      _ ≤ (2 ^ m) ^ l := Nat.pow_le_pow_left hZcard l

/-- There is a choice of subsets for which the `OR` approximation has few bad inputs. -/
lemma exists_or_choice {m : ℕ} (l : ℕ) (y : Fin m → Cube n → ZMod q) :
    ∃ c : Fin l → Finset (Fin m),
      ((Finset.univ : Finset (Cube n)).filter
        (fun x => orPoly y c x ≠ orTarget y x)).card * 2 ^ l ≤ 2 ^ n := by
  classical
  set Ch := (Finset.univ : Finset (Fin l → Finset (Fin m))) with hCh
  have hChcard : Ch.card = (2 ^ m) ^ l := by
    rw [hCh, Finset.card_univ]
    simp [Fintype.card_finset]
  have hChne : Ch.Nonempty := by
    rw [← Finset.card_pos, hChcard]
    positivity
  have hdouble : ∑ c ∈ Ch, (((Finset.univ : Finset (Cube n)).filter
      (fun x => orPoly y c x ≠ orTarget y x)).card * 2 ^ l) ≤ ∑ _c ∈ Ch, 2 ^ n := by
    have hswap : ∑ c ∈ Ch, ((Finset.univ : Finset (Cube n)).filter
        (fun x => orPoly y c x ≠ orTarget y x)).card
        = ∑ x : Cube n, (Ch.filter (fun c => orPoly y c x ≠ orTarget y x)).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    have hx : ∀ x : Cube n,
        (Ch.filter (fun c => orPoly y c x ≠ orTarget y x)).card * 2 ^ l ≤ (2 ^ m) ^ l := by
      intro x
      have := card_bad_choices (q := q) (l := l) (fun i => y i x)
      refine le_trans (le_of_eq ?_) this
      congr 2
      apply Finset.filter_congr
      intro c _
      rw [orPoly_apply, orTarget]
    calc ∑ c ∈ Ch, (((Finset.univ : Finset (Cube n)).filter
            (fun x => orPoly y c x ≠ orTarget y x)).card * 2 ^ l)
        = (∑ c ∈ Ch, ((Finset.univ : Finset (Cube n)).filter
            (fun x => orPoly y c x ≠ orTarget y x)).card) * 2 ^ l := by
          rw [Finset.sum_mul]
      _ = (∑ x : Cube n, (Ch.filter (fun c => orPoly y c x ≠ orTarget y x)).card) * 2 ^ l := by
          rw [hswap]
      _ = ∑ x : Cube n, ((Ch.filter (fun c => orPoly y c x ≠ orTarget y x)).card * 2 ^ l) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ _x : Cube n, (2 ^ m) ^ l := Finset.sum_le_sum (fun x _ => hx x)
      _ = 2 ^ n * (2 ^ m) ^ l := by
          rw [Finset.sum_const, Finset.card_univ]
          simp
      _ = ∑ _c ∈ Ch, 2 ^ n := by
          rw [Finset.sum_const, hChcard]
          simp [mul_comm]
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_sum_le hChne hdouble
  exact ⟨c, hc⟩

lemma bit_eq_zero_iff {b : Bool} : bit q b = 0 ↔ b = false := by
  cases b <;> simp [bit]

lemma bit_not (b : Bool) : bit q (!b) = 1 - bit q b := by
  cases b <;> simp [bit]

lemma sum_bit_countP {α : Type*} (w : α → Bool) (L : List α) :
    (L.map (fun j => bit q (w j))).sum = ((L.countP w : ℕ) : ZMod q) := by
  induction L with
  | nil => simp [bit]
  | cons a L ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      cases w a <;> simp [bit]
      ring

lemma le_foldr_max {α : Type*} (f : α → ℕ) (L : List α) {a : α} (h : a ∈ L) :
    f a ≤ (L.map f).foldr max 0 := by
  induction L with
  | nil => cases h
  | cons b L ih =>
      rcases List.mem_cons.1 h with rfl | h
      · simp
      · simp only [List.map_cons, List.foldr_cons]
        exact le_max_of_le_right (ih h)

lemma forall_getElem_iff {α : Type*} (L : List α) (p : α → Prop) :
    (∀ pos : Fin L.length, p L[pos]) ↔ ∀ a ∈ L, p a := by
  constructor
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    exact h ⟨i, hi⟩
  · intro h pos
    exact h _ (List.getElem_mem pos.2)

/-- **Razborov's approximation lemma.**  Every gate of a circuit is computed, outside a small
set of bad inputs, by a function of low degree over `ZMod q`. -/
theorem approx_circuit {n : ℕ} (l : ℕ) (hl : 1 ≤ l) :
    ∀ {k : ℕ} (C : Ckt n k), ∃ (P : Fin k → Cube n → ZMod q) (B : Finset (Cube n)),
      B.card * 2 ^ l ≤ k * 2 ^ n ∧
      (∀ i, P i ∈ Deg (ZMod q) n (((q - 1) * l) ^ (C.depth i))) ∧
      (∀ i, ∀ x ∉ B, P i x = bit q (C.eval q x i)) := by
  classical
  have hq2 : 2 ≤ q := hq.out.two_le
  have hbase : 1 ≤ (q - 1) * l := Nat.one_le_iff_ne_zero.2 (by
    have : q - 1 ≠ 0 := by omega
    exact Nat.mul_ne_zero this (by omega))
  have hpowmono : ∀ a b : ℕ, a ≤ b → ((q - 1) * l) ^ a ≤ ((q - 1) * l) ^ b :=
    fun a b h => Nat.pow_le_pow_right hbase h
  intro k C
  induction C with
  | nil => exact ⟨Fin.elim0, ∅, by simp, fun i => i.elim0, fun i => i.elim0⟩
  | @cons k c g ih =>
      obtain ⟨P, B, hB, hdeg, hcorr⟩ := ih
      obtain ⟨newP, E, hE, hnewdeg, hnewcorr⟩ :
        ∃ (newP : Cube n → ZMod q) (E : Finset (Cube n)),
          E.card * 2 ^ l ≤ 2 ^ n ∧
          newP ∈ Deg (ZMod q) n (((q - 1) * l) ^ (g.depth c.depth)) ∧
          (∀ x, x ∉ B → x ∉ E → newP x = bit q (g.eval q (c.eval q x) x)) := by
        cases g with
        | var i =>
            refine ⟨coord (ZMod q) i, ∅, by simp, ?_, ?_⟩
            · simpa [Node.depth] using coord_mem_Deg (F := ZMod q) i (le_refl 1)
            · intro x _ _
              by_cases h : x i <;> simp [Node.eval, coord, bit, h]
        | const b =>
            refine ⟨fun _ => bit q b, ∅, by simp, ?_, ?_⟩
            · exact const_mem_Deg _ _
            · intro x _ _
              simp [Node.eval]
        | not j =>
            refine ⟨1 - P j, ∅, by simp, ?_, ?_⟩
            · exact Submodule.sub_mem _ (one_mem_Deg _) (hdeg j)
            · intro x hxB _
              simp only [Node.eval, Pi.sub_apply, Pi.one_apply, hcorr j x hxB]
              rw [← bit_not]
        | mod L =>
            set dmax := ((q - 1) * l) ^ ((L.map c.depth).foldr max 0) with hdmax
            set y : Fin L.length → Cube n → ZMod q := fun pos => P (L[pos]) with hy
            have hydeg : ∀ pos, y pos ∈ Deg (ZMod q) n dmax := by
              intro pos
              refine mem_Deg_of_le (hdeg (L[pos])) ?_
              exact hpowmono _ _ (le_foldr_max c.depth L (List.getElem_mem pos.2))
            refine ⟨fun x => 1 - Ez q (∑ pos : Fin L.length, y pos x), ∅, by simp, ?_, ?_⟩
            · have hsum : (fun x => ∑ pos : Fin L.length, y pos x) ∈ Deg (ZMod q) n dmax := by
                have he : (fun x => ∑ pos : Fin L.length, y pos x)
                    = ∑ pos : Fin L.length, y pos := by
                  funext x; simp [Finset.sum_apply]
                rw [he]
                exact Submodule.sum_mem _ (fun pos _ => hydeg pos)
              have hpow := pow_mem_Deg hsum (q - 1)
              have hfun : (fun x => 1 - Ez q (∑ pos : Fin L.length, y pos x))
                  = 1 - (fun x => ∑ pos : Fin L.length, y pos x) ^ (q - 1) := by
                funext x; simp [Ez, Pi.pow_apply]
              rw [hfun]
              refine Submodule.sub_mem _ (one_mem_Deg _) (mem_Deg_of_le hpow ?_)
              simp only [Node.depth]
              rw [pow_add, pow_one, ← hdmax]
              exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
            · intro x hxB _
              dsimp only
              have hval : ∑ pos : Fin L.length, y pos x
                  = ((L.countP (fun j => c.eval q x j) : ℕ) : ZMod q) := by
                rw [← sum_bit_countP (q := q) (fun j => c.eval q x j) L]
                rw [← Fin.sum_univ_fun_getElem L (fun j => bit q (c.eval q x j))]
                exact Finset.sum_congr rfl (fun pos _ => hcorr _ x hxB)
              rw [hval, Ez_eq_ite]
              have hdvd : (((L.countP (fun j => c.eval q x j) : ℕ) : ZMod q) = 0)
                  ↔ q ∣ L.countP (fun j => c.eval q x j) :=
                ZMod.natCast_eq_zero_iff _ _
              simp only [Node.eval, bit]
              by_cases hd : q ∣ L.countP (fun j => c.eval q x j)
              · rw [if_pos (hdvd.2 hd), if_pos (by simpa using hd)]
                simp
              · rw [if_neg (fun hcon => hd (hdvd.1 hcon)), if_neg (by simpa using hd)]
                simp
        | or L =>
            set dmax := ((q - 1) * l) ^ ((L.map c.depth).foldr max 0) with hdmax
            set y : Fin L.length → Cube n → ZMod q := fun pos => P (L[pos]) with hy
            have hydeg : ∀ pos, y pos ∈ Deg (ZMod q) n dmax := by
              intro pos
              refine mem_Deg_of_le (hdeg (L[pos])) ?_
              exact hpowmono _ _ (le_foldr_max c.depth L (List.getElem_mem pos.2))
            obtain ⟨ch, hch⟩ := exists_or_choice (q := q) (n := n) l y
            refine ⟨orPoly y ch,
              (Finset.univ : Finset (Cube n)).filter (fun x => orPoly y ch x ≠ orTarget y x),
              hch, ?_, ?_⟩
            · refine mem_Deg_of_le (orPoly_mem_Deg y ch hydeg) ?_
              simp only [Node.depth]
              rw [pow_add, pow_one, ← hdmax]
              exact le_of_eq (by ring)
            · intro x hxB hxE
              have hEq : orPoly y ch x = orTarget y x := by
                by_contra hcon
                exact hxE (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩)
              rw [hEq, orTarget]
              have hyx : ∀ pos : Fin L.length, y pos x = bit q (c.eval q x (L[pos])) :=
                fun pos => hcorr _ x hxB
              have hiff : (∀ pos : Fin L.length, y pos x = 0)
                  ↔ ∀ a ∈ L, c.eval q x a = false := by
                rw [← forall_getElem_iff L (fun a => c.eval q x a = false)]
                constructor
                · intro h pos
                  have := hyx pos
                  rw [h pos] at this
                  exact bit_eq_zero_iff.1 this.symm
                · intro h pos
                  rw [hyx pos, h pos]
                  simp [bit]
              simp only [Node.eval]
              by_cases hany : L.any (fun j => c.eval q x j) = true
              · have hnot : ¬ (∀ pos : Fin L.length, y pos x = 0) := by
                  rw [hiff]
                  intro hcon
                  obtain ⟨a, ha, hva⟩ := List.any_eq_true.1 hany
                  rw [hcon a ha] at hva
                  exact Bool.false_ne_true hva
                rw [if_neg hnot, hany]
                simp [bit]
              · have hyes : ∀ pos : Fin L.length, y pos x = 0 := by
                  rw [hiff]
                  intro a ha
                  by_contra hcon
                  exact hany (List.any_eq_true.2 ⟨a, ha, by simpa using hcon⟩)
                rw [if_pos hyes]
                have hf : L.any (fun j => c.eval q x j) = false := by simpa using hany
                rw [hf]
                simp [bit]
        | and L =>
            set dmax := ((q - 1) * l) ^ ((L.map c.depth).foldr max 0) with hdmax
            set z : Fin L.length → Cube n → ZMod q := fun pos => 1 - P (L[pos]) with hz
            have hzdeg : ∀ pos, z pos ∈ Deg (ZMod q) n dmax := by
              intro pos
              refine Submodule.sub_mem _ (one_mem_Deg _) (mem_Deg_of_le (hdeg (L[pos])) ?_)
              exact hpowmono _ _ (le_foldr_max c.depth L (List.getElem_mem pos.2))
            obtain ⟨ch, hch⟩ := exists_or_choice (q := q) (n := n) l z
            refine ⟨1 - orPoly z ch,
              (Finset.univ : Finset (Cube n)).filter (fun x => orPoly z ch x ≠ orTarget z x),
              hch, ?_, ?_⟩
            · refine Submodule.sub_mem _ (one_mem_Deg _)
                (mem_Deg_of_le (orPoly_mem_Deg z ch hzdeg) ?_)
              simp only [Node.depth]
              rw [pow_add, pow_one, ← hdmax]
              exact le_of_eq (by ring)
            · intro x hxB hxE
              have hEq : orPoly z ch x = orTarget z x := by
                by_contra hcon
                exact hxE (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩)
              simp only [Pi.sub_apply, Pi.one_apply, hEq, orTarget]
              have hzx : ∀ pos : Fin L.length, z pos x = 1 - bit q (c.eval q x (L[pos])) := by
                intro pos
                simp only [hz, Pi.sub_apply, Pi.one_apply, hcorr _ x hxB]
              have hiff : (∀ pos : Fin L.length, z pos x = 0)
                  ↔ ∀ a ∈ L, c.eval q x a = true := by
                rw [← forall_getElem_iff L (fun a => c.eval q x a = true)]
                constructor
                · intro h pos
                  have h2 := hzx pos
                  rw [h pos] at h2
                  by_contra hcon
                  have : c.eval q x (L[pos]) = false := by simpa using hcon
                  rw [this] at h2
                  simp [bit] at h2
                · intro h pos
                  rw [hzx pos, h pos]
                  simp [bit]
              simp only [Node.eval]
              by_cases hall : L.all (fun j => c.eval q x j) = true
              · have hyes : ∀ pos : Fin L.length, z pos x = 0 := by
                  rw [hiff]
                  intro a ha
                  exact List.all_eq_true.1 hall a ha
                rw [if_pos hyes, hall]
                simp [bit]
              · have hnot : ¬ (∀ pos : Fin L.length, z pos x = 0) := by
                  rw [hiff]
                  intro hcon
                  exact hall (List.all_eq_true.2 (fun a ha => hcon a ha))
                rw [if_neg hnot]
                have hf : L.all (fun j => c.eval q x j) = false := by simpa using hall
                rw [hf]
                simp [bit]
      refine ⟨Fin.snoc P newP, B ∪ E, ?_, ?_, ?_⟩
      · have hcard : (B ∪ E).card ≤ B.card + E.card := Finset.card_union_le _ _
        have : (B ∪ E).card * 2 ^ l ≤ (B.card + E.card) * 2 ^ l :=
          Nat.mul_le_mul_right _ hcard
        have h2 : (B.card + E.card) * 2 ^ l ≤ (k + 1) * 2 ^ n := by
          rw [add_mul, add_mul, one_mul]
          exact Nat.add_le_add hB hE
        omega
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa [Ckt.depth] using hnewdeg
        · intro j
          simpa [Ckt.depth] using hdeg j
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · intro x hx
          simp only [Fin.snoc_last, Ckt.eval]
          exact hnewcorr x (fun h => hx (Finset.mem_union_left _ h))
            (fun h => hx (Finset.mem_union_right _ h))
        · intro j x hx
          simp only [Fin.snoc_castSucc, Ckt.eval]
          rw [hcorr j x (fun h => hx (Finset.mem_union_left _ h))]

end Field

end CS

import Mathlib

/-!
# Low-degree functions on the Boolean cube

For a commutative ring `F` we consider the `F`-valued functions on the Boolean cube
`Cube n = Fin n → Bool`.  A *monomial* is a function of the form
`x ↦ ∏ i ∈ S, (if x i then 1 else 0)`.  The submodule `Deg F n D` is the span of all
monomials of degree at most `D`; these are exactly the functions computed by
multilinear polynomials of degree at most `D`.
-/

namespace CS

open Finset

/-- The Boolean cube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- The number of `true` coordinates of a point of the cube. -/
def ones {n : ℕ} (x : Cube n) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

section Ring

variable (F : Type*) [CommRing F] {n : ℕ}

/-- The `i`-th coordinate function, valued in `F`. -/
def coord {n : ℕ} (i : Fin n) : Cube n → F := fun x => if x i then 1 else 0

/-- The monomial function attached to a set `S` of coordinates. -/
def mono {n : ℕ} (S : Finset (Fin n)) : Cube n → F := fun x => ∏ i ∈ S, coord F i x

lemma mono_apply (S : Finset (Fin n)) (x : Cube n) :
    mono F S x = if ∀ i ∈ S, x i = true then 1 else 0 := by
  classical
  unfold mono coord
  split
  · next h => exact Finset.prod_eq_one (fun i hi => by simp [h i hi])
  · next h =>
      push_neg at h
      obtain ⟨i, hi, hxi⟩ := h
      refine Finset.prod_eq_zero hi ?_
      have hx : x i = false := by simpa using hxi
      simp [hx]

@[simp] lemma mono_empty : mono F (∅ : Finset (Fin n)) = 1 := by
  funext x; simp [mono]

lemma mono_mul_mono (S T : Finset (Fin n)) :
    mono F S * mono F T = mono F (S ∪ T) := by
  classical
  funext x
  simp only [Pi.mul_apply, mono_apply, Finset.forall_mem_union]
  split_ifs <;> simp_all

lemma coord_eq_mono (i : Fin n) : coord F i = mono F {i} := by
  funext x; simp [mono, coord]

/-- The submodule of functions of degree at most `D`. -/
def Deg (n D : ℕ) : Submodule F (Cube n → F) :=
  Submodule.span F {f | ∃ S : Finset (Fin n), S.card ≤ D ∧ f = mono F S}

variable {F}

lemma mono_mem_Deg {S : Finset (Fin n)} {D : ℕ} (h : S.card ≤ D) :
    mono F S ∈ Deg F n D :=
  Submodule.subset_span ⟨S, h, rfl⟩

lemma Deg_mono_le {D D' : ℕ} (h : D ≤ D') : Deg F n D ≤ Deg F n D' := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨S, hS, rfl⟩
  exact mono_mem_Deg (hS.trans h)

lemma mem_Deg_of_le {f : Cube n → F} {D D' : ℕ} (hf : f ∈ Deg F n D) (h : D ≤ D') :
    f ∈ Deg F n D' := Deg_mono_le h hf

lemma one_mem_Deg (D : ℕ) : (1 : Cube n → F) ∈ Deg F n D := by
  have := mono_mem_Deg (F := F) (S := (∅ : Finset (Fin n))) (D := D) (by simp)
  simpa using this

lemma const_mem_Deg (c : F) (D : ℕ) : (fun _ : Cube n => c) ∈ Deg F n D := by
  have : (fun _ : Cube n => c) = c • (1 : Cube n → F) := by funext x; simp
  rw [this]
  exact Submodule.smul_mem _ _ (one_mem_Deg D)

lemma coord_mem_Deg (i : Fin n) {D : ℕ} (h : 1 ≤ D) : coord F i ∈ Deg F n D := by
  rw [coord_eq_mono]
  exact mono_mem_Deg (by simpa using h)

/-- The degree filtration is multiplicative. -/
lemma mul_mem_Deg {f g : Cube n → F} {a b : ℕ}
    (hf : f ∈ Deg F n a) (hg : g ∈ Deg F n b) : f * g ∈ Deg F n (a + b) := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨T, hT, rfl⟩ := hg
          rw [mono_mul_mono]
          exact mono_mem_Deg ((Finset.card_union_le _ _).trans (Nat.add_le_add hS hT))
      | zero => simp
      | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu =>
          have : mono F S * (c • u) = c • (mono F S * u) := by
            funext x; simp [mul_comm, mul_left_comm]
          rw [this]; exact Submodule.smul_mem _ _ hu
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu =>
      have : (c • u) * g = c • (u * g) := by funext x; simp [mul_assoc]
      rw [this]; exact Submodule.smul_mem _ _ hu

lemma prod_mem_Deg {ι : Type*} (s : Finset ι) (f : ι → (Cube n → F)) (d : ι → ℕ)
    (h : ∀ i ∈ s, f i ∈ Deg F n (d i)) : (∏ i ∈ s, f i) ∈ Deg F n (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one_mem_Deg (F := F) (n := n) 0
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact mul_mem_Deg (h a (by simp)) (ih (fun i hi => h i (by simp [hi])))

lemma pow_mem_Deg {f : Cube n → F} {d : ℕ} (hf : f ∈ Deg F n d) (r : ℕ) :
    f ^ r ∈ Deg F n (r * d) := by
  induction r with
  | zero => simpa using one_mem_Deg 0
  | succ r ih =>
      have : f ^ (r + 1) = f ^ r * f := by ring
      rw [this]
      have := mul_mem_Deg ih hf
      exact mem_Deg_of_le this (by ring_nf; omega)

lemma prod_mem_Deg' {ι : Type*} (s : Finset ι) (f : ι → (Cube n → F))
    (h : ∀ i ∈ s, f i ∈ Deg F n 1) : (∏ i ∈ s, f i) ∈ Deg F n s.card := by
  simpa using prod_mem_Deg s f (fun _ => 1) h

/-- Composition with a map of cubes whose coordinates are degree-`1` functions preserves
the degree filtration. -/
lemma comp_mem_Deg {N : ℕ} (g : Cube n → Cube N) {f : Cube N → F} {D : ℕ}
    (hg : ∀ i : Fin N, (fun x => coord F i (g x)) ∈ Deg F n 1)
    (hf : f ∈ Deg F N D) : (fun x => f (g x)) ∈ Deg F n D := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, rfl⟩ := hf
      have : (fun x => mono F S (g x)) = ∏ i ∈ S, (fun x => coord F i (g x)) := by
        funext x; simp [mono, Finset.prod_apply]
      rw [this]
      exact mem_Deg_of_le (prod_mem_Deg' S _ (fun i _ => hg i)) hS
  | zero => exact Submodule.zero_mem _
  | add u v _ _ hu hv => exact Submodule.add_mem _ hu hv
  | smul c u _ hu => exact Submodule.smul_mem _ c hu

/-- Pushing a low-degree function forward along a ring homomorphism. -/
lemma map_mem_Deg {K : Type*} [CommRing K] (φ : F →+* K) {f : Cube n → F} {D : ℕ}
    (hf : f ∈ Deg F n D) : (fun x => φ (f x)) ∈ Deg K n D := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, rfl⟩ := hf
      have : (fun x => φ (mono F S x)) = mono K S := by
        funext x
        simp only [mono, coord, map_prod]
        exact Finset.prod_congr rfl (fun i _ => by by_cases h : x i <;> simp [h])
      rw [this]
      exact mono_mem_Deg hS
  | zero =>
      have h0 : (fun x : Cube n => φ ((0 : Cube n → F) x)) = 0 := by funext x; simp
      rw [h0]; exact Submodule.zero_mem _
  | add u v _ _ hu hv =>
      have : (fun x => φ ((u + v) x)) = (fun x => φ (u x)) + (fun x => φ (v x)) := by
        funext x; simp
      rw [this]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu =>
      have : (fun x => φ ((c • u) x)) = φ c • (fun x => φ (u x)) := by
        funext x; simp
      rw [this]; exact Submodule.smul_mem _ _ hu

/-- Indicator function of a point of the cube. -/
lemma ind_mem_Deg (a : Cube n) :
    (fun x => if x = a then (1 : F) else 0) ∈ Deg F n n := by
  classical
  have key : (fun x : Cube n => if x = a then (1 : F) else 0)
      = ∏ i ∈ (Finset.univ : Finset (Fin n)),
          (fun x : Cube n => if a i then coord F i x else 1 - coord F i x) := by
    funext x
    simp only [Finset.prod_apply]
    by_cases hx : x = a
    · subst hx
      rw [if_pos rfl]
      exact (Finset.prod_eq_one (fun i _ => by by_cases h : x i <;> simp [coord, h])).symm
    · rw [if_neg hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ a i := by
        by_contra h
        push_neg at h
        exact hx (funext h)
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      cases hxi : x i <;> cases hai : a i <;> simp [coord, hxi, hai] at hi ⊢
  rw [key]
  have h2 : (∏ i ∈ (Finset.univ : Finset (Fin n)),
      (fun x : Cube n => if a i then coord F i x else 1 - coord F i x))
        ∈ Deg F n (Finset.univ : Finset (Fin n)).card := by
    refine prod_mem_Deg' _ _ (fun i _ => ?_)
    by_cases h : a i
    · simpa [h] using coord_mem_Deg (F := F) i (le_refl 1)
    · simp only [h, if_false, Bool.false_eq_true]
      exact Submodule.sub_mem _ (one_mem_Deg 1) (coord_mem_Deg (F := F) i (le_refl 1))
  simpa using h2

lemma Deg_top : Deg F n n = ⊤ := by
  classical
  refine eq_top_iff.2 (fun f _ => ?_)
  have key : f = ∑ a : Cube n, f a • (fun x => if x = a then (1 : F) else 0) := by
    funext x
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [key]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (ind_mem_Deg a))

end Ring

section Field

variable {F : Type*} [Field F] {n : ℕ}

/-- The finite set of monomials of degree at most `D`. -/
noncomputable def monoFinset (F : Type*) [Field F] (n D : ℕ) : Finset (Cube n → F) := by
  classical
  exact ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D)).image (mono F)

lemma coe_monoFinset (D : ℕ) :
    ((monoFinset F n D : Finset (Cube n → F)) : Set (Cube n → F))
      = {f | ∃ S : Finset (Fin n), S.card ≤ D ∧ f = mono F S} := by
  classical
  ext f
  constructor
  · intro hf
    simp only [monoFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_filter] at hf
    obtain ⟨S, hS, rfl⟩ := hf
    exact ⟨S, hS.2, rfl⟩
  · rintro ⟨S, hS, rfl⟩
    simp only [monoFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
    exact ⟨S, ⟨Finset.mem_univ _, hS⟩, rfl⟩

lemma Deg_eq_span_monoFinset (D : ℕ) :
    Deg F n D = Submodule.span F (monoFinset F n D : Set (Cube n → F)) := by
  rw [coe_monoFinset]; rfl

lemma finrank_Deg_le (D : ℕ) :
    Module.finrank F (Deg F n D) ≤
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D)).card := by
  classical
  rw [Deg_eq_span_monoFinset]
  exact le_trans (finrank_span_finset_le_card _) (Finset.card_image_le)

end Field

end CS

import RequestProject.Deg

/-!
# Smolensky's counting argument

If, on a large subset `G` of the cube, the indicator functions of the residues of `ones x`
modulo `p` are all computed by polynomials of degree at most `D`, then `G` cannot be large:
`|G| ≤ #{S : Finset (Fin n) | #S ≤ m + D}` whenever `n ≤ 2 * m + 1`.

The argument works over a field `F` containing a `p`-th root of unity `ζ ≠ 1`.
-/

namespace CS

open Finset

section Smolensky

variable {F : Type*} [Field F] {n : ℕ}

variable (F) in
/-- The substituted variables `y i = 1 + (ζ - 1) x i`, taking the values `1` and `ζ`. -/
noncomputable def yv (ζ : F) (i : Fin n) : Cube n → F := fun x => 1 + (ζ - 1) * coord F i x

variable (F) in
/-- The inverse of `y i`, again an affine function of `x i`. -/
noncomputable def yinv (ζ : F) (i : Fin n) : Cube n → F := fun x => 1 + (ζ⁻¹ - 1) * coord F i x

variable (F) in
/-- The product of the `y i` over a set `S`. -/
noncomputable def Yprod (ζ : F) (S : Finset (Fin n)) : Cube n → F := ∏ i ∈ S, yv F ζ i

lemma yv_mem_Deg (ζ : F) (i : Fin n) : yv F ζ i ∈ Deg F n 1 := by
  have : yv F ζ i = (fun _ : Cube n => (1 : F)) + (ζ - 1) • coord F i := by
    funext x; simp [yv, Algebra.smul_def, mul_comm]
  rw [this]
  exact Submodule.add_mem _ (const_mem_Deg 1 1) (Submodule.smul_mem _ _ (coord_mem_Deg i le_rfl))

lemma yinv_mem_Deg (ζ : F) (i : Fin n) : yinv F ζ i ∈ Deg F n 1 := by
  have : yinv F ζ i = (fun _ : Cube n => (1 : F)) + (ζ⁻¹ - 1) • coord F i := by
    funext x; simp [yinv, Algebra.smul_def, mul_comm]
  rw [this]
  exact Submodule.add_mem _ (const_mem_Deg 1 1) (Submodule.smul_mem _ _ (coord_mem_Deg i le_rfl))

lemma Yprod_mem_Deg (ζ : F) (S : Finset (Fin n)) : Yprod F ζ S ∈ Deg F n S.card :=
  prod_mem_Deg' _ _ (fun i _ => yv_mem_Deg ζ i)

lemma yv_apply_mul_yinv_apply {ζ : F} (hζ : ζ ≠ 0) (i : Fin n) (x : Cube n) :
    yv F ζ i x * yinv F ζ i x = 1 := by
  by_cases h : x i <;> simp [yv, yinv, coord, h]
  field_simp

lemma yv_apply {ζ : F} (i : Fin n) (x : Cube n) :
    yv F ζ i x = if x i then ζ else 1 := by
  by_cases h : x i <;> simp [yv, coord, h]

/-- `∏ i, y i` computes `ζ ^ (ones x)`. -/
lemma Yprod_univ_apply (ζ : F) (x : Cube n) :
    Yprod F ζ (Finset.univ) x = ζ ^ ones x := by
  classical
  simp only [Yprod, Finset.prod_apply, yv_apply, ones]
  rw [Finset.prod_ite]
  simp

/-- Smolensky's dimension bound. -/
theorem smolensky_bound {p : ℕ} (hp : 0 < p) (ζ : F) (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1)
    {m D : ℕ} (hnm : n ≤ 2 * m + 1) (G : Finset (Cube n))
    (Q : Fin p → Cube n → F) (hQdeg : ∀ j, Q j ∈ Deg F n D)
    (hQ : ∀ j : Fin p, ∀ x ∈ G, Q j x = if ones x % p = (j : ℕ) then 1 else 0) :
    G.card ≤ ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ m + D)).card := by
  classical
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h] at hζp; simp [zero_pow hp.ne'] at hζp
  -- the restriction map to `G`
  set ρ : (Cube n → F) →ₗ[F] (G → F) :=
    { toFun := fun f => fun x => f (x : Cube n)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } with hρ
  have hρsurj : Function.Surjective ρ := by
    intro g
    refine ⟨fun x => if h : x ∈ G then g ⟨x, h⟩ else 0, ?_⟩
    funext x
    simp [hρ, x.2]
  -- The combination of the `Q j` computing `∏ i, y i` on `G`.
  set R : Cube n → F := ∑ j : Fin p, (ζ ^ (j : ℕ)) • Q j with hR
  have hRdeg : R ∈ Deg F n D :=
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hQdeg j))
  have hRG : ∀ x ∈ G, R x = Yprod F ζ Finset.univ x := by
    intro x hx
    have hlt : ones x % p < p := Nat.mod_lt _ hp
    rw [Yprod_univ_apply]
    simp only [hR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (⟨_, hlt⟩ : Fin p)]
    · rw [hQ _ x hx, if_pos rfl, mul_one]
      conv_rhs => rw [← Nat.div_add_mod (ones x) p]
      rw [pow_add, pow_mul, hζp, one_pow, one_mul]
    · intro b _ hb
      rw [hQ _ x hx, if_neg, mul_zero]
      intro h
      exact hb (Fin.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  -- every `Yprod` agrees on `G` with a function of degree at most `m + D`
  have key : ∀ S : Finset (Fin n), ∃ g ∈ Deg F n (m + D), ∀ x ∈ G, Yprod F ζ S x = g x := by
    intro S
    by_cases hS : S.card ≤ m
    · exact ⟨Yprod F ζ S, mem_Deg_of_le (Yprod_mem_Deg ζ S) (le_trans hS (Nat.le_add_right _ _)),
        fun x _ => rfl⟩
    · push_neg at hS
      refine ⟨R * ∏ i ∈ Sᶜ, yinv F ζ i, ?_, ?_⟩
      · have hcard : Sᶜ.card ≤ m := by
          have := Finset.card_compl S
          have h1 : Sᶜ.card = n - S.card := by simpa using this
          omega
        have : R * ∏ i ∈ Sᶜ, yinv F ζ i ∈ Deg F n (D + Sᶜ.card) :=
          mul_mem_Deg hRdeg (prod_mem_Deg' _ _ (fun i _ => yinv_mem_Deg ζ i))
        exact mem_Deg_of_le this (by omega)
      · intro x hx
        have h1 : (R * ∏ i ∈ Sᶜ, yinv F ζ i) x
            = Yprod F ζ Finset.univ x * ∏ i ∈ Sᶜ, yinv F ζ i x := by
          simp [hRG x hx, Finset.prod_apply]
        rw [h1]
        have h2 : Yprod F ζ Finset.univ x = Yprod F ζ S x * ∏ i ∈ Sᶜ, yv F ζ i x := by
          simp only [Yprod, Finset.prod_apply]
          rw [← Finset.prod_union (disjoint_compl_right)]
          congr 1
          simp
        rw [h2, mul_assoc, ← Finset.prod_mul_distrib]
        rw [Finset.prod_congr rfl (fun i _ => yv_apply_mul_yinv_apply hζ0 i x)]
        simp
  -- hence the restriction of `Deg F n (m + D)` to `G` is everything
  have hmap : Submodule.map ρ (Deg F n (m + D)) = ⊤ := by
    refine eq_top_iff.2 ?_
    rintro g -
    obtain ⟨f, rfl⟩ := hρsurj g
    -- it suffices to treat `f` in a spanning set
    have hW : ∀ f : Cube n → F, ρ f ∈ Submodule.map ρ (Deg F n (m + D)) := by
      intro f
      have hmem : f ∈ (⊤ : Submodule F (Cube n → F)) := trivial
      rw [← Deg_top (F := F) (n := n)] at hmem
      have hYmem : ∀ T : Finset (Fin n), ρ (Yprod F ζ T) ∈ Submodule.map ρ (Deg F n (m + D)) := by
        intro T
        obtain ⟨g, hg, hgT⟩ := key T
        refine ⟨g, hg, ?_⟩
        funext x
        exact (hgT x x.2).symm
      have hmono : ∀ S : Finset (Fin n), ρ (mono F S) ∈ Submodule.map ρ (Deg F n (m + D)) := by
        intro S
        have hne : (ζ - 1) ≠ 0 := sub_ne_zero.2 hζ1
        have hcoord : ∀ i : Fin n, coord F i
            = (fun _ : Cube n => (ζ - 1)⁻¹) * yv F ζ i
              + (fun _ : Cube n => -(ζ - 1)⁻¹) := by
          intro i
          funext x
          simp only [Pi.add_apply, Pi.mul_apply, yv]
          field_simp
          ring
        have hprod : mono F S = ∏ i ∈ S, coord F i := by
          funext x; simp [mono, Finset.prod_apply]
        rw [hprod]
        rw [Finset.prod_congr rfl (fun i _ => hcoord i)]
        rw [Finset.prod_add]
        rw [map_sum]
        refine Submodule.sum_mem _ (fun T hT => ?_)
        have : ((∏ i ∈ T, ((fun _ : Cube n => (ζ - 1)⁻¹) * yv F ζ i))
              * ∏ _i ∈ S \ T, (fun _ : Cube n => -(ζ - 1)⁻¹))
            = ((ζ - 1)⁻¹ ^ T.card * (-(ζ - 1)⁻¹) ^ (S \ T).card) • Yprod F ζ T := by
          rw [Finset.prod_mul_distrib]
          funext x
          simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Finset.prod_apply,
            Finset.prod_const, Pi.pow_apply, Yprod]
          ring
        rw [this, map_smul]
        exact Submodule.smul_mem _ _ (hYmem T)
      induction hmem using Submodule.span_induction with
      | mem f hf => obtain ⟨S, _, rfl⟩ := hf; exact hmono S
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ _ hu
    exact hW f
  -- dimension count
  have h1 : Module.finrank F (G → F) = G.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have h2 : Module.finrank F (G → F) ≤ Module.finrank F (Deg F n (m + D)) := by
    have := Submodule.finrank_map_le ρ (Deg F n (m + D))
    rwa [hmap, finrank_top] at this
  calc G.card = Module.finrank F (G → F) := h1.symm
    _ ≤ Module.finrank F (Deg F n (m + D)) := h2
    _ ≤ _ := finrank_Deg_le _

end Smolensky

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

import RequestProject.Deg

/-!
# Constant depth circuits with MOD gates

We model a circuit as a straight-line program: a list of gates, each of which may use the
input variables and the values of the previously computed gates.  Gates are

* input variables and constants,
* negations (which are *free*: they do not increase the depth),
* unbounded fan-in `AND` and `OR` gates,
* unbounded fan-in `MOD q` gates, which output `true` iff the number of `true` inputs is
  divisible by `q`.

The size of a circuit is its number of gates, and the depth of a gate is the maximal number of
`AND`/`OR`/`MOD` gates on a path from an input to it.

`InAC0mod q f` says that the family of Boolean functions `f` is computed by a family of
circuits of polynomial size and constant depth using such gates; this is the class `AC⁰[q]`.
-/

namespace CS

open Finset

/-- A gate of a straight-line program which may refer to the `k` previously computed gates. -/
inductive Node (n : ℕ) (k : ℕ) : Type
  | var : Fin n → Node n k
  | const : Bool → Node n k
  | not : Fin k → Node n k
  | or : List (Fin k) → Node n k
  | and : List (Fin k) → Node n k
  | mod : List (Fin k) → Node n k
  deriving Inhabited

/-- Value of a gate, given the values of the previous gates and the input. -/
def Node.eval (q : ℕ) {n k : ℕ} (g : Node n k) (v : Fin k → Bool) (x : Cube n) : Bool :=
  match g with
  | .var i => x i
  | .const b => b
  | .not j => !(v j)
  | .or L => L.any (fun j => v j)
  | .and L => L.all (fun j => v j)
  | .mod L => decide (q ∣ L.countP (fun j => v j))

/-- Depth of a gate, given the depths of the previous gates.  Negations are free. -/
def Node.depth {n k : ℕ} (g : Node n k) (dep : Fin k → ℕ) : ℕ :=
  match g with
  | .var _ => 0
  | .const _ => 0
  | .not j => dep j
  | .or L => 1 + (L.map dep).foldr max 0
  | .and L => 1 + (L.map dep).foldr max 0
  | .mod L => 1 + (L.map dep).foldr max 0

/-- A straight-line circuit with `k` gates on `n` inputs. -/
inductive Ckt (n : ℕ) : ℕ → Type
  | nil : Ckt n 0
  | cons : ∀ {k : ℕ}, Ckt n k → Node n k → Ckt n (k + 1)

/-- The values of all the gates of a circuit on a given input. -/
def Ckt.eval (q : ℕ) {n : ℕ} : ∀ {k : ℕ}, Ckt n k → Cube n → Fin k → Bool
  | _, .nil, _ => Fin.elim0
  | _, .cons c g, x => Fin.snoc (Ckt.eval q c x) (g.eval q (Ckt.eval q c x) x)

/-- The depths of all the gates of a circuit. -/
def Ckt.depth {n : ℕ} : ∀ {k : ℕ}, Ckt n k → Fin k → ℕ
  | _, .nil => Fin.elim0
  | _, .cons c g => Fin.snoc (Ckt.depth c) (g.depth (Ckt.depth c))

/-- The class `AC⁰[q]`: families of Boolean functions computed by polynomial size,
constant depth circuits with unbounded fan-in `AND`, `OR` and `MOD q` gates. -/
def InAC0mod (q : ℕ) (f : ∀ n, Cube n → Bool) : Prop :=
  ∃ d c : ℕ, ∀ n : ℕ, ∃ (k : ℕ) (C : Ckt n k) (o : Fin k),
    k ≤ c * (n + 1) ^ c ∧ C.depth o ≤ d ∧ ∀ x, C.eval q x o = f n x

/-- The `MOD p` function: `true` iff the number of ones of the input is divisible by `p`. -/
def MODfun (p : ℕ) : ∀ n : ℕ, Cube n → Bool := fun _ x => decide (p ∣ ones x)

end CS

/-
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Approx
import RequestProject.Counting
import RequestProject.Binom
import RequestProject.Aux

/-!
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

lemma ones_append {n p : ℕ} (x : Cube n) (e : Cube p) :
    ones (Fin.append x e) = ones x + ones e := by
  classical
  simp only [ones, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

lemma card_filter_val_lt (p r : ℕ) (hr : r ≤ p) :
    (Finset.filter (fun i : Fin p => (i : ℕ) < r) Finset.univ).card = r := by
  classical
  have h : (Finset.filter (fun i : Fin p => (i : ℕ) < r) Finset.univ).image (Fin.val)
      = Finset.range r := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro ha; exact ⟨⟨a, lt_of_lt_of_le ha hr⟩, ha, rfl⟩
  have h2 : (Finset.filter (fun i : Fin p => (i : ℕ) < r) Finset.univ).card
      = ((Finset.filter (fun i : Fin p => (i : ℕ) < r) Finset.univ).image (Fin.val)).card :=
    (Finset.card_image_of_injective _ Fin.val_injective).symm
  rw [h2, h, Finset.card_range]

lemma dvd_add_sub_mod {p s j : ℕ} (hp : 0 < p) (hj : j < p) :
    (p ∣ s + (p - j) % p) ↔ s % p = j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [Nat.dvd_iff_mod_eq_zero]
  · have hr : (p - j) % p = p - j := Nat.mod_eq_of_lt (by omega)
    rw [hr]
    set b := s % p with hb
    have hbp : b < p := Nat.mod_lt _ hp
    have key : (s + (p - j)) % p = (b + p - j) % p := by
      conv_lhs => rw [Nat.add_mod]
      rw [← hb, Nat.mod_eq_of_lt (show p - j < p by omega)]
      congr 1
      omega
    rw [Nat.dvd_iff_mod_eq_zero, key]
    rcases lt_trichotomy b j with h | h | h
    · rw [Nat.mod_eq_of_lt (by omega)]
      constructor <;> intro <;> omega
    · rw [h, show j + p - j = p by omega, Nat.mod_self]
      simp
    · rw [show b + p - j = p + (b - j) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)]
      constructor <;> intro <;> omega

/-- The heart of the Razborov–Smolensky argument, over an abstract field `F` of characteristic
`q` containing a nontrivial `p`-th root of unity. -/
theorem razborov_smolensky_aux {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (F : Type) [Field F] [CharP F q] (ζ : F) (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1) :
    ¬ InAC0mod q (MODfun p) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  rintro ⟨d0, c0, H⟩
  obtain ⟨t, l, m, hl, -, hparam1, hparam2⟩ :=
    exists_params p q (d0 + 1) (c0 + 1) hp.two_le (by omega) (by omega)
  set D := ((q - 1) * l) ^ (d0 + 1) with hD
  have hbase : 1 ≤ (q - 1) * l :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := hq.two_le; omega) (by omega))
  -- the circuit computing `MOD p` on `(2 * m + 1) + p` inputs
  obtain ⟨k, C, o, hk, hdepth, heval⟩ := H (2 * m + 1 + p)
  have hk1 : 0 < k := lt_of_le_of_lt (Nat.zero_le _) o.2
  -- Razborov's approximation
  obtain ⟨P, B, hB, hPdeg, hPcorr⟩ := approx_circuit (q := q) (n := 2 * m + 1 + p) l hl C
  have hPo : P o ∈ Deg (ZMod q) (2 * m + 1 + p) D := by
    refine mem_Deg_of_le (hPdeg o) ?_
    exact Nat.pow_le_pow_right hbase (le_trans hdepth (by omega))
  set φ : ZMod q →+* F := ZMod.castHom (dvd_refl q) F with hφ
  -- the shifted inputs
  set e : Fin p → Cube p := fun j => fun i => decide ((i : ℕ) < (p - (j : ℕ)) % p) with he
  set g : Fin p → Cube (2 * m + 1) → Cube (2 * m + 1 + p) :=
    fun j x => Fin.append x (e j) with hg
  set Q : Fin p → Cube (2 * m + 1) → F := fun j x => φ (P o (g j x)) with hQ
  set Bad : Fin p → Finset (Cube (2 * m + 1)) :=
    fun j => Finset.univ.filter (fun x => g j x ∈ B) with hBad
  set G : Finset (Cube (2 * m + 1)) := Finset.univ \ (Finset.univ.biUnion Bad) with hG
  -- the degrees
  have hQdeg : ∀ j : Fin p, Q j ∈ Deg F (2 * m + 1) D := by
    intro j
    have h1 : (fun z => φ (P o z)) ∈ Deg F (2 * m + 1 + p) D := map_mem_Deg φ hPo
    refine comp_mem_Deg (g j) ?_ h1
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro a
      have h2 : (fun x : Cube (2 * m + 1) => coord F (Fin.castAdd p a) (g j x)) = coord F a := by
        funext x
        simp [hg, coord, Fin.append_left]
      rw [h2]
      exact coord_mem_Deg a le_rfl
    · intro b
      have h2 : (fun x : Cube (2 * m + 1) => coord F (Fin.natAdd (2 * m + 1) b) (g j x))
          = fun _ => coord F b (e j) := by
        funext x
        simp [hg, coord, Fin.append_right]
      rw [h2]
      exact const_mem_Deg _ _
  -- the values
  have honesE : ∀ j : Fin p, ones (e j) = (p - (j : ℕ)) % p := by
    intro j
    have hfilter : (Finset.univ.filter (fun i : Fin p => e j i = true))
        = Finset.filter (fun i : Fin p => (i : ℕ) < (p - (j : ℕ)) % p) Finset.univ := by
      apply Finset.filter_congr
      intro i _
      simp [he]
    rw [ones, hfilter]
    exact card_filter_val_lt p _ (le_of_lt (Nat.mod_lt _ hp.pos))
  have hQcorr : ∀ j : Fin p, ∀ x ∈ G, Q j x = if ones x % p = (j : ℕ) then 1 else 0 := by
    intro j x hxG
    have hxB : g j x ∉ B := by
      intro hmem
      have h1 : x ∈ Bad j := Finset.mem_filter.2 ⟨Finset.mem_univ _, hmem⟩
      have h2 : x ∈ Finset.univ.biUnion Bad := Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, h1⟩
      exact (Finset.mem_sdiff.1 hxG).2 h2
    have h1 : P o (g j x) = bit q (C.eval q (g j x) o) := hPcorr o _ hxB
    rw [heval] at h1
    have h2 : ones (g j x) = ones x + (p - (j : ℕ)) % p := by
      rw [hg]
      simp only
      rw [ones_append, honesE j]
    have h3 : (p ∣ ones (g j x)) ↔ ones x % p = (j : ℕ) := by
      rw [h2]
      exact dvd_add_sub_mod hp.pos j.2
    have h4 : Q j x = φ (bit q (MODfun p (2 * m + 1 + p) (g j x))) := by rw [hQ]; simp only [h1]
    rw [h4, MODfun]
    by_cases hcase : ones x % p = (j : ℕ)
    · rw [if_pos hcase, decide_eq_true (h3.2 hcase)]
      simp [bit]
    · have h5 : ¬ (p ∣ ones (g j x)) := fun hdv => hcase (h3.1 hdv)
      rw [if_neg hcase, decide_eq_false h5]
      simp [bit]
  -- the size of the good set
  have hGcard : 2 ^ (2 * m + 1) ≤ G.card + p * B.card := by
    have h2 : ∀ j : Fin p, (Bad j).card ≤ B.card := by
      intro j
      refine Finset.card_le_card_of_injOn (g j) ?_ ?_
      · intro x hx
        have := (Finset.mem_filter.1 (by simpa using hx : x ∈ Bad j)).2
        simpa using this
      · intro x _ y _ hxy
        funext i
        have h3 := congrFun hxy (Fin.castAdd p i)
        simpa [hg, Fin.append_left] using h3
    have h1 : (Finset.univ.biUnion Bad).card ≤ ∑ j : Fin p, (Bad j).card :=
      Finset.card_biUnion_le
    have h3 : ∑ j : Fin p, (Bad j).card ≤ p * B.card := by
      calc ∑ j : Fin p, (Bad j).card ≤ ∑ _j : Fin p, B.card :=
            Finset.sum_le_sum (fun j _ => h2 j)
        _ = p * B.card := by simp
    have h4 : G.card + (Finset.univ.biUnion Bad).card
        = (Finset.univ : Finset (Cube (2 * m + 1))).card := by
      rw [hG]
      exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
    have h5 : (Finset.univ : Finset (Cube (2 * m + 1))).card = 2 ^ (2 * m + 1) := by
      simp [Finset.card_univ]
    omega
  -- Smolensky's bound
  have hsmol : G.card ≤ ((Finset.univ : Finset (Finset (Fin (2 * m + 1)))).filter
      (fun S => S.card ≤ m + D)).card :=
    smolensky_bound hp.pos ζ hζ1 hζp le_rfl G Q hQdeg hQcorr
  have hcount : G.card ≤ 4 ^ m + D * ((2 * m + 1).choose m) := by
    refine le_trans hsmol ?_
    rw [card_filter_card_le (2 * m + 1) (m + D)]
    exact sum_choose_le m D
  -- the two quantitative estimates
  have hR1 : 8 * p * k * 2 ^ p ≤ 2 ^ l := by
    refine hparam1 k (le_trans hk ?_)
    have h1 : (2 * m + 1 + p + 1) ^ c0 ≤ (2 * m + 1 + p + 1) ^ (c0 + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.mul_le_mul (by omega) h1
  have hR2 : 9 * D ^ 2 ≤ m := hparam2
  -- `4 * (p * |B|) ≤ 4 ^ m`
  have hb : 4 * (p * B.card) ≤ 4 ^ m := by
    have h1 : B.card * (8 * p * k * 2 ^ p) ≤ B.card * 2 ^ l := Nat.mul_le_mul_left _ hR1
    have h3 : (2 : ℕ) ^ (2 * m + 1 + p) = 2 * 4 ^ m * 2 ^ p := by
      rw [pow_add, pow_succ, pow_mul]; norm_num; ring
    have h4 : B.card * (8 * p * k * 2 ^ p) ≤ k * (2 * 4 ^ m * 2 ^ p) := by
      rw [← h3]
      exact le_trans h1 hB
    have h5 : (2 * (4 * (p * B.card))) * (k * 2 ^ p) ≤ (2 * 4 ^ m) * (k * 2 ^ p) := by
      calc (2 * (4 * (p * B.card))) * (k * 2 ^ p) = B.card * (8 * p * k * 2 ^ p) := by ring
        _ ≤ k * (2 * 4 ^ m * 2 ^ p) := h4
        _ = (2 * 4 ^ m) * (k * 2 ^ p) := by ring
    have h6 : 0 < k * 2 ^ p := by positivity
    have h7 : 2 * (4 * (p * B.card)) ≤ 2 * 4 ^ m := Nat.le_of_mul_le_mul_right h5 h6
    exact Nat.le_of_mul_le_mul_left h7 (by norm_num)
  -- the final contradiction
  have hfinal : 2 * 4 ^ m ≤ G.card + p * B.card := by
    have h1 : (2 : ℕ) ^ (2 * m + 1) = 2 * 4 ^ m := by
      rw [pow_succ, pow_mul]; norm_num; ring
    omega
  exact final_arith hb (choose_mul_lt hR2) (by omega)

/-- **Razborov–Smolensky.**  For distinct primes `p` and `q`, the function `MOD p` is not in
`AC⁰[q]`: it is not computed by any family of constant depth, polynomial size circuits with
unbounded fan-in `AND`, `OR`, `NOT` and `MOD q` gates. -/
theorem razborov_smolensky {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ InAC0mod q (MODfun p) := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨ζ, hζp, hζ1⟩ := exists_root_of_unity p q hp hpq
  exact razborov_smolensky_aux hp hq (GaloisField q (p - 1)) ζ hζ1 hζp

end CS

