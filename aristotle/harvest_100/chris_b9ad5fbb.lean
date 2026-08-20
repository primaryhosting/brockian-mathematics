import Mathlib
/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the very first command in a file, so the header
comment appears immediately after it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace QPhys

open Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The degree-`N` homogeneous component of the product `exp a * exp b`. -/
noncomputable def bchL (a b : A) (N : ℕ) : A :=
  ∑ m ∈ range (N + 1), ((m ! : ℚ) * ((N - m)! : ℚ))⁻¹ • (a ^ m * b ^ (N - m))

/-- Rational coefficients appearing in `bchR`. -/
noncomputable def bchCoef (N j : ℕ) : ℚ :=
  if 2 * j ≤ N then (((N - 2 * j)! : ℚ) * (j ! : ℚ) * 2 ^ j)⁻¹ else 0

/-- The degree-`N` homogeneous component of `exp d * exp (2⁻¹ • c)`, where `c` is given
degree `2` and `d` degree `1`. -/
noncomputable def bchR (c d : A) (N : ℕ) : A :=
  ∑ j ∈ range (N + 1), bchCoef N j • (c ^ j * d ^ (N - 2 * j))

section

variable {a b c d : A}

/-- Moving `b` past a power of `a`, when the commutator `c = ab - ba` is central. -/
lemma mul_pow_succ_comm_of_central (hc : c = a * b - b * a) (hac : Commute a c) (m : ℕ) :
    b * a ^ (m + 1) = a ^ (m + 1) * b - ((m : ℚ) + 1) • (c * a ^ m) := by
  have hba : b * a = a * b - c := by rw [hc]; abel
  induction m with
  | zero => simp [hba]
  | succ n ih =>
    have h0 : b * a ^ (n + 2) = (b * a ^ (n + 1)) * a := by rw [pow_succ, ← mul_assoc]
    rw [h0, ih, sub_mul, mul_assoc, hba, smul_mul_assoc]
    have h1 : a ^ (n + 1) * (a * b - c) = a ^ (n + 2) * b - c * a ^ (n + 1) := by
      rw [mul_sub, ← mul_assoc, ← pow_succ, (hac.pow_left (n + 1)).eq]
    rw [h1, mul_assoc]
    push_cast
    rw [← pow_succ]
    module

/-- Moving `b` past a power of `a`, when the commutator `c = ab - ba` is central. -/
lemma mul_pow_comm_of_central (hc : c = a * b - b * a) (hac : Commute a c) (m : ℕ) :
    b * a ^ m = a ^ m * b - (m : ℚ) • (c * a ^ (m - 1)) := by
  cases m with
  | zero => simp
  | succ n => simpa using mul_pow_succ_comm_of_central hc hac n

lemma bchL_zero (a b : A) : bchL a b 0 = 1 := by
  simp [bchL]

lemma bchL_one (a b : A) : bchL a b 1 = a + b := by
  simp [bchL, Finset.sum_range_succ, add_comm]

lemma bchL_rec (hc : c = a * b - b * a) (hac : Commute a c) (N : ℕ) :
    ((N + 2 : ℕ) : ℚ) • bchL a b (N + 2)
      = (a + b) * bchL a b (N + 1) + c * bchL a b N := by
  have hA : a * bchL a b (N + 1)
      = ∑ m ∈ range (N + 3), ((m : ℚ) * ((m ! : ℚ) * ((N + 2 - m)! : ℚ))⁻¹) •
          (a ^ m * b ^ (N + 2 - m)) := by
    rw [Finset.sum_range_succ' _ (N + 2), bchL, Finset.mul_sum]
    simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero, Nat.succ_sub_succ]
    refine (Finset.sum_congr rfl fun m hm => ?_).symm
    rw [mul_smul_comm, ← mul_assoc, ← pow_succ']
    congr 1
    push_cast [Nat.factorial_succ]
    have h1 : (m ! : ℚ) ≠ 0 := by positivity
    have h2 : ((N + 1 - m)! : ℚ) ≠ 0 := by positivity
    field_simp
  have hB1 : b * bchL a b (N + 1)
      = (∑ m ∈ range (N + 2), ((m ! : ℚ) * ((N + 1 - m)! : ℚ))⁻¹ • (a ^ m * b ^ (N + 2 - m)))
        - ∑ m ∈ range (N + 2), ((m : ℚ) * ((m ! : ℚ) * ((N + 1 - m)! : ℚ))⁻¹) •
            (c * (a ^ (m - 1) * b ^ (N + 1 - m))) := by
    rw [bchL, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ N + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hex : N + 2 - m = (N + 1 - m) + 1 := by omega
    rw [hex, mul_smul_comm, ← mul_assoc, mul_pow_comm_of_central hc hac, sub_mul, smul_sub,
      mul_assoc (a ^ m) b, ← pow_succ', smul_mul_assoc, mul_assoc, smul_smul, mul_comm ((m : ℚ))]
  have hB2 : ∑ m ∈ range (N + 2), ((m ! : ℚ) * ((N + 1 - m)! : ℚ))⁻¹ • (a ^ m * b ^ (N + 2 - m))
      = ∑ m ∈ range (N + 3), (((N + 2 - m : ℕ) : ℚ) * ((m ! : ℚ) * ((N + 2 - m)! : ℚ))⁻¹) •
          (a ^ m * b ^ (N + 2 - m)) := by
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ N + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hex : N + 2 - m = (N + 1 - m) + 1 := by omega
    rw [hex]
    congr 1
    push_cast [Nat.factorial_succ]
    have h1 : (m ! : ℚ) ≠ 0 := by positivity
    have h2 : ((N + 1 - m)! : ℚ) ≠ 0 := by positivity
    field_simp
  have hB3 : ∑ m ∈ range (N + 2), ((m : ℚ) * ((m ! : ℚ) * ((N + 1 - m)! : ℚ))⁻¹) •
        (c * (a ^ (m - 1) * b ^ (N + 1 - m))) = c * bchL a b N := by
    rw [bchL, Finset.mul_sum, Finset.sum_range_succ' _ (N + 1)]
    simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hex : N + 1 - (m + 1) = N - m := by omega
    rw [hex, mul_smul_comm]
    simp only [Nat.add_sub_cancel]
    congr 1
    push_cast [Nat.factorial_succ]
    have h1 : (m ! : ℚ) ≠ 0 := by positivity
    have h2 : ((N - m)! : ℚ) ≠ 0 := by positivity
    field_simp
  have hC : ((N + 2 : ℕ) : ℚ) • bchL a b (N + 2)
      = ∑ m ∈ range (N + 3), (((N + 2 : ℕ) : ℚ) * ((m ! : ℚ) * ((N + 2 - m)! : ℚ))⁻¹) •
          (a ^ m * b ^ (N + 2 - m)) := by
    rw [bchL, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_smul]
  rw [hC, add_mul, hA, hB1, hB2, hB3, add_assoc, sub_add_cancel, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ N + 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [← add_smul]
  congr 1
  have hcast : ((N + 2 - m : ℕ) : ℚ) = ((N + 2 : ℕ) : ℚ) - (m : ℚ) := by
    push_cast [Nat.cast_sub hm']
    ring
  rw [hcast]
  ring

lemma bchR_zero (c d : A) : bchR c d 0 = 1 := by
  simp [bchR, bchCoef]

lemma bchR_one (c d : A) : bchR c d 1 = d := by
  simp [bchR, bchCoef, Finset.sum_range_succ]

lemma bchCoef_rec (N j : ℕ) :
    ((N + 2 : ℕ) : ℚ) * bchCoef (N + 2) j
      = bchCoef (N + 1) j + (if j = 0 then 0 else bchCoef N (j - 1)) := by
  cases j with
  | zero =>
    simp only [bchCoef, Nat.mul_zero, Nat.zero_le, if_pos, Nat.sub_zero,
      Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one]
    rw [Nat.factorial_succ (N + 1)]
    push_cast
    have h1 : ((N + 1)! : ℚ) ≠ 0 := by positivity
    field_simp
    ring
  | succ k =>
    have hk0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
    simp only [hk0, if_false, Nat.add_sub_cancel]
    have hfk : ((k ! : ℚ)) ≠ 0 := by positivity
    rcases le_or_gt (2 * (k + 1)) (N + 1) with h | h
    · have h2 : 2 * (k + 1) ≤ N + 2 := by omega
      have h3 : 2 * k ≤ N := by omega
      obtain ⟨v, hv⟩ : ∃ v, N - 2 * k = v + 1 := ⟨N - 2 * k - 1, by omega⟩
      have e1 : N + 2 - 2 * (k + 1) = v + 1 := by omega
      have e2 : N + 1 - 2 * (k + 1) = v := by omega
      rw [bchCoef, bchCoef, bchCoef, if_pos h2, if_pos h, if_pos h3, e1, e2, hv]
      have hNv : ((N + 2 : ℕ) : ℚ) = ((v : ℚ) + 1) + 2 * ((k : ℚ) + 1) := by
        have hN : N + 2 = (v + 1) + 2 * (k + 1) := by omega
        rw [hN]; push_cast; ring
      have hfv : ((v ! : ℚ)) ≠ 0 := by positivity
      rw [hNv]
      simp only [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · rcases eq_or_lt_of_le (show N + 2 ≤ 2 * (k + 1) by omega) with h4 | h4
      · have h3 : 2 * k ≤ N := by omega
        have h5 : ¬ (2 * (k + 1) ≤ N + 1) := by omega
        have h6 : N + 2 - 2 * (k + 1) = 0 := by omega
        have h7 : N - 2 * k = 0 := by omega
        rw [bchCoef, bchCoef, bchCoef, if_pos (by omega : 2 * (k + 1) ≤ N + 2), if_neg h5,
          if_pos h3, h6, h7]
        have hNk : ((N + 2 : ℕ) : ℚ) = 2 * ((k : ℚ) + 1) := by
          rw [h4]; push_cast; ring
        rw [hNk]
        simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      · have h5 : ¬ (2 * (k + 1) ≤ N + 1) := by omega
        have h6 : ¬ (2 * (k + 1) ≤ N + 2) := by omega
        have h7 : ¬ (2 * k ≤ N) := by omega
        rw [bchCoef, bchCoef, bchCoef, if_neg h5, if_neg h6, if_neg h7]
        ring

lemma bchR_rec (hcd : Commute c d) (N : ℕ) :
    ((N + 2 : ℕ) : ℚ) • bchR c d (N + 2) = d * bchR c d (N + 1) + c * bchR c d N := by
  have hD : d * bchR c d (N + 1)
      = ∑ j ∈ range (N + 3), bchCoef (N + 1) j • (c ^ j * d ^ (N + 2 - 2 * j)) := by
    rw [bchR, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show bchCoef (N + 1) (N + 2) = 0 from by rw [bchCoef, if_neg (by omega)]]
    simp only [zero_smul, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj2 : 2 * j ≤ N + 1
    · have hex : N + 2 - 2 * j = (N + 1 - 2 * j) + 1 := by omega
      rw [hex, mul_smul_comm, ← mul_assoc, (hcd.symm.pow_right j).eq, mul_assoc, ← pow_succ']
    · rw [bchCoef, if_neg hj2]
      simp
  have hE : c * bchR c d N
      = ∑ j ∈ range (N + 3), (if j = 0 then 0 else bchCoef N (j - 1)) •
          (c ^ j * d ^ (N + 2 - 2 * j)) := by
    rw [bchR, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_range_succ' _ (N + 2), Finset.sum_range_succ]
    rw [show bchCoef N (N + 1 + 1 - 1) = 0 from by rw [bchCoef, if_neg (by omega)]]
    simp only [Nat.succ_ne_zero, if_false, zero_smul, add_zero, Nat.add_sub_cancel, reduceIte]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hex : N + 2 - 2 * (j + 1) = N - 2 * j := by omega
    rw [hex, mul_smul_comm, ← mul_assoc, ← pow_succ']
  have hF : ((N + 2 : ℕ) : ℚ) • bchR c d (N + 2)
      = ∑ j ∈ range (N + 3), (((N + 2 : ℕ) : ℚ) * bchCoef (N + 2) j) •
          (c ^ j * d ^ (N + 2 - 2 * j)) := by
    rw [bchR, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  rw [hF, hD, hE, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [← add_smul, bchCoef_rec]

/-- Cancelling a nonzero rational scalar. -/
lemma smul_left_cancel_rat {k : ℚ} (hk : k ≠ 0) {x y : A} (h : k • x = k • y) : x = y := by
  have h2 := congrArg (fun z : A => k⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hk] using h2

/-- The key graded identity: the homogeneous components of `exp a * exp b` and of
`exp (a+b) * exp (c/2)` agree. -/
lemma bchL_eq_bchR (hc : c = a * b - b * a) (hac : Commute a c) (hbc : Commute b c) (N : ℕ) :
    bchL a b N = bchR c (a + b) N := by
  have hcd : Commute c (a + b) := (hac.add_left hbc).symm
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [bchL_zero, bchR_zero]
    | 1 => rw [bchL_one, bchR_one]
    | (n + 2) =>
      have h1 := ih n (by omega)
      have h2 := ih (n + 1) (by omega)
      refine smul_left_cancel_rat (k := ((n + 2 : ℕ) : ℚ)) (by positivity) ?_
      rw [bchL_rec hc hac, bchR_rec hcd, h1, h2]

/-- If `a ^ K = 0 = b ^ K`, then all homogeneous components of degree `≥ 2K` vanish. -/
lemma bchL_eq_zero {K N : ℕ} (hKa : a ^ K = 0) (hKb : b ^ K = 0) (hN : 2 * K ≤ N) :
    bchL a b N = 0 := by
  refine Finset.sum_eq_zero fun m hm => ?_
  rcases le_or_gt K m with h | h
  · rw [pow_eq_zero_of_le h hKa, zero_mul, smul_zero]
  · rw [pow_eq_zero_of_le (by omega : K ≤ N - m) hKb, mul_zero, smul_zero]

/-- The commutator of two nilpotent elements with central commutator is nilpotent. -/
lemma commutator_pow_eq_zero (hc : c = a * b - b * a) (hac : Commute a c) (hbc : Commute b c)
    {K : ℕ} (hK : a ^ K = 0) : c ^ K = 0 := by
  have key : ∀ i, i ≤ K → a ^ (K - i) * c ^ i = 0 := by
    intro i
    induction i with
    | zero => intro _; simp [hK]
    | succ i ih =>
      intro hi
      have ihz := ih (by omega)
      obtain ⟨n, hn⟩ : ∃ n, K - i = n + 1 := ⟨K - i - 1, by omega⟩
      rw [hn] at ihz
      have hn' : K - (i + 1) = n := by omega
      have hcb : Commute (c ^ i) b := hbc.symm.pow_left i
      have hac' : a ^ n * c ^ i = c ^ i * a ^ n := (hac.pow_pow n i).eq
      have e2 : c * a ^ n * c ^ i = c ^ (i + 1) * a ^ n := by
        rw [mul_assoc, hac', ← mul_assoc, ← pow_succ']
      have e1 : b * (a ^ (n + 1) * c ^ i)
          = a ^ (n + 1) * c ^ i * b - ((n : ℚ) + 1) • (c ^ (i + 1) * a ^ n) := by
        rw [← mul_assoc, mul_pow_succ_comm_of_central hc hac, sub_mul, smul_mul_assoc, e2,
          mul_assoc, hcb.symm.eq, ← mul_assoc]
      rw [ihz, mul_zero, zero_mul, zero_sub, eq_comm, neg_eq_zero] at e1
      have h0 : c ^ (i + 1) * a ^ n = 0 := by
        refine smul_left_cancel_rat (k := ((n : ℚ) + 1)) (by positivity) ?_
        rw [smul_zero]
        exact e1
      rw [hn', (hac.pow_pow n (i + 1)).eq, h0]
  simpa using key K le_rfl

lemma bchCoef_zero_ne_zero (N : ℕ) : bchCoef N 0 ≠ 0 := by
  rw [bchCoef, if_pos (by omega)]
  simp [Nat.factorial_ne_zero]

/-- Downward induction on the power of `c`, used to show that `a + b` is nilpotent. -/
lemma aux_pow_mul_eq_zero {r M : ℕ} (hcr : c ^ r = 0) (hR : ∀ N, M ≤ N → bchR c d N = 0) :
    ∀ t, t ≤ r → ∀ N, M + 2 * t ≤ N → c ^ (r - t) * d ^ N = 0 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro htr N hN
    have hRN : bchR c d N = 0 := hR N (by omega)
    have expand : c ^ (r - t) * bchR c d N
        = ∑ j ∈ range (N + 1), bchCoef N j • (c ^ (r - t + j) * d ^ (N - 2 * j)) := by
      rw [bchR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm, ← mul_assoc, ← pow_add]
    rw [hRN, mul_zero] at expand
    rw [Finset.sum_range_succ' _ N] at expand
    have hzero : ∑ j ∈ range N, bchCoef N (j + 1) •
        (c ^ (r - t + (j + 1)) * d ^ (N - 2 * (j + 1))) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases le_or_gt (j + 1) t with h | h
      · have h1 : t - (j + 1) < t := by omega
        have h2 : t - (j + 1) ≤ r := by omega
        have h3 : M + 2 * (t - (j + 1)) ≤ N - 2 * (j + 1) := by omega
        have h4 := ih (t - (j + 1)) h1 h2 (N - 2 * (j + 1)) h3
        have hexp : r - (t - (j + 1)) = r - t + (j + 1) := by omega
        rw [hexp] at h4
        rw [h4, smul_zero]
      · have h5 : c ^ (r - t + (j + 1)) = 0 := pow_eq_zero_of_le (by omega) hcr
        rw [h5, zero_mul, smul_zero]
    rw [hzero, zero_add] at expand
    simp only [Nat.add_zero, Nat.mul_zero, Nat.sub_zero] at expand
    refine smul_left_cancel_rat (bchCoef_zero_ne_zero N) ?_
    rw [smul_zero]
    exact expand.symm

/-- Assembling the graded components of `exp a * exp b`. -/
lemma exp_mul_exp_eq_sum_bchL {K : ℕ} (hKa : a ^ K = 0) (hKb : b ^ K = 0) :
    IsNilpotent.exp a * IsNilpotent.exp b = ∑ N ∈ range (2 * K), bchL a b N := by
  classical
  have hprod : IsNilpotent.exp a * IsNilpotent.exp b
      = ∑ p ∈ range K ×ˢ range K, ((p.1 ! : ℚ) * (p.2 ! : ℚ))⁻¹ • (a ^ p.1 * b ^ p.2) := by
    rw [IsNilpotent.exp_eq_sum hKa, IsNilpotent.exp_eq_sum hKb, Finset.sum_mul_sum,
      Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, mul_inv]
  have hmaps : ∀ p ∈ range K ×ˢ range K, p.1 + p.2 ∈ range (2 * K) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  rw [hprod, ← Finset.sum_fiberwise_of_maps_to hmaps
    (fun p => ((p.1 ! : ℚ) * (p.2 ! : ℚ))⁻¹ • (a ^ p.1 * b ^ p.2))]
  refine Finset.sum_congr rfl fun N _ => ?_
  have hsub : ∑ p ∈ (range K ×ˢ range K) with p.1 + p.2 = N,
        ((p.1 ! : ℚ) * (p.2 ! : ℚ))⁻¹ • (a ^ p.1 * b ^ p.2)
      = ∑ p ∈ Finset.antidiagonal N, ((p.1 ! : ℚ) * (p.2 ! : ℚ))⁻¹ • (a ^ p.1 * b ^ p.2) := by
    refine Finset.sum_subset ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      rw [Finset.mem_antidiagonal]
      exact hp.2
    · intro p hp hp2
      rw [Finset.mem_antidiagonal] at hp
      have hno : ¬ (p.1 < K ∧ p.2 < K) := by
        intro hcon
        exact hp2 (by
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨hcon.1, hcon.2⟩, hp⟩)
      rcases not_and_or.mp hno with h | h
      · rw [pow_eq_zero_of_le (not_lt.mp h) hKa, zero_mul, smul_zero]
      · rw [pow_eq_zero_of_le (not_lt.mp h) hKb, mul_zero, smul_zero]
  rw [hsub, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, bchL]

/-- Assembling the graded components of `exp d * exp (c/2)`. -/
lemma exp_mul_exp_eq_sum_bchR (hcd : Commute c d) {K : ℕ} (hKc : c ^ K = 0) (hKd : d ^ K = 0) :
    IsNilpotent.exp d * IsNilpotent.exp ((2⁻¹ : ℚ) • c) = ∑ N ∈ range (3 * K), bchR c d N := by
  classical
  have hKc' : ((2⁻¹ : ℚ) • c) ^ K = 0 := by rw [smul_pow, hKc, smul_zero]
  have hprod : IsNilpotent.exp d * IsNilpotent.exp ((2⁻¹ : ℚ) • c)
      = ∑ p ∈ range K ×ˢ range K,
          ((p.1 ! : ℚ) * (p.2 ! : ℚ) * 2 ^ p.2)⁻¹ • (c ^ p.2 * d ^ p.1) := by
    rw [IsNilpotent.exp_eq_sum hKd, IsNilpotent.exp_eq_sum hKc', Finset.sum_mul_sum,
      Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_pow, smul_smul, smul_mul_smul_comm, (hcd.pow_pow j i).eq]
    congr 1
    rw [inv_pow]
    field_simp
  have hmaps : ∀ p ∈ range K ×ˢ range K, p.1 + 2 * p.2 ∈ range (3 * K) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  rw [hprod, ← Finset.sum_fiberwise_of_maps_to hmaps
    (fun p => ((p.1 ! : ℚ) * (p.2 ! : ℚ) * 2 ^ p.2)⁻¹ • (c ^ p.2 * d ^ p.1))]
  refine Finset.sum_congr rfl fun N _ => ?_
  have hB : ∑ j ∈ (range (N + 1)) with (2 * j ≤ N ∧ j < K ∧ N - 2 * j < K),
        bchCoef N j • (c ^ j * d ^ (N - 2 * j)) = bchR c d N := by
    rw [bchR]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro j hj hj2
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hj hj2
    by_cases h1 : 2 * j ≤ N
    · rcases lt_or_ge j K with h2 | h2
      · have h3 : K ≤ N - 2 * j := not_lt.mp (hj2 hj h1 h2)
        rw [pow_eq_zero_of_le h3 hKd, mul_zero, smul_zero]
      · rw [pow_eq_zero_of_le h2 hKc, zero_mul, smul_zero]
    · rw [bchCoef, if_neg h1, zero_smul]
  rw [← hB]
  refine Finset.sum_nbij' (fun p => p.2) (fun j => (N - 2 * j, j)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hj ⊢
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    have h5 : N - 2 * p.2 = p.1 := by omega
    simp [h5]
  · intro j _
    simp
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    dsimp only
    have hp1 : N - 2 * p.2 = p.1 := by omega
    rw [bchCoef, if_pos (by omega), hp1]

end

/-- **Baker–Campbell–Hausdorff, special case of a central commutator.**

If `a` and `b` are nilpotent elements of a `ℚ`-algebra whose commutator `[a,b] = ab - ba`
commutes with both `a` and `b`, then `exp a * exp b = exp (a + b + ½[a,b])`. -/
theorem bcH_special {A : Type*} [Ring A] [Algebra ℚ A] {a b : A}
    (ha : IsNilpotent a) (hb : IsNilpotent b)
    (hac : Commute a (a * b - b * a)) (hbc : Commute b (a * b - b * a)) :
    IsNilpotent.exp a * IsNilpotent.exp b
      = IsNilpotent.exp (a + b + (2⁻¹ : ℚ) • (a * b - b * a)) := by
  classical
  set c : A := a * b - b * a with hc
  obtain ⟨n₁, hn₁⟩ := ha
  obtain ⟨n₂, hn₂⟩ := hb
  set K : ℕ := max n₁ n₂ with hK
  have hKa : a ^ K = 0 := pow_eq_zero_of_le (le_max_left _ _) hn₁
  have hKb : b ^ K = 0 := pow_eq_zero_of_le (le_max_right _ _) hn₂
  have hKc : c ^ K = 0 := commutator_pow_eq_zero hc hac hbc hKa
  have hcd : Commute c (a + b) := (hac.add_left hbc).symm
  have hRzero : ∀ N, 2 * K ≤ N → bchR c (a + b) N = 0 := by
    intro N hN
    rw [← bchL_eq_bchR hc hac hbc, bchL_eq_zero hKa hKb hN]
  have hd : (a + b) ^ (4 * K) = 0 := by
    have h := aux_pow_mul_eq_zero hKc hRzero K le_rfl (4 * K) (by omega)
    simpa using h
  have hKc2 : c ^ (4 * K) = 0 := pow_eq_zero_of_le (by omega) hKc
  have e1 : IsNilpotent.exp a * IsNilpotent.exp b = ∑ N ∈ range (2 * K), bchL a b N :=
    exp_mul_exp_eq_sum_bchL hKa hKb
  have e2 : IsNilpotent.exp (a + b) * IsNilpotent.exp ((2⁻¹ : ℚ) • c)
      = ∑ N ∈ range (3 * (4 * K)), bchR c (a + b) N :=
    exp_mul_exp_eq_sum_bchR hcd hKc2 hd
  have e3 : ∑ N ∈ range (2 * K), bchL a b N = ∑ N ∈ range (3 * (4 * K)), bchR c (a + b) N := by
    rw [Finset.sum_congr rfl (fun N _ => bchL_eq_bchR hc hac hbc N)]
    have hsub : range (2 * K) ⊆ range (3 * (4 * K)) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    refine Finset.sum_subset hsub ?_
    intro N _ hN2
    simp only [Finset.mem_range, not_lt] at hN2
    exact hRzero N hN2
  have hnil_d : IsNilpotent (a + b) := ⟨4 * K, hd⟩
  have hnil_c : IsNilpotent ((2⁻¹ : ℚ) • c) := ⟨4 * K, by rw [smul_pow, hKc2, smul_zero]⟩
  rw [e1, e3, ← e2, IsNilpotent.exp_add_of_commute (hcd.symm.smul_right _) hnil_d hnil_c]

open Matrix in
/-- The hypotheses of `QPhys.bcH_special` are not vacuous: they hold, with a nonzero
commutator, for the standard Heisenberg (strictly upper triangular `3 × 3`) matrices. -/
theorem bcH_special_heisenberg :
    ∃ a b : Matrix (Fin 3) (Fin 3) ℚ,
      IsNilpotent a ∧ IsNilpotent b ∧ Commute a (a * b - b * a) ∧ Commute b (a * b - b * a) ∧
        a * b - b * a ≠ 0 ∧
        IsNilpotent.exp a * IsNilpotent.exp b
          = IsNilpotent.exp (a + b + (2⁻¹ : ℚ) • (a * b - b * a)) := by
  refine ⟨!![0,1,0;0,0,0;0,0,0], !![0,0,0;0,0,1;0,0,0], ⟨2, ?_⟩, ⟨2, ?_⟩, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]
  · show _ * _ = _ * _
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · show _ * _ = _ * _
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · intro h
    have h2 := congrFun (congrFun h 0) 2
    simp at h2
  · exact bcH_special ⟨2, by ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]⟩
      ⟨2, by ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]⟩
      (by show _ * _ = _ * _; ext i j; fin_cases i <;> fin_cases j <;> simp)
      (by show _ * _ = _ * _; ext i j; fin_cases i <;> fin_cases j <;> simp)

end QPhys

