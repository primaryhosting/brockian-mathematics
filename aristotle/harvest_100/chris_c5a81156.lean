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

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise lower bounds on the communication complexity of set disjointness
`DISJ_n` on `n`-element ground sets.

* `CS.disjointness_lb` : the main target.  Any *public-coin randomised one-way*
  protocol that computes `DISJ_n` with error probability at most `1/8` on every
  input must communicate `c` bits with `n ≤ 6 * (c + 1)`, i.e. `c = Ω(n)`.
* `CS.disjointness_lb_deterministic` : any *deterministic two-way* protocol
  computing `DISJ_n` has depth (communication cost) at least `n`.
* `CS.disjointness_lb_two_way` : any randomised two-way protocol whose error
  probability on each input is smaller than `4 ^ (-n)` has depth at least `n`.
* `CS.disjointness_upper` : the hypotheses are not vacuous — a one-way protocol
  with `n` bits of communication and zero error always exists.

The proof of the main theorem is the standard argument: averaging over the public
randomness fixes a deterministic one-way protocol that is correct on average over
the hard distribution (`x` uniform, `y` a uniformly random singleton `{i}`); the
protocol's message determines a decoding `z` of Alice's input, so most inputs `x`
lie in a Hamming ball of radius `n / 4` around one of the `2 ^ c` decodings, and a
volume bound for Hamming balls forces `2 ^ c` to be exponentially large in `n`.
Note that `DISJ (x, {i}) = ¬ x i`, i.e. the index function reduces to disjointness.
-/

open Finset

namespace CS

/-- Inputs: subsets of `Fin n`, encoded as Boolean vectors. -/
abbrev Inp (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Set disjointness: `true` iff the two subsets of `Fin n` are disjoint. -/
def disj (x y : Inp n) : Bool := decide (∀ i, x i = false ∨ y i = false)

/-- The singleton subset `{i}`. -/
def sing (i : Fin n) : Inp n := fun j => decide (j = i)

lemma disj_sing (x : Inp n) (i : Fin n) : disj x (sing i) = !(x i) := by
  cases hx : x i <;> simp [disj, sing, hx]
  intro j
  by_cases h : j = i
  · subst h; simp [hx]
  · exact Or.inr h

/-! ### A counting bound for Hamming balls -/

/-- `∑_x 3 ^ (#agreements of x with z) = 4 ^ n`. -/
lemma agree_sum (z : Inp n) :
    ∑ x : Inp n, 3 ^ ((univ.filter (fun i => x i = z i)).card) = 4 ^ n := by
  have h := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset Bool))
    (fun i b => if b = z i then (3 : ℕ) else 1)
  simp only [Fintype.piFinset_univ] at h
  have key : ∀ x : Inp n, ∏ i, (if x i = z i then (3 : ℕ) else 1)
      = 3 ^ ((univ.filter (fun i => x i = z i)).card) := by
    intro x
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  simp only [key] at h
  rw [← h]
  have hb : ∀ i : Fin n,
      ((if true = z i then (3 : ℕ) else 1) + if false = z i then (3 : ℕ) else 1) = 4 := by
    intro i; cases z i <;> simp
  simp only [Fintype.sum_bool]
  rw [Finset.prod_congr rfl (fun i _ => hb i)]
  simp

/-- Volume bound for Hamming balls: a set of vectors all within Hamming distance
`k` of a fixed centre `z` has size at most `4 ^ n / 3 ^ (n - k)`. -/
lemma ball_card_bound (z : Inp n) (S : Finset (Inp n)) (k : ℕ)
    (hS : ∀ x ∈ S, ((univ.filter (fun i => x i ≠ z i)).card) ≤ k) :
    3 ^ (n - k) * S.card ≤ 4 ^ n := by
  have hagree : ∀ x ∈ S, 3 ^ (n - k) ≤ 3 ^ ((univ.filter (fun i => x i = z i)).card) := by
    intro x hx
    have hsplit : (univ.filter (fun i => x i = z i)).card
        + (univ.filter (fun i => ¬ (x i = z i))).card = (univ : Finset (Fin n)).card :=
      Finset.card_filter_add_card_filter_not _
    have hcard : (univ : Finset (Fin n)).card = n := by simp
    have := hS x hx
    have hle : n - k ≤ (univ.filter (fun i => x i = z i)).card := by
      simp only [ne_eq] at this
      omega
    exact Nat.pow_le_pow_right (by norm_num) hle
  calc 3 ^ (n - k) * S.card = ∑ _x ∈ S, 3 ^ (n - k) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ S, 3 ^ ((univ.filter (fun i => x i = z i)).card) :=
        Finset.sum_le_sum hagree
    _ ≤ ∑ x : Inp n, 3 ^ ((univ.filter (fun i => x i = z i)).card) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 4 ^ n := agree_sum z

/-! ### An arithmetic lemma -/

lemma pow_ineq (m N : ℕ) (h : 6 * m < N) : 16 ^ (N + m) ≤ 27 ^ N := by
  obtain ⟨t, ht⟩ : ∃ t, N = 6 * m + 1 + t := ⟨N - (6 * m + 1), by omega⟩
  subst ht
  have h1 : (16 : ℕ) ^ 7 ≤ 27 ^ 6 := by norm_num
  have h2 : ((16 : ℕ) ^ 7) ^ m ≤ (27 ^ 6) ^ m := Nat.pow_le_pow_left h1 m
  have h3 : (16 : ℕ) ^ t ≤ 27 ^ t := Nat.pow_le_pow_left (by norm_num) t
  have e1 : (16 : ℕ) ^ (6 * m + 1 + t + m) = 16 * ((16 ^ 7) ^ m * 16 ^ t) := by
    rw [← pow_mul]
    ring
  have e2 : (27 : ℕ) ^ (6 * m + 1 + t) = 27 * ((27 ^ 6) ^ m * 27 ^ t) := by
    rw [← pow_mul]
    ring
  rw [e1, e2]
  have : ((16 : ℕ) ^ 7) ^ m * 16 ^ t ≤ (27 ^ 6) ^ m * 27 ^ t := Nat.mul_le_mul h2 h3
  calc 16 * (((16 : ℕ) ^ 7) ^ m * 16 ^ t) ≤ 16 * ((27 ^ 6) ^ m * 27 ^ t) := by
        exact Nat.mul_le_mul_left _ this
    _ ≤ 27 * ((27 ^ 6) ^ m * 27 ^ t) := by
        exact Nat.mul_le_mul_right _ (by norm_num)

/-! ### Randomised one-way protocols -/

/-- A deterministic one-way protocol with `c` bits of communication: Alice sends
a `c`-bit message `msg x`, and Bob outputs `out (msg x) y`. -/
structure OneWay (n c : ℕ) where
  msg : Inp n → Fin (2 ^ c)
  out : Fin (2 ^ c) → Inp n → Bool

/-- The output of a one-way protocol. -/
def OneWay.eval {n c : ℕ} (p : OneWay n c) (x y : Inp n) : Bool := p.out (p.msg x) y

/-- **Main theorem.**  Set disjointness on an `n`-element ground set requires
`Ω(n)` bits of communication for randomised (public-coin, one-way) protocols
with error probability at most `1/8`.

Here `P : Fin N → OneWay n c` is a public-coin randomised protocol: the players
share a uniformly random `r : Fin N` and then run the deterministic `c`-bit
one-way protocol `P r`.  The hypothesis `herr` says that for every input pair
`(x, y)` the protocol errs with probability at most `1/8`.  The conclusion
`n ≤ 6 * (c + 1)`, i.e. `c ≥ n/6 - 1`, is a linear lower bound on the number of
communicated bits. -/
theorem disjointness_lb {n c N : ℕ} (hN : 0 < N) (P : Fin N → OneWay n c)
    (herr : ∀ x y : Inp n,
      8 * ((univ.filter (fun r => (P r).eval x y ≠ disj x y)).card) ≤ N) :
    n ≤ 6 * (c + 1) := by
  classical
  have hNe : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  -- the error indicator of the protocol `P r` on the input pair `(x, {i})`
  set E : Fin N → Inp n → Fin n → ℕ :=
    fun r x i => if (P r).eval x (sing i) ≠ disj x (sing i) then 1 else 0 with hE
  have hcnt : ∀ (x : Inp n) (i : Fin n),
      ∑ r, E r x i
        = (univ.filter (fun r => (P r).eval x (sing i) ≠ disj x (sing i))).card := by
    intro x i
    rw [Finset.card_filter]
  have hcard2 : (univ : Finset (Inp n)).card = 2 ^ n := by
    rw [Finset.card_univ]
    simp
  -- Step 1: average over the public randomness
  have htot : 8 * (∑ r, ∑ x : Inp n, ∑ i : Fin n, E r x i) ≤ N * (2 ^ n * n) := by
    have hswap : (∑ r, ∑ x : Inp n, ∑ i : Fin n, E r x i)
        = ∑ x : Inp n, ∑ i : Fin n, ∑ r, E r x i := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    rw [hswap, Finset.mul_sum]
    have hrow : ∀ x : Inp n, 8 * (∑ i : Fin n, ∑ r, E r x i) ≤ n * N := by
      intro x
      rw [Finset.mul_sum]
      calc ∑ i : Fin n, 8 * ∑ r, E r x i ≤ ∑ _i : Fin n, N := by
            refine Finset.sum_le_sum ?_
            intro i _
            rw [hcnt]
            exact herr x (sing i)
        _ = n * N := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    calc ∑ x : Inp n, 8 * (∑ i : Fin n, ∑ r, E r x i)
        ≤ ∑ _x : Inp n, (n * N) := Finset.sum_le_sum fun x _ => hrow x
      _ = 2 ^ n * (n * N) := by rw [Finset.sum_const, hcard2, smul_eq_mul]
      _ = N * (2 ^ n * n) := by ring
  have hpre : (∑ r, 8 * ∑ x : Inp n, ∑ i : Fin n, E r x i)
      ≤ ∑ _r : Fin N, (2 ^ n * n) := by
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact htot
  obtain ⟨r₁, -, hr₁⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hpre
  -- Step 2: the fixed deterministic protocol and its decoding centres
  set p := P r₁ with hp
  set z : Fin (2 ^ c) → Inp n := fun m j => !(p.out m (sing j)) with hz
  set d : Inp n → ℕ := fun x => (univ.filter (fun i => x i ≠ z (p.msg x) i)).card with hd
  have hEd : ∀ x : Inp n, ∑ i : Fin n, E r₁ x i = d x := by
    intro x
    show ∑ i, E r₁ x i = (univ.filter (fun i => x i ≠ z (p.msg x) i)).card
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hiff : ((P r₁).eval x (sing i) ≠ disj x (sing i)) ↔ (x i ≠ z (p.msg x) i) := by
      rw [disj_sing, hz]
      simp only [OneWay.eval, ← hp]
      cases hb : x i <;> cases ha : p.out (p.msg x) (sing i) <;> simp
    simp only [hE]
    by_cases hcase : (P r₁).eval x (sing i) ≠ disj x (sing i)
    · rw [if_pos hcase, if_pos (hiff.mp hcase)]
    · rw [if_neg hcase, if_neg (fun h => hcase (hiff.mpr h))]
  have hsumd : 8 * (∑ x : Inp n, d x) ≤ 2 ^ n * n := by
    calc 8 * (∑ x : Inp n, d x) = 8 * ∑ x : Inp n, ∑ i : Fin n, E r₁ x i := by
          rw [Finset.sum_congr rfl (fun x _ => hEd x)]
      _ ≤ 2 ^ n * n := hr₁
  -- Step 3: Markov: at least half the inputs are decoded to within Hamming distance n/4
  set G : Finset (Inp n) := univ.filter (fun x => 4 * d x ≤ n) with hG
  have hGcard : 2 ^ n < 2 * G.card := by
    set B : Finset (Inp n) := univ.filter (fun x => ¬ (4 * d x ≤ n)) with hB
    have hsplit : G.card + B.card = 2 ^ n := by
      rw [hG, hB, Finset.card_filter_add_card_filter_not, hcard2]
    have hBd : ∑ _x ∈ B, (n + 1) ≤ ∑ x ∈ B, 4 * d x := by
      refine Finset.sum_le_sum ?_
      intro x hx
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      omega
    have h2 : ∑ x ∈ B, d x ≤ ∑ x : Inp n, d x :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have key : 2 * (B.card * (n + 1)) ≤ 2 ^ n * n := by
      have e1 : ∑ _x ∈ B, (n + 1) = B.card * (n + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
      have e2 : ∑ x ∈ B, 4 * d x = 4 * ∑ x ∈ B, d x := by rw [Finset.mul_sum]
      rw [e1, e2] at hBd
      omega
    have hBlt : 2 * B.card < 2 ^ n := by
      by_contra hcon
      push_neg at hcon
      have hmul : 2 ^ n * (n + 1) ≤ (2 * B.card) * (n + 1) :=
        Nat.mul_le_mul_right _ hcon
      have h2n : 0 < 2 ^ n := pow_pos (by norm_num) n
      have : 2 ^ n * (n + 1) ≤ 2 ^ n * n := by
        calc 2 ^ n * (n + 1) ≤ (2 * B.card) * (n + 1) := hmul
          _ = 2 * (B.card * (n + 1)) := by ring
          _ ≤ 2 ^ n * n := key
      have := Nat.le_of_mul_le_mul_left this h2n
      omega
    omega
  -- Step 4: the good inputs are covered by 2 ^ c Hamming balls of radius n / 4
  have hfib : G.card = ∑ m : Fin (2 ^ c), (G.filter (fun x => p.msg x = m)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  have hball : ∀ m : Fin (2 ^ c),
      3 ^ (n - n / 4) * (G.filter (fun x => p.msg x = m)).card ≤ 4 ^ n := by
    intro m
    refine ball_card_bound (z m) _ (n / 4) ?_
    intro x hx
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hrw : (univ.filter (fun i => x i ≠ (z m) i)).card = d x := by
      rw [hd, ← hx2]
    rw [hrw]
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have hcover : 3 ^ (n - n / 4) * G.card ≤ 2 ^ c * 4 ^ n := by
    rw [hfib, Finset.mul_sum]
    calc ∑ m : Fin (2 ^ c), 3 ^ (n - n / 4) * (G.filter (fun x => p.msg x = m)).card
        ≤ ∑ _m : Fin (2 ^ c), 4 ^ n := Finset.sum_le_sum fun m _ => hball m
      _ = 2 ^ c * 4 ^ n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- Step 5: arithmetic
  set k := n / 4 with hk
  have hk4 : 4 * k ≤ n := by omega
  have hkn : k ≤ n := by omega
  have h3pos : 0 < 3 ^ (n - k) := pow_pos (by norm_num) _
  have hA : 3 ^ (n - k) * 2 ^ n < 2 ^ (c + 1) * 4 ^ n := by
    calc 3 ^ (n - k) * 2 ^ n < 3 ^ (n - k) * (2 * G.card) := by
          exact Nat.mul_lt_mul_of_pos_left hGcard h3pos
      _ = 2 * (3 ^ (n - k) * G.card) := by ring
      _ ≤ 2 * (2 ^ c * 4 ^ n) := by
          exact Nat.mul_le_mul_left _ hcover
      _ = 2 ^ (c + 1) * 4 ^ n := by ring
  have hpow4 : (3 ^ (n - k) * 2 ^ n) ^ 4 < (2 ^ (c + 1) * 4 ^ n) ^ 4 :=
    Nat.pow_lt_pow_left hA (by norm_num)
  have e2n : (2 : ℕ) ^ (n * 4) = 16 ^ n := by
    rw [pow_mul']
    norm_num
  have hL : 27 ^ n * 16 ^ n ≤ (3 ^ (n - k) * 2 ^ n) ^ 4 := by
    have e1 : (3 ^ (n - k) * 2 ^ n) ^ 4 = 3 ^ ((n - k) * 4) * 16 ^ n := by
      rw [mul_pow, ← pow_mul, ← pow_mul, e2n]
    have e4 : (27 : ℕ) ^ n = 3 ^ (n * 3) := by
      rw [pow_mul']
      norm_num
    have e5 : n * 3 ≤ (n - k) * 4 := by omega
    rw [e1, e4]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) e5)
  have hR : (2 ^ (c + 1) * 4 ^ n) ^ 4 = (16 ^ (c + 1) * 16 ^ n) * 16 ^ n := by
    have h16 : (16 : ℕ) ^ n * 16 ^ n = 256 ^ n := by
      rw [← mul_pow]
      norm_num
    have h2c : (2 : ℕ) ^ ((c + 1) * 4) = 16 ^ (c + 1) := by
      rw [pow_mul']
      norm_num
    have h4n : (4 : ℕ) ^ (n * 4) = 256 ^ n := by
      rw [pow_mul']
      norm_num
    rw [mul_assoc, h16, mul_pow, ← pow_mul, ← pow_mul, h2c, h4n]
  have hfinal : 27 ^ n < 16 ^ (n + (c + 1)) := by
    have hlt : 27 ^ n * 16 ^ n < (16 ^ (c + 1) * 16 ^ n) * 16 ^ n := by
      calc 27 ^ n * 16 ^ n ≤ (3 ^ (n - k) * 2 ^ n) ^ 4 := hL
        _ < (2 ^ (c + 1) * 4 ^ n) ^ 4 := hpow4
        _ = (16 ^ (c + 1) * 16 ^ n) * 16 ^ n := hR
    have := Nat.lt_of_mul_lt_mul_right hlt
    calc 27 ^ n < 16 ^ (c + 1) * 16 ^ n := this
      _ = 16 ^ (n + (c + 1)) := by rw [← pow_add, Nat.add_comm]
  by_contra hcon
  push_neg at hcon
  have := pow_ineq (c + 1) n hcon
  omega

/-- Non-vacuity of the hypotheses of `disjointness_lb`: Alice can always send her
whole `n`-bit input, giving a one-way protocol with `n` bits of communication and
no error at all. -/
theorem disjointness_upper (n : ℕ) : ∃ p : OneWay n n, ∀ x y : Inp n, p.eval x y = disj x y := by
  classical
  have hcard : Fintype.card (Inp n) = 2 ^ n := by simp
  obtain e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨fun x => e x, fun m y => disj (e.symm m) y⟩, ?_⟩
  intro x y
  simp [OneWay.eval]

/-! ### Deterministic two-way protocols -/

/-- Deterministic two-way communication protocols as protocol trees. -/
inductive Prot (n : ℕ) : Type where
  | leaf : Bool → Prot n
  | alice : (Inp n → Bool) → Prot n → Prot n → Prot n
  | bob : (Inp n → Bool) → Prot n → Prot n → Prot n

/-- The communication cost of a protocol: the depth of the protocol tree. -/
def Prot.depth : Prot n → ℕ
  | .leaf _ => 0
  | .alice _ p q => max p.depth q.depth + 1
  | .bob _ p q => max p.depth q.depth + 1

/-- The output of a protocol on a pair of inputs. -/
def Prot.eval : Prot n → Inp n → Inp n → Bool
  | .leaf b, _, _ => b
  | .alice f p q, x, y => if f x then p.eval x y else q.eval x y
  | .bob f p q, x, y => if f y then p.eval x y else q.eval x y

/-- The fooling-set bound: a fooling set of `1`-inputs has size at most
`2 ^ (communication cost)`. -/
lemma fooling_card (p : Prot n) (S : Finset (Inp n × Inp n))
    (h1 : ∀ q ∈ S, p.eval q.1 q.2 = true)
    (h2 : ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' → p.eval q.1 q'.2 = false ∨ p.eval q'.1 q.2 = false) :
    S.card ≤ 2 ^ p.depth := by
  classical
  induction p generalizing S with
  | leaf b =>
    simp only [Prot.depth, pow_zero]
    rw [Finset.card_le_one]
    intro a ha b' hb'
    by_contra hne
    have hb := h1 a ha
    simp only [Prot.eval] at hb
    rcases h2 a ha b' hb' hne with h | h <;> simp [Prot.eval, hb] at h
  | alice f p q ihp ihq =>
    have hcard : (S.filter (fun s => f s.1 = true)).card
        + (S.filter (fun s => ¬ (f s.1 = true))).card = S.card :=
      Finset.card_filter_add_card_filter_not _
    have hp : (S.filter (fun s => f s.1 = true)).card ≤ 2 ^ p.depth := by
      refine ihp _ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter] at hs
        have := h1 s hs.1
        simp only [Prot.eval, hs.2, if_true] at this
        exact this
      · intro s hs s' hs' hne
        simp only [Finset.mem_filter] at hs hs'
        have := h2 s hs.1 s' hs'.1 hne
        simp only [Prot.eval, hs.2, hs'.2, if_true] at this
        exact this
    have hq : (S.filter (fun s => ¬ (f s.1 = true))).card ≤ 2 ^ q.depth := by
      refine ihq _ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter, Bool.not_eq_true] at hs
        have := h1 s hs.1
        simp only [Prot.eval, hs.2] at this
        simpa using this
      · intro s hs s' hs' hne
        simp only [Finset.mem_filter, Bool.not_eq_true] at hs hs'
        have := h2 s hs.1 s' hs'.1 hne
        simp only [Prot.eval, hs.2, hs'.2] at this
        simpa using this
    have h1' : (2 : ℕ) ^ p.depth ≤ 2 ^ (max p.depth q.depth) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2' : (2 : ℕ) ^ q.depth ≤ 2 ^ (max p.depth q.depth) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    simp only [Prot.depth, pow_succ]
    omega
  | bob f p q ihp ihq =>
    have hcard : (S.filter (fun s => f s.2 = true)).card
        + (S.filter (fun s => ¬ (f s.2 = true))).card = S.card :=
      Finset.card_filter_add_card_filter_not _
    have hp : (S.filter (fun s => f s.2 = true)).card ≤ 2 ^ p.depth := by
      refine ihp _ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter] at hs
        have := h1 s hs.1
        simp only [Prot.eval, hs.2, if_true] at this
        exact this
      · intro s hs s' hs' hne
        simp only [Finset.mem_filter] at hs hs'
        have := h2 s hs.1 s' hs'.1 hne
        simp only [Prot.eval, hs.2, hs'.2, if_true] at this
        exact this
    have hq : (S.filter (fun s => ¬ (f s.2 = true))).card ≤ 2 ^ q.depth := by
      refine ihq _ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter, Bool.not_eq_true] at hs
        have := h1 s hs.1
        simp only [Prot.eval, hs.2] at this
        simpa using this
      · intro s hs s' hs' hne
        simp only [Finset.mem_filter, Bool.not_eq_true] at hs hs'
        have := h2 s hs.1 s' hs'.1 hne
        simp only [Prot.eval, hs.2, hs'.2] at this
        simpa using this
    have h1' : (2 : ℕ) ^ p.depth ≤ 2 ^ (max p.depth q.depth) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2' : (2 : ℕ) ^ q.depth ≤ 2 ^ (max p.depth q.depth) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    simp only [Prot.depth, pow_succ]
    omega

/-- **Deterministic lower bound.**  Any deterministic two-way protocol computing
set disjointness on an `n`-element ground set has communication cost `≥ n`. -/
theorem disjointness_lb_deterministic (p : Prot n) (hp : ∀ x y : Inp n, p.eval x y = disj x y) :
    n ≤ p.depth := by
  classical
  set S : Finset (Inp n × Inp n) :=
    Finset.image (fun x : Inp n => (x, fun i => !(x i))) univ with hS
  have hinj : Function.Injective (fun x : Inp n => (x, fun i => !(x i))) := by
    intro a b h
    exact congrArg Prod.fst h
  have hcard : S.card = 2 ^ n := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp
  have key : S.card ≤ 2 ^ p.depth := by
    refine fooling_card p S ?_ ?_
    · intro q hq
      simp only [hS, Finset.mem_image, Finset.mem_univ, true_and] at hq
      obtain ⟨x, rfl⟩ := hq
      simp only [hp, disj, decide_eq_true_eq]
      intro i
      cases hx : x i <;> simp
    · intro q hq q' hq' hne
      simp only [hS, Finset.mem_image, Finset.mem_univ, true_and] at hq hq'
      obtain ⟨x, rfl⟩ := hq
      obtain ⟨x', rfl⟩ := hq'
      have hxx : x ≠ x' := by
        intro h
        exact hne (by rw [h])
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
        by_contra hcon
        push_neg at hcon
        exact hxx (funext hcon)
      simp only [hp]
      cases hx : x i with
      | false =>
        right
        have hx' : x' i = true := by
          rw [hx] at hi
          simpa using Ne.symm hi
        simp only [disj, decide_eq_false_iff_not]
        push_neg
        exact ⟨i, by simp [hx'], by simp [hx]⟩
      | true =>
        left
        have hx' : x' i = false := by
          rw [hx] at hi
          simpa using Ne.symm hi
        simp only [disj, decide_eq_false_iff_not]
        push_neg
        exact ⟨i, by simp [hx], by simp [hx']⟩
  rw [hcard] at key
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp key

/-- **Randomised two-way protocols with tiny error.**  Any randomised two-way
protocol whose error probability on every input is smaller than `4 ^ (-n)` has
communication cost at least `n`. -/
theorem disjointness_lb_two_way {N : ℕ} (hN : 0 < N) (P : Fin N → Prot n) (d : ℕ)
    (hd : ∀ r, (P r).depth ≤ d)
    (herr : ∀ x y : Inp n,
      4 ^ n * ((univ.filter (fun r => (P r).eval x y ≠ disj x y)).card) < N) :
    n ≤ d := by
  classical
  set bad : Inp n × Inp n → Finset (Fin N) :=
    fun q => univ.filter (fun r => (P r).eval q.1 q.2 ≠ disj q.1 q.2) with hbad
  set B : Finset (Fin N) := univ.biUnion bad with hB
  have hBcard : B.card ≤ ∑ q : Inp n × Inp n, (bad q).card := Finset.card_biUnion_le
  have h4 : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have hpairs : (univ : Finset (Inp n × Inp n)).card = 4 ^ n := by
    rw [Finset.card_univ, Fintype.card_prod, h4]
    simp
  have hlt : ∀ q : Inp n × Inp n, 4 ^ n * (bad q).card < N := fun q => herr q.1 q.2
  have hsum : 4 ^ n * (∑ q : Inp n × Inp n, (bad q).card) ≤ 4 ^ n * (N - 1) := by
    rw [Finset.mul_sum]
    calc ∑ q : Inp n × Inp n, 4 ^ n * (bad q).card
        ≤ ∑ _q : Inp n × Inp n, (N - 1) := by
          refine Finset.sum_le_sum ?_
          intro q _
          have := hlt q
          omega
      _ = 4 ^ n * (N - 1) := by
          rw [Finset.sum_const, hpairs, smul_eq_mul]
  have hpos : 0 < (4 : ℕ) ^ n := pow_pos (by norm_num) n
  have hBlt : B.card < N := by
    have : (∑ q : Inp n × Inp n, (bad q).card) ≤ N - 1 := Nat.le_of_mul_le_mul_left hsum hpos
    omega
  obtain ⟨r, hr⟩ : ∃ r : Fin N, r ∉ B := by
    by_contra hcon
    push_neg at hcon
    have : (univ : Finset (Fin N)).card ≤ B.card :=
      Finset.card_le_card (fun r _ => hcon r)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hgood : ∀ x y : Inp n, (P r).eval x y = disj x y := by
    intro x y
    by_contra hne
    apply hr
    rw [hB]
    refine Finset.mem_biUnion.mpr ⟨(x, y), Finset.mem_univ _, ?_⟩
    simpa [hbad] using hne
  exact le_trans (disjointness_lb_deterministic (P r) hgood) (hd r)

end CS

