import Mathlib
import RequestProject.DisjointnessLb

/-!
# Deterministic two-way communication complexity of set disjointness

As a companion to `CS.disjointness_lb` (a linear lower bound for *randomized* one-way
protocols), this file formalises the general *two-way deterministic* model as protocol
trees and proves the classical fooling-set lower bound: any deterministic protocol
computing set disjointness on an `n`-element universe has cost at least `n`.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- Bitwise complement of a characteristic vector. -/
def negVec (a : Fin n → Bool) : Fin n → Bool := fun i => !(a i)

lemma Disj_negVec_self (a : Fin n → Bool) : Disj a (negVec a) = true := by
  simp [Disj, negVec]

lemma Disj_eq_false_of_mem {a b : Fin n → Bool} {i : Fin n} (h1 : a i = true)
    (h2 : b i = false) : Disj a (negVec b) = false := by
  simp only [Disj, negVec, decide_eq_false_iff_not, not_forall, not_not]
  exact ⟨i, h1, by simp [h2]⟩

/-- A deterministic two-party communication protocol tree: at each internal node either
Alice or Bob sends one bit, computed from her/his own input. -/
inductive Proto (n : ℕ) where
  | leaf : Bool → Proto n
  | alice : ((Fin n → Bool) → Bool) → (Bool → Proto n) → Proto n
  | bob : ((Fin n → Bool) → Bool) → (Bool → Proto n) → Proto n

namespace Proto

/-- The cost (depth, i.e. worst-case number of communicated bits) of a protocol. -/
def cost : Proto n → ℕ
  | leaf _ => 0
  | alice _ f => 1 + max (cost (f false)) (cost (f true))
  | bob _ f => 1 + max (cost (f false)) (cost (f true))

/-- The value output by a protocol on a pair of inputs. -/
def run : Proto n → (Fin n → Bool) → (Fin n → Bool) → Bool
  | leaf v, _, _ => v
  | alice g f, a, b => run (f (g a)) a b
  | bob g f, a, b => run (f (g b)) a b

/-- Fooling-set counting: if a protocol computes disjointness correctly on all pairs
`(a, negVec b)` with `a, b` in a set `A`, then `A` has at most `2 ^ cost` elements. -/
lemma card_le_two_pow_cost (p : Proto n) (A : Finset (Fin n → Bool))
    (h : ∀ a ∈ A, ∀ b ∈ A, run p a (negVec b) = Disj a (negVec b)) :
    A.card ≤ 2 ^ cost p := by
  induction p generalizing A with
  | leaf v =>
      refine le_trans (Finset.card_le_one.mpr ?_) (by simp [cost])
      intro a ha b hb
      by_contra hne
      have hv : v = true := by
        have := h a ha a ha
        rw [run, Disj_negVec_self] at this
        exact this
      obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
        by_contra hc
        push_neg at hc
        exact hne (funext hc)
      rcases hA : a i with _ | _ <;> rcases hB : b i with _ | _
      · exact hi (by rw [hA, hB])
      · have := h b hb a ha
        rw [run, Disj_eq_false_of_mem hB hA] at this
        rw [hv] at this
        exact Bool.noConfusion this
      · have := h a ha b hb
        rw [run, Disj_eq_false_of_mem hA hB] at this
        rw [hv] at this
        exact Bool.noConfusion this
      · exact hi (by rw [hA, hB])
  | alice g f ih =>
      classical
      have hsplit : (A.filter (fun a => g a = true)).card
          + (A.filter (fun a => ¬ (g a = true))).card = A.card :=
        Finset.card_filter_add_card_filter_not _
      have h1 : (A.filter (fun a => g a = true)).card ≤ 2 ^ cost (f true) := by
        refine ih true _ (fun a ha b hb => ?_)
        rw [Finset.mem_filter] at ha
        have := h a ha.1 b (Finset.mem_filter.mp hb).1
        rwa [run, ha.2] at this
      have h0 : (A.filter (fun a => ¬ (g a = true))).card ≤ 2 ^ cost (f false) := by
        refine ih false _ (fun a ha b hb => ?_)
        rw [Finset.mem_filter] at ha
        have hga : g a = false := by simpa using ha.2
        have := h a ha.1 b (Finset.mem_filter.mp hb).1
        rwa [run, hga] at this
      have hm0 : (2:ℕ) ^ cost (f false) ≤ 2 ^ max (cost (f false)) (cost (f true)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hm1 : (2:ℕ) ^ cost (f true) ≤ 2 ^ max (cost (f false)) (cost (f true)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : A.card ≤ 2 ^ max (cost (f false)) (cost (f true))
          + 2 ^ max (cost (f false)) (cost (f true)) := by omega
      rw [cost, pow_add, pow_one]
      omega
  | bob g f ih =>
      classical
      have hsplit : (A.filter (fun b => g (negVec b) = true)).card
          + (A.filter (fun b => ¬ (g (negVec b) = true))).card = A.card :=
        Finset.card_filter_add_card_filter_not _
      have h1 : (A.filter (fun b => g (negVec b) = true)).card ≤ 2 ^ cost (f true) := by
        refine ih true _ (fun a ha b hb => ?_)
        rw [Finset.mem_filter] at hb
        have := h a (Finset.mem_filter.mp ha).1 b hb.1
        rwa [run, hb.2] at this
      have h0 : (A.filter (fun b => ¬ (g (negVec b) = true))).card ≤ 2 ^ cost (f false) := by
        refine ih false _ (fun a ha b hb => ?_)
        rw [Finset.mem_filter] at hb
        have hgb : g (negVec b) = false := by simpa using hb.2
        have := h a (Finset.mem_filter.mp ha).1 b hb.1
        rwa [run, hgb] at this
      have hm0 : (2:ℕ) ^ cost (f false) ≤ 2 ^ max (cost (f false)) (cost (f true)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hm1 : (2:ℕ) ^ cost (f true) ≤ 2 ^ max (cost (f false)) (cost (f true)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : A.card ≤ 2 ^ max (cost (f false)) (cost (f true))
          + 2 ^ max (cost (f false)) (cost (f true)) := by omega
      rw [cost, pow_add, pow_one]
      omega

end Proto

/-- **Deterministic two-way lower bound.** Any deterministic communication protocol that
computes set disjointness on an `n`-element universe must communicate at least `n` bits. -/
theorem disjointness_lb_deterministic (n : ℕ) (p : Proto n)
    (hp : ∀ a b : Fin n → Bool, p.run a b = Disj a b) :
    n ≤ p.cost := by
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card ≤ 2 ^ p.cost :=
    Proto.card_le_two_pow_cost p _ (fun a _ b _ => hp a (negVec b))
  have h2 : (2:ℕ) ^ n ≤ 2 ^ p.cost := by simpa using hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

/-- A concrete protocol for `n = 1`, witnessing that the hypothesis of
`disjointness_lb_deterministic` is satisfiable. -/
def proto1 : Proto 1 :=
  .alice (fun a => a 0)
    (fun v => if v then .bob (fun b => b 0) (fun w => .leaf (!w)) else .leaf true)

example : ∀ a b : Fin 1 → Bool, proto1.run a b = Disj a b := by decide

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

/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file proves a linear lower bound on the *randomized* (public-coin) one-way
communication complexity of set disjointness on `n`-element universes:
any public-coin randomized protocol in which Alice sends a single `c`-bit message
to Bob, who then outputs the value of `Disj`, and which errs with probability at
most `1/16` on every input pair, must satisfy `n ≤ 3 * (c + 1)`, i.e. `c = Ω(n)`.

The proof is the standard one: average over the public randomness to fix a
deterministic message map that is correct on average over uniformly random
inputs `(a, {i})`, observe that Alice's message then determines a string within
small Hamming distance of `a` for at least half of all `a`, and finish with a
counting argument using a Hamming-ball volume bound.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- Set disjointness, on characteristic vectors of subsets of `Fin n`. -/
def Disj (a b : Fin n → Bool) : Bool := decide (∀ i, ¬ (a i = true ∧ b i = true))

/-- The characteristic vector of the singleton `{i}`. -/
def sing (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

/-- Disjointness against a singleton is negated membership. -/
lemma Disj_sing (a : Fin n → Bool) (i : Fin n) : Disj a (sing i) = !(a i) := by
  cases h : a i <;> simp [Disj, sing, h, decide_eq_true_eq]
  intro j hj hji
  subst hji
  rw [h] at hj
  exact Bool.noConfusion hj

/-- Volume bound for Hamming balls, in the form `∑_{j ≤ k} C(n,j) ≤ 8^k (8/7)^{n-k}`.
This is the usual entropy bound specialised to the parameter `1/8`. -/
lemma sum_choose_le_real (n k : ℕ) (hk : k ≤ n) :
    ((∑ j ∈ range (k + 1), n.choose j : ℕ) : ℝ) ≤ 8 ^ k * (8 / 7) ^ (n - k) := by
  have hmono : ∀ j ∈ range (k + 1),
      ((1 : ℝ) / 8) ^ k * (7 / 8) ^ (n - k) ≤ (1 / 8) ^ j * (7 / 8) ^ (n - j) := by
    intro j hj
    simp only [mem_range, Nat.lt_succ_iff] at hj
    obtain ⟨s, rfl⟩ : ∃ s, k = j + s := ⟨k - j, by omega⟩
    have h1 : n - j = (n - (j + s)) + s := by omega
    rw [h1, pow_add, pow_add]
    have h2 : ((1 : ℝ) / 8) ^ s ≤ (7 / 8) ^ s := pow_le_pow_left₀ (by norm_num) (by norm_num) s
    have h3 : (1 / 8 : ℝ) ^ j * (1 / 8) ^ s * (7 / 8) ^ (n - (j + s))
        = ((1 / 8 : ℝ) ^ j * (7 / 8) ^ (n - (j + s))) * (1 / 8) ^ s := by ring
    have h4 : (1 / 8 : ℝ) ^ j * ((7 / 8) ^ (n - (j + s)) * (7 / 8) ^ s)
        = ((1 / 8 : ℝ) ^ j * (7 / 8) ^ (n - (j + s))) * (7 / 8) ^ s := by ring
    rw [h3, h4]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hw : (0 : ℝ) < (1 / 8 : ℝ) ^ k * (7 / 8) ^ (n - k) := by positivity
  have step1 : (∑ j ∈ range (k + 1), (n.choose j : ℝ)) * ((1 / 8 : ℝ) ^ k * (7 / 8) ^ (n - k))
      ≤ ∑ j ∈ range (k + 1), (n.choose j : ℝ) * ((1 / 8) ^ j * (7 / 8) ^ (n - j)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hmono j hj) (by positivity)
  have step2 : (∑ j ∈ range (k + 1), (n.choose j : ℝ) * ((1 / 8) ^ j * (7 / 8) ^ (n - j)))
      ≤ ∑ j ∈ range (n + 1), (n.choose j : ℝ) * ((1 / 8) ^ j * (7 / 8) ^ (n - j)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun i _ _ => by positivity)
    simp only [mem_range] at *
    omega
  have step3 : (∑ j ∈ range (n + 1), (n.choose j : ℝ) * ((1 / 8) ^ j * (7 / 8) ^ (n - j))) = 1 := by
    have h5 : ∑ j ∈ range (n + 1), (n.choose j : ℝ) * ((1 / 8) ^ j * (7 / 8) ^ (n - j))
        = ∑ j ∈ range (n + 1), (1 / 8 : ℝ) ^ j * (7 / 8) ^ (n - j) * (n.choose j) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [h5, ← add_pow]
    norm_num
  have hle : (∑ j ∈ range (k + 1), (n.choose j : ℝ)) * ((1 / 8 : ℝ) ^ k * (7 / 8) ^ (n - k)) ≤ 1 := by
    linarith
  have hinv : (8 : ℝ) ^ k * (8 / 7) ^ (n - k) = ((1 / 8 : ℝ) ^ k * (7 / 8) ^ (n - k))⁻¹ := by
    rw [mul_inv, ← inv_pow, ← inv_pow]
    norm_num
  rw [hinv, inv_eq_one_div, le_div_iff₀ hw]
  push_cast
  exact hle

/-- Counting step: the inputs whose "reconstruction" from Alice's message is within
Hamming distance `n / 8` are determined by the message together with a small
difference set, so there are at most `2 ^ c * ∑_{j ≤ n/8} C(n,j)` of them. -/
private lemma card_close_le (n c : ℕ) (m : (Fin n → Bool) → Fin (2 ^ c))
    (y : Fin (2 ^ c) → (Fin n → Bool)) :
    ((Finset.univ.filter (fun a : Fin n → Bool =>
        8 * (Finset.univ.filter (fun i => y (m a) i ≠ a i)).card ≤ n)).card)
      ≤ 2 ^ c * ∑ j ∈ range (n / 8 + 1), n.choose j := by
  classical
  set k := n / 8 with hk
  set T : Finset (Fin (2 ^ c) × Finset (Fin n)) :=
    (univ : Finset (Fin (2 ^ c))) ×ˢ
      ((range (k + 1)).biUnion (fun j => Finset.powersetCard j (univ : Finset (Fin n)))) with hT
  have hTcard : T.card ≤ 2 ^ c * ∑ j ∈ range (k + 1), n.choose j := by
    rw [hT, Finset.card_product]
    simp only [Finset.card_univ, Fintype.card_fin]
    refine Nat.mul_le_mul_left _ (le_trans Finset.card_biUnion_le ?_)
    simp [Finset.card_powersetCard]
  refine le_trans (Finset.card_le_card_of_injOn
    (fun a => (m a, Finset.univ.filter (fun i => y (m a) i ≠ a i))) ?_ ?_) hTcard
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha
    simp only [hT, Finset.mem_coe, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_range]
    refine ⟨(Finset.univ.filter (fun i => y (m a) i ≠ a i)).card, by omega, ?_⟩
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, rfl⟩
  · intro a ha b hb hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    funext i
    have hi := congrArg (fun S => i ∈ S) h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at hi
    rw [h1] at hi
    revert hi
    cases y (m b) i <;> cases hA : a i <;> cases hB : b i <;> simp

/-- Markov step: if the average error count is at most `2^n * n / 16`, then fewer than
half of the inputs have error count larger than `n / 8`. -/
private lemma card_bad_lt (n : ℕ) (D : (Fin n → Bool) → ℕ)
    (hDsum : ∑ a : (Fin n → Bool), (D a : ℝ) ≤ (2 ^ n * n : ℝ) / 16) :
    2 * (Finset.univ.filter (fun a : Fin n → Bool => ¬ (8 * D a ≤ n))).card < 2 ^ n := by
  classical
  set Bad := (Finset.univ.filter (fun a : Fin n → Bool => ¬ (8 * D a ≤ n))) with hBad
  have h0 : ∑ _a ∈ Bad, (((n : ℝ) + 1) / 8) ≤ ∑ a ∈ Bad, (D a : ℝ) := by
    refine Finset.sum_le_sum fun a ha => ?_
    rw [hBad, Finset.mem_filter] at ha
    have h : n + 1 ≤ 8 * D a := by omega
    have h' : ((n : ℝ) + 1) ≤ 8 * (D a : ℝ) := by exact_mod_cast h
    linarith
  have h1 : (Bad.card : ℝ) * (((n : ℝ) + 1) / 8) ≤ ∑ a ∈ Bad, (D a : ℝ) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using h0
  have h2 : ∑ a ∈ Bad, (D a : ℝ) ≤ ∑ a : (Fin n → Bool), (D a : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => by positivity)
  have h3 : (Bad.card : ℝ) * (((n : ℝ) + 1) / 8) ≤ (2 ^ n * n : ℝ) / 16 := by linarith
  have h4 : (2 * Bad.card : ℝ) < 2 ^ n := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    nlinarith [h3, hn, hp]
  exact_mod_cast h4

/-- The final arithmetic: a Hamming-ball counting bound of this shape forces `n ≤ 3(c+1)`. -/
private lemma arith_contradiction (n c k V g : ℕ) (hcon : 3 * (c + 1) < n) (hk : 8 * k ≤ n)
    (hkn : k ≤ n) (hG2 : 2 ^ n < 2 * g) (hGT : g ≤ 2 ^ c * V)
    (hV : (V : ℝ) ≤ 8 ^ k * (8 / 7) ^ (n - k)) : False := by
  have hVR : (0 : ℝ) ≤ V := by positivity
  have h1 : (2 : ℝ) ^ n < 2 * (2 ^ c * V) := by
    have h : ((2 ^ n : ℕ) : ℝ) < ((2 * (2 ^ c * V) : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le hG2 (by omega)
    push_cast at h
    exact h
  have h2 : ((8 : ℝ) / 7) ^ (n - k) ≤ (8 / 7) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (2 : ℝ) ^ n < 2 ^ (c + 1) * 8 ^ k * (8 / 7) ^ n := by
    have e : (2 : ℝ) ^ (c + 1) * 8 ^ k * (8 / 7) ^ n = 2 * (2 ^ c * (8 ^ k * (8 / 7) ^ n)) := by
      rw [pow_succ]; ring
    calc (2 : ℝ) ^ n < 2 * (2 ^ c * V) := h1
      _ ≤ 2 * (2 ^ c * (8 ^ k * (8 / 7) ^ (n - k))) := by gcongr
      _ ≤ 2 * (2 ^ c * (8 ^ k * (8 / 7) ^ n)) := by gcongr
      _ = 2 ^ (c + 1) * 8 ^ k * (8 / 7) ^ n := e.symm
  have h24 : ((2 : ℝ) ^ n) ^ 24 < ((2 : ℝ) ^ (c + 1) * 8 ^ k * (8 / 7) ^ n) ^ 24 :=
    pow_lt_pow_left₀ h3 (by positivity) (by norm_num)
  have a1 : ((2 : ℝ) ^ (c + 1)) ^ 24 ≤ 2 ^ (8 * n) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have a2 : ((8 : ℝ) ^ k) ^ 24 ≤ 2 ^ (9 * n) := by
    have e : ((8 : ℝ) ^ k) ^ 24 = 2 ^ (72 * k) := by
      rw [← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
      ring_nf
    rw [e]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have a3 : (((8 : ℝ) / 7) ^ n) ^ 24 ≤ 2 ^ (7 * n) := by
    rw [← pow_mul, mul_comm n 24, pow_mul, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) n
  have hfin : ((2 : ℝ) ^ (c + 1) * 8 ^ k * (8 / 7) ^ n) ^ 24 ≤ 2 ^ (8 * n) * 2 ^ (9 * n) * 2 ^ (7 * n) := by
    rw [mul_pow, mul_pow]
    gcongr
  have hL : ((2 : ℝ) ^ n) ^ 24 = 2 ^ (8 * n) * 2 ^ (9 * n) * 2 ^ (7 * n) := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    ring_nf
  linarith

/-- **Set disjointness has linear randomized communication complexity.**

Model: a public-coin randomized one-way protocol on inputs `a b : Fin n → Bool`
(characteristic vectors of subsets of an `n`-element universe).  The public random
string is uniform on `Fin N` (`N > 0`); given the random string `r`, Alice sends the
`c`-bit message `msg r a : Fin (2 ^ c)` and Bob answers `out r (msg r a) b`.  The
protocol is assumed to err with probability at most `1/16` on every input pair.

Conclusion: `n ≤ 3 * (c + 1)`, i.e. the number `c` of communicated bits is `Ω(n)`. -/
theorem disjointness_lb (n c N : ℕ) (hN : 0 < N)
    (msg : Fin N → (Fin n → Bool) → Fin (2 ^ c))
    (out : Fin N → Fin (2 ^ c) → (Fin n → Bool) → Bool)
    (herr : ∀ a b : Fin n → Bool,
      ((Finset.univ.filter (fun r : Fin N => out r (msg r a) b ≠ Disj a b)).card : ℝ)
        ≤ (N : ℝ) / 16) :
    n ≤ 3 * (c + 1) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hNne : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set ind : Fin N → (Fin n → Bool) → Fin n → ℝ := fun r a i =>
    if out r (msg r a) (sing i) ≠ !(a i) then 1 else 0 with hind
  -- Step 1: for each input pair `(a, {i})` the protocol errs for few random strings.
  have hcard : ∀ (a : Fin n → Bool) (i : Fin n), ∑ r : Fin N, ind r a i ≤ (N : ℝ) / 16 := by
    intro a i
    have h := herr a (sing i)
    rw [Disj_sing] at h
    have e : ∑ r : Fin N, ind r a i
        = ((Finset.univ.filter (fun r : Fin N => out r (msg r a) (sing i) ≠ !(a i))).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [e]; exact h
  -- Step 2: fix a random string that is good on average over uniform inputs.
  obtain ⟨r₀, hr₀⟩ :
      ∃ r₀ : Fin N, (∑ a : (Fin n → Bool), ∑ i : Fin n, ind r₀ a i) ≤ (2 ^ n * n : ℝ) / 16 := by
    have hswap : ∑ r : Fin N, (∑ a : (Fin n → Bool), ∑ i : Fin n, ind r a i)
        = ∑ a : (Fin n → Bool), ∑ i : Fin n, ∑ r : Fin N, ind r a i := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    have hle : ∑ r : Fin N, (∑ a : (Fin n → Bool), ∑ i : Fin n, ind r a i)
        ≤ ∑ _r : Fin N, ((2 ^ n * n : ℝ) / 16) := by
      rw [hswap]
      have h1 : ∑ a : (Fin n → Bool), ∑ i : Fin n, ∑ r : Fin N, ind r a i
          ≤ ∑ _a : (Fin n → Bool), ∑ _i : Fin n, ((N : ℝ) / 16) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ => hcard a i
      refine h1.trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_bool]
      push_cast
      ring
    obtain ⟨r₀, -, h⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
    exact ⟨r₀, h⟩
  -- Step 3: Bob's answers on singletons reconstruct a string `y m` from the message `m`.
  set y : Fin (2 ^ c) → (Fin n → Bool) := fun m i => !(out r₀ m (sing i)) with hy
  set D : (Fin n → Bool) → ℕ :=
    fun a => (Finset.univ.filter (fun i => y (msg r₀ a) i ≠ a i)).card with hD
  have hDeq : ∀ a : Fin n → Bool, (D a : ℝ) = ∑ i : Fin n, ind r₀ a i := by
    intro a
    rw [hD]
    simp only
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    cases hh : out r₀ (msg r₀ a) (sing i) <;> cases ha : a i <;> simp [hind, hy, hh, ha]
  have hDsum : ∑ a : (Fin n → Bool), (D a : ℝ) ≤ (2 ^ n * n : ℝ) / 16 := by
    refine le_trans (le_of_eq ?_) hr₀
    exact Finset.sum_congr rfl fun a _ => hDeq a
  -- Step 4: at least half of the inputs are reconstructed to within distance `n / 8`.
  have hBadlt := card_bad_lt n D hDsum
  have hcardX : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
  have hGBad : (Finset.univ.filter (fun a : Fin n → Bool => 8 * D a ≤ n)).card
      + (Finset.univ.filter (fun a : Fin n → Bool => ¬ (8 * D a ≤ n))).card = 2 ^ n := by
    rw [Finset.card_filter_add_card_filter_not, hcardX]
  have hG2 : 2 ^ n < 2 * (Finset.univ.filter (fun a : Fin n → Bool => 8 * D a ≤ n)).card := by
    omega
  -- Step 5: counting.
  have hGT : (Finset.univ.filter (fun a : Fin n → Bool => 8 * D a ≤ n)).card
      ≤ 2 ^ c * ∑ j ∈ range (n / 8 + 1), n.choose j := by
    simpa [hD] using card_close_le n c (msg r₀) y
  exact arith_contradiction n c (n / 8) (∑ j ∈ range (n / 8 + 1), n.choose j) _ hcon
    (by omega) (by omega) hG2 hGT (sum_choose_le_real n (n / 8) (by omega))

/-- The hypotheses of `disjointness_lb` are satisfiable: with `c = n` bits Alice can send
her whole input and Bob answers with no error at all.  So the lower bound is not vacuous
(and is tight up to the constant factor). -/
theorem exists_exact_protocol (n N : ℕ) :
    ∃ (msg : Fin N → (Fin n → Bool) → Fin (2 ^ n))
      (out : Fin N → Fin (2 ^ n) → (Fin n → Bool) → Bool),
      ∀ a b : Fin n → Bool,
        ((Finset.univ.filter (fun r : Fin N => out r (msg r a) b ≠ Disj a b)).card : ℝ)
          ≤ (N : ℝ) / 16 := by
  classical
  have e : (Fin n → Bool) ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq (by simp)
  refine ⟨fun _ a => e a, fun _ m b => Disj (e.symm m) b, fun a b => ?_⟩
  simp [Equiv.symm_apply_apply]
  positivity

end CS

