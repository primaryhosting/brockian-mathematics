import RequestProject.SimonQuantum

/-!
# Recovering the hidden shift from the measured samples

Each run of the quantum subroutine returns a uniformly random `y ∈ s^⊥`.  After `m`
runs the classical post-processing solves the linear system `t ⬝ y_i = 0` and outputs the
unique nonzero solution, which succeeds exactly when the samples *determine* `s`.
We bound the number of sample sequences that fail to determine `s`.
-/

open scoped BigOperators

namespace QI

variable {n : ℕ}

/-- The samples `y : Fin m → BV n` determine the hidden shift `s`: the only vectors
orthogonal to all of them are `0` and `s`. -/
def Determines (s : BV n) {m : ℕ} (y : Fin m → BV n) : Prop :=
  ∀ t : BV n, (∀ i, dotp t (y i) = 0) → t = 0 ∨ t = s

/-- If the samples determine `s`, then `s` is the *unique* nonzero solution of the linear
system `t ⬝ y_i = 0`; hence solving that system recovers the hidden shift. -/
theorem unique_solution_of_determines {s : BV n} (hs : s ≠ 0) {m : ℕ} {y : Fin m → BV n}
    (hmem : ∀ i, dotp s (y i) = 0) (hdet : Determines s y) :
    ∃! t : BV n, t ≠ 0 ∧ ∀ i, dotp t (y i) = 0 := by
  refine ⟨s, ⟨hs, hmem⟩, ?_⟩
  rintro t ⟨ht0, ht⟩
  rcases hdet t ht with h | h
  · exact absurd h ht0
  · exact h

/-- All sequences of `m` samples from the hyperplane `s^⊥`. -/
def allSamples (s : BV n) (m : ℕ) : Finset (Fin m → BV n) :=
  Fintype.piFinset (fun _ => perp s)

open Classical in
/-- The sequences of `m` samples from `s^⊥` that fail to determine `s`. -/
noncomputable def badSamples (s : BV n) (m : ℕ) : Finset (Fin m → BV n) :=
  (allSamples s m).filter (fun y => ¬ Determines s y)

lemma card_allSamples (s : BV n) (m : ℕ) :
    (allSamples s m).card = (perp s).card ^ m := by
  simp [allSamples, Fintype.card_piFinset]

/-- For `t ∉ {0, s}` the functional `dotp t` is nonzero on `s^⊥`, so it halves it. -/
lemma card_perp_filter {s t : BV n} (ht0 : t ≠ 0) (hts : t ≠ s) :
    2 * ((perp s).filter (fun y => dotp t y = 0)).card = (perp s).card := by
  classical
  obtain ⟨a, ha, ha'⟩ : ∃ a : BV n, dotp s a = 0 ∧ dotp t a = 1 := by
    by_contra hc
    push_neg at hc
    have hall : ∀ y : BV n, dotp s y = 0 → dotp t y = 0 := by
      intro y hy
      rcases QI.ZMod.two_cases (dotp t y) with h0 | h1
      · exact h0
      · exact absurd h1 (hc y hy)
    rcases eq_zero_or_eq_of_forall_dotp hall with h | h
    · exact ht0 h
    · exact hts h
  refine card_filter_half _ t a ?_ ha'
  intro x hx
  rw [mem_perp] at hx ⊢
  rw [dotp_add_right, hx, ha, add_zero]

/-- **Failure probability of Simon's algorithm.**  Out of the `|s^⊥|^m` equally likely
sample sequences, at most a `2^n / 2^m` fraction fails to determine the hidden shift. -/
theorem card_badSamples_le (s : BV n) (m : ℕ) :
    2 ^ m * (badSamples s m).card ≤ 2 ^ n * (perp s).card ^ m := by
  classical
  set F : Finset (BV n) := Finset.univ.filter (fun t => t ≠ 0 ∧ t ≠ s) with hF
  set P : BV n → Finset (BV n) := fun t => (perp s).filter (fun y => dotp t y = 0) with hP
  have hsub : badSamples s m ⊆ F.biUnion (fun t => Fintype.piFinset (fun _ => P t)) := by
    intro y hy
    simp only [badSamples, allSamples, Finset.mem_filter, Fintype.mem_piFinset] at hy
    obtain ⟨hmem, hnd⟩ := hy
    rw [Determines] at hnd
    push_neg at hnd
    obtain ⟨t, htall, ht0, hts⟩ := hnd
    refine Finset.mem_biUnion.2 ⟨t, ?_, ?_⟩
    · simp [hF, ht0, hts]
    · exact Fintype.mem_piFinset.2 (fun i => Finset.mem_filter.2 ⟨hmem i, htall i⟩)
  have hcard : (badSamples s m).card ≤ ∑ t ∈ F, (P t).card ^ m := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_biUnion_le) ?_
    exact Finset.sum_le_sum (fun t _ => by simp [Fintype.card_piFinset])
  calc 2 ^ m * (badSamples s m).card ≤ 2 ^ m * ∑ t ∈ F, (P t).card ^ m := by
        exact Nat.mul_le_mul_left _ hcard
    _ = ∑ t ∈ F, (2 * (P t).card) ^ m := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [mul_pow]
    _ = ∑ _t ∈ F, (perp s).card ^ m := by
        refine Finset.sum_congr rfl fun t ht => ?_
        simp only [hF, Finset.mem_filter] at ht
        rw [card_perp_filter ht.2.1 ht.2.2]
    _ = F.card * (perp s).card ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ n * (perp s).card ^ m := by
        refine Nat.mul_le_mul_right _ ?_
        refine le_trans (Finset.card_filter_le _ _) ?_
        simp [Finset.card_univ, ZMod.card]

/-- With `m = n + k` queries, the failure probability of Simon's algorithm is at most
`2^{-k}`: at most a `2^{-k}` fraction of the `|s^⊥|^(n+k)` sample sequences fails to
determine the hidden shift.  In particular `O(n)` quantum queries suffice. -/
theorem simon_failure_prob (s : BV n) (k : ℕ) :
    2 ^ k * (badSamples s (n + k)).card ≤ (allSamples s (n + k)).card := by
  have h := card_badSamples_le s (n + k)
  rw [card_allSamples]
  have hpow : (2 : ℕ) ^ (n + k) = 2 ^ n * 2 ^ k := pow_add 2 n k
  rw [hpow] at h
  have h2 : 2 ^ n * (2 ^ k * (badSamples s (n + k)).card)
      ≤ 2 ^ n * ((perp s).card ^ (n + k)) := by
    calc 2 ^ n * (2 ^ k * (badSamples s (n + k)).card)
        = 2 ^ n * 2 ^ k * (badSamples s (n + k)).card := by ring
      _ ≤ 2 ^ n * (perp s).card ^ (n + k) := h
  exact Nat.le_of_mul_le_mul_left h2 (Nat.two_pow_pos n)

end QI

import RequestProject.SimonBasic

/-!
# Orthogonal complements in `F_2^n`

Counting lemmas for the hyperplanes `{y : dotp t y = 0}` used both in the analysis of
Simon's algorithm and in the classical lower bound.
-/

open scoped BigOperators

namespace QI

variable {n : ℕ}

/-- If `A` is closed under translation by `a` and `dotp t a = 1`, then exactly half of `A`
is orthogonal to `t`. -/
lemma card_filter_half (A : Finset (BV n)) (t a : BV n)
    (hA : ∀ x ∈ A, x + a ∈ A) (ha : dotp t a = 1) :
    2 * (A.filter (fun x => dotp t x = 0)).card = A.card := by
  classical
  have hsplit : (A.filter (fun x => dotp t x = 0)).card
      + (A.filter (fun x => ¬ dotp t x = 0)).card = A.card :=
    Finset.card_filter_add_card_filter_not _
  have hne : (A.filter (fun x => ¬ dotp t x = 0))
      = (A.filter (fun x => dotp t x = 1)) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · intro h
      rcases QI.ZMod.two_cases (dotp t x) with h0 | h1
      · exact absurd h0 h
      · exact h1
    · intro h
      rw [h]
      decide
  rw [hne] at hsplit
  have hbij : (A.filter (fun x => dotp t x = 0)).card
      = (A.filter (fun x => dotp t x = 1)).card := by
    refine Finset.card_bij' (fun x _ => x + a) (fun x _ => x + a) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      refine ⟨hA x hx.1, ?_⟩
      rw [dotp_add_right, hx.2, ha, zero_add]
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      refine ⟨hA x hx.1, ?_⟩
      rw [dotp_add_right, hx.2, ha]
      decide
    · intro x _
      simp [BV.add_add_cancel]
    · intro x _
      simp [BV.add_add_cancel]
  omega

/-- The hyperplane orthogonal to `s`. -/
def perp (s : BV n) : Finset (BV n) := Finset.univ.filter (fun y => dotp s y = 0)

lemma mem_perp {s y : BV n} : y ∈ perp s ↔ dotp s y = 0 := by
  simp [perp]

lemma exists_dotp_eq_one {s : BV n} (hs : s ≠ 0) : ∃ a : BV n, dotp s a = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hs (funext fun i => h i)
  refine ⟨e i, ?_⟩
  rcases QI.ZMod.two_cases (s i) with h0 | h1
  · exact absurd h0 hi
  · simpa using h1

/-- The hyperplane `s^⊥` has `2^(n-1)` elements: `2 * |s^⊥| = 2^n`. -/
lemma card_perp {s : BV n} (hs : s ≠ 0) : 2 * (perp s).card = 2 ^ n := by
  classical
  obtain ⟨a, ha⟩ := exists_dotp_eq_one hs
  have := card_filter_half (Finset.univ : Finset (BV n)) s a (by simp) ha
  simpa [perp, Finset.card_univ, ZMod.card] using this

/-- `(s^⊥)^⊥ = {0, s}`: a vector orthogonal to everything orthogonal to `s` is `0` or `s`. -/
lemma eq_zero_or_eq_of_forall_dotp {s t : BV n}
    (h : ∀ y : BV n, dotp s y = 0 → dotp t y = 0) : t = 0 ∨ t = s := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ht0, hts⟩ := hcon
  -- find `y` with `dotp s y = 0` and `dotp t y = 1`
  obtain ⟨i, hi⟩ : ∃ i, t i = 1 := by
    by_contra hc
    push_neg at hc
    exact ht0 (funext fun i => by
      rcases QI.ZMod.two_cases (t i) with h0 | h1
      · simpa using h0
      · exact absurd h1 (hc i))
  by_cases hsi : s i = 0
  · exact absurd (h (e i) (by simpa using hsi)) (by simp [hi])
  · have hsi1 : s i = 1 := by
      rcases QI.ZMod.two_cases (s i) with h0 | h1
      · exact absurd h0 hsi
      · exact h1
    -- `t ≠ s`, so there is `j` with `t j ≠ s j`
    obtain ⟨j, hj⟩ : ∃ j, t j ≠ s j := by
      by_contra hc
      push_neg at hc
      exact hts (funext hc)
    have hji : j ≠ i := by
      rintro rfl; exact hj (by rw [hi, hsi1])
    rcases QI.ZMod.two_cases (s j) with hsj | hsj
    · -- s j = 0, t j = 1: use e j
      have htj : t j = 1 := by
        rcases QI.ZMod.two_cases (t j) with h0 | h1
        · exact absurd (by rw [h0, hsj]) hj
        · exact h1
      exact absurd (h (e j) (by simpa using hsj)) (by simp [htj])
    · -- s j = 1, t j = 0: use e i + e j
      have htj : t j = 0 := by
        rcases QI.ZMod.two_cases (t j) with h0 | h1
        · exact h0
        · exact absurd (by rw [h1, hsj]) hj
      have hzero : dotp s (e i + e j) = 0 := by
        rw [dotp_add_right, dotp_e, dotp_e, hsi1, hsj]; decide
      have := h _ hzero
      rw [dotp_add_right, dotp_e, dotp_e, hi, htj] at this
      simp at this

end QI

import Mathlib

/-!
# Simon's problem: basic definitions

`BV n` is the `n`-dimensional Boolean vector space `F_2^n`, `dotp` is the standard
bilinear form on it, and `IsSimon s f` says that `f` is a Simon function with hidden
shift `s`, i.e. `f x = f y ↔ y = x ∨ y = x + s` with `s ≠ 0`.
-/

open scoped BigOperators

namespace QI

/-- The `n`-dimensional Boolean vector space `F_2^n` (bit strings of length `n`). -/
abbrev BV (n : ℕ) : Type := Fin n → ZMod 2

/-- The standard bilinear (inner) product on `F_2^n`. -/
def dotp {n : ℕ} (x y : BV n) : ZMod 2 := ∑ i, x i * y i

/-- `f` is an instance of Simon's problem with hidden shift `s`: `s` is nonzero and
`f` is two-to-one with `f x = f y` exactly when `y ∈ {x, x + s}`. -/
def IsSimon {n : ℕ} {β : Type*} (s : BV n) (f : BV n → β) : Prop :=
  s ≠ 0 ∧ ∀ x y, f x = f y ↔ (y = x ∨ y = x + s)

section Basic

variable {n : ℕ}

@[simp] lemma BV.add_self (x : BV n) : x + x = 0 := by
  funext i
  have : ∀ a : ZMod 2, a + a = 0 := by decide +kernel
  simpa using this (x i)

lemma BV.add_add_cancel (x s : BV n) : x + s + s = x := by
  rw [add_assoc, BV.add_self, add_zero]

lemma dotp_comm (x y : BV n) : dotp x y = dotp y x := by
  simp [dotp, mul_comm]

lemma dotp_add_right (x y z : BV n) : dotp x (y + z) = dotp x y + dotp x z := by
  simp [dotp, mul_add, Finset.sum_add_distrib]

lemma dotp_add_left (x y z : BV n) : dotp (x + y) z = dotp x z + dotp y z := by
  simp [dotp, add_mul, Finset.sum_add_distrib]

@[simp] lemma dotp_zero_left (y : BV n) : dotp 0 y = 0 := by simp [dotp]

@[simp] lemma dotp_zero_right (y : BV n) : dotp y 0 = 0 := by simp [dotp]

/-- The `i`-th standard basis vector of `F_2^n`. -/
def e (i : Fin n) : BV n := Pi.single i 1

@[simp] lemma dotp_e (x : BV n) (i : Fin n) : dotp x (e i) = x i := by
  classical
  simp [dotp, e, Pi.single_apply, Finset.sum_ite_eq' Finset.univ i]

lemma ZMod.two_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by decide +kernel +revert

end Basic

end QI

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

import RequestProject.SimonOrtho

/-!
# The quantum step of Simon's algorithm

One query to the Simon oracle for `f`, sandwiched between Hadamard transforms on the
input register, produces the state

`2^(-n) * ∑ x, ∑ y, (-1)^(x·y) |y⟩ |f x⟩`,

so measuring the input register gives outcome `y` with probability
`∑ z (2^(-n) * ∑_{x : f x = z} (-1)^(x·y))^2`.  We prove that this distribution is exactly
the uniform distribution on the hyperplane `s^⊥`, where `s` is the hidden shift.
-/

open scoped BigOperators

namespace QI

variable {n : ℕ}

/-- The real character `b ↦ (-1)^b` of `ZMod 2`. -/
noncomputable def chi (b : ZMod 2) : ℝ := if b = 0 then 1 else -1

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> simp [chi, show (1 : ZMod 2) + 1 = 0 by decide]

@[simp] lemma chi_mul_self (a : ZMod 2) : chi a * chi a = 1 := by
  fin_cases a <;> simp [chi]

/-- The probability of measuring `y` in the input register after one query of Simon's
algorithm on the oracle `f` (Hadamard, query, Hadamard, measure). -/
noncomputable def simonProb {β : Type*} [DecidableEq β] (f : BV n → β) (y : BV n) : ℝ :=
  ∑ z ∈ Finset.image f Finset.univ,
    ((1 / 2 ^ n : ℝ) * ∑ x : BV n, (if f x = z then chi (dotp x y) else 0)) ^ 2

/-- Expanding the squared amplitudes as a sum over pairs of inputs with equal values. -/
lemma sum_sq_amp {β : Type*} [DecidableEq β] (f : BV n → β) (c : BV n → ℝ) :
    ∑ z ∈ Finset.image f Finset.univ, (∑ x : BV n, (if f x = z then c x else 0)) ^ 2
      = ∑ x : BV n, ∑ x' : BV n, (if f x = f x' then c x * c x' else 0) := by
  classical
  have hstep : ∀ z, (∑ x : BV n, (if f x = z then c x else 0)) ^ 2
      = ∑ x : BV n, ∑ x' : BV n,
        (if f x = z then c x else 0) * (if f x' = z then c x' else 0) := by
    intro z
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x' _
  rw [Finset.sum_eq_single (f x)]
  · by_cases h : f x = f x'
    · simp [h]
    · simp [h, Ne.symm h]
  · intro z _ hz
    simp [Ne.symm hz]
  · intro hx
    exact absurd (Finset.mem_image_of_mem f (Finset.mem_univ x)) hx

/-- **Simon's quantum measurement.**  For a Simon function `f` with hidden shift `s`, one
query produces the uniform distribution on the hyperplane `s^⊥`: the outcome `y` has
probability `2 / 2^n = 2^{-(n-1)}` if `y ⬝ s = 0`, and probability `0` otherwise. -/
theorem simonProb_eq {β : Type*} [DecidableEq β] {s : BV n} {f : BV n → β}
    (hf : IsSimon s f) (y : BV n) :
    simonProb f y = if dotp s y = 0 then 2 / 2 ^ n else 0 := by
  classical
  obtain ⟨hs, hfib⟩ := hf
  have hfactor : simonProb f y = (1 / 2 ^ n : ℝ) ^ 2 *
      ∑ z ∈ Finset.image f Finset.univ,
        (∑ x : BV n, (if f x = z then chi (dotp x y) else 0)) ^ 2 := by
    rw [simonProb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [mul_pow]
  have hpairs : ∀ x : BV n,
      (∑ x' : BV n, (if f x = f x' then chi (dotp x y) * chi (dotp x' y) else 0))
        = 1 + chi (dotp s y) := by
    intro x
    have hset : (Finset.univ.filter (fun x' : BV n => f x = f x')) = {x, x + s} := by
      ext x'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact hfib x x'
    rw [← Finset.sum_filter, hset]
    have hne : x ≠ x + s := fun h => hs (left_eq_add.mp h)
    rw [Finset.sum_pair hne]
    have h1 : chi (dotp x y) * chi (dotp x y) = 1 := chi_mul_self _
    have h2 : chi (dotp x y) * chi (dotp (x + s) y) = chi (dotp s y) := by
      rw [dotp_add_left, chi_add, ← mul_assoc, chi_mul_self, one_mul]
    rw [h1, h2]
  rw [hfactor, sum_sq_amp f (fun x => chi (dotp x y))]
  have : ∑ x : BV n, ∑ x' : BV n,
      (if f x = f x' then chi (dotp x y) * chi (dotp x' y) else 0)
      = (2 ^ n : ℝ) * (1 + chi (dotp s y)) := by
    rw [Finset.sum_congr rfl (fun x _ => hpairs x)]
    simp [Finset.card_univ, ZMod.card, mul_comm]
    ring
  rw [this]
  have hpow : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  by_cases hy : dotp s y = 0
  · rw [if_pos hy, hy]
    have hchi : chi (0 : ZMod 2) = 1 := by simp [chi]
    rw [hchi]
    field_simp
    ring
  · rw [if_neg hy]
    have : chi (dotp s y) = -1 := by simp [chi, hy]
    rw [this]
    ring

/-- The measurement distribution is a genuine probability distribution: the outcome
probabilities sum to `1`. -/
theorem simonProb_sum_eq_one {β : Type*} [DecidableEq β] {s : BV n} {f : BV n → β}
    (hf : IsSimon s f) : ∑ y : BV n, simonProb f y = 1 := by
  classical
  have hcard := card_perp hf.1
  rw [Finset.sum_congr rfl (fun y _ => simonProb_eq hf y)]
  rw [← Finset.sum_filter]
  have hfil : (Finset.univ.filter (fun y : BV n => dotp s y = 0)) = perp s := rfl
  rw [hfil, Finset.sum_const, nsmul_eq_mul]
  have h2 : ((perp s).card : ℝ) * 2 = 2 ^ n := by
    have : ((2 * (perp s).card : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by rw [hcard]
    push_cast at this
    linarith
  have hpow : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  field_simp
  linarith [h2]

/-- The measured outcome always lies in `s^⊥`. -/
theorem simonProb_support {β : Type*} [DecidableEq β] {s : BV n} {f : BV n → β}
    (hf : IsSimon s f) {y : BV n} (hy : simonProb f y ≠ 0) : dotp s y = 0 := by
  by_contra h
  rw [simonProb_eq hf y, if_neg h] at hy
  exact hy rfl

end QI

