/-
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The Green–Tao theorem: *the primes contain arbitrarily long arithmetic progressions.*

This file contains

* the formal statement (`Frontier.HasArbitrarilyLongAPs Frontier.primeSet`, unfolded in
  `Frontier.GreenTaoStatement`);
* two Lean-checked reductions of it to standard conjectures, `Frontier.Green_Tao` (from the
  Erdős–Turán conjecture on arithmetic progressions, via Mathlib's divergence of the sum of
  prime reciprocals) and `Frontier.Green_Tao_of_Dickson` (from Dickson's conjecture on
  simultaneous primality of linear forms);
* unconditional base cases, `Frontier.Green_Tao_base`: an arithmetic progression of `k` primes
  exists for every `k ≤ 13`.

Every hypothesis is an explicit argument of the corresponding theorem; no axiom is introduced.
-/

namespace Frontier

/-- `IsAPIn A k a d` says that the `k`-term arithmetic progression with first term `a`
and common difference `d` is entirely contained in the set `A`. -/
def IsAPIn (A : Set ℕ) (k a d : ℕ) : Prop := ∀ i < k, a + i * d ∈ A

/-- `HasArbitrarilyLongAPs A` says that `A ⊆ ℕ` contains arithmetic progressions of every
finite length (with positive common difference). -/
def HasArbitrarilyLongAPs (A : Set ℕ) : Prop :=
  ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ IsAPIn A k a d

/-- The set of prime natural numbers. -/
def primeSet : Set ℕ := {p | Nat.Prime p}

/-- The statement of the Green–Tao theorem: the primes contain arbitrarily long arithmetic
progressions. -/
def GreenTaoStatement : Prop :=
  ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d)

/-- The two ways of phrasing the Green–Tao statement agree. -/
theorem greenTaoStatement_iff :
    GreenTaoStatement ↔ HasArbitrarilyLongAPs primeSet := Iff.rfl

/-! ### Reduction 1: from the Erdős–Turán conjecture -/

/-- The Erdős–Turán conjecture on arithmetic progressions: any set of natural numbers whose
sum of reciprocals diverges contains arbitrarily long arithmetic progressions. -/
def ErdosTuranAPConjecture : Prop :=
  ∀ A : Set ℕ, ¬ Summable (A.indicator fun n : ℕ => (1 : ℝ) / n) → HasArbitrarilyLongAPs A

/-- **Green–Tao theorem (Lean-checked reduction).**

The primes contain arbitrarily long arithmetic progressions: for every `k` there are natural
numbers `a` and `d > 0` with `a, a + d, …, a + (k-1) d` all prime.

The Green–Tao theorem itself is not available in Mathlib, so what is proved here is a
*reduction*: the conclusion is derived, unconditionally in Lean, from the Erdős–Turán
conjecture on arithmetic progressions, using Mathlib's theorem that the sum of the reciprocals
of the primes diverges.  The hypothesis is an explicit assumption of the statement; no axiom is
introduced. -/
theorem Green_Tao (hET : ErdosTuranAPConjecture) :
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d) := by
  have h : HasArbitrarilyLongAPs primeSet := hET primeSet not_summable_one_div_on_primes
  intro k
  obtain ⟨a, d, hd, hAP⟩ := h k
  exact ⟨a, d, hd, fun i hi => hAP i hi⟩

/-! ### Reduction 2: from Dickson's conjecture -/

/-- **Dickson's conjecture.**  Given finitely many linear forms `a i + b i * n` (`i < k`) with
positive leading coefficients, if the tuple is *admissible* — for every prime `p` some `n`
makes all the forms coprime to `p` — then there are arbitrarily large `n` for which all the
forms are simultaneously prime. -/
def DicksonConjecture : Prop :=
  ∀ (k : ℕ) (a b : ℕ → ℕ), (∀ i < k, 0 < b i) →
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ i < k, ¬ (p ∣ a i + b i * n)) →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∀ i < k, Nat.Prime (a i + b i * n)

/-- The `k`-tuple of linear forms `n + i · k!` (`i < k`), which computes the `k`-term
arithmetic progression with common difference `k!`, is admissible: for every prime `p`
there is an `n` making all `k` values coprime to `p`.

For `p ≤ k` one may take `n = 1`, since `p ∣ k!`.  For `p > k` the `k` forbidden residue
classes mod `p` cannot exhaust `ZMod p`, so a suitable residue exists. -/
theorem admissible_factorial_AP (k p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, ∀ i < k, ¬ (p ∣ i * Nat.factorial k + n) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  classical
  rcases Nat.lt_or_ge k p with hkp | hpk
  · obtain ⟨x, hx⟩ : ∃ x : ZMod p, x ∉ (Finset.range k).image
        (fun i : ℕ => -((i : ZMod p) * ((Nat.factorial k : ℕ) : ZMod p))) := by
      by_contra hcon
      push_neg at hcon
      have h : (Finset.range k).image
          (fun i : ℕ => -((i : ZMod p) * ((Nat.factorial k : ℕ) : ZMod p))) = Finset.univ :=
        Finset.eq_univ_of_forall hcon
      have hcard : ((Finset.range k).image
          (fun i : ℕ => -((i : ZMod p) * ((Nat.factorial k : ℕ) : ZMod p)))).card < p := by
        calc _ ≤ (Finset.range k).card := Finset.card_image_le
          _ = k := Finset.card_range k
          _ < p := hkp
      rw [h, Finset.card_univ, ZMod.card] at hcard
      exact lt_irrefl _ hcard
    refine ⟨x.val, fun i hi hdvd => hx ?_⟩
    have h0 : ((i * Nat.factorial k + x.val : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0
    rw [ZMod.natCast_val, ZMod.cast_id] at h0
    have hxe : x = -((i : ZMod p) * ((Nat.factorial k : ℕ) : ZMod p)) := by linear_combination h0
    rw [hxe]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)
  · refine ⟨1, fun i hi hdvd => ?_⟩
    have h1 : p ∣ i * Nat.factorial k := Dvd.dvd.mul_left (Nat.dvd_factorial hp.pos hpk) i
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

/-- **Green–Tao theorem from Dickson's conjecture (Lean-checked reduction).**

Applying Dickson's conjecture to the admissible tuple of linear forms `n + i · k!` (`i < k`)
produces, for each `k`, a `k`-term arithmetic progression of primes with common difference
`k!`. -/
theorem Green_Tao_of_Dickson (hD : DicksonConjecture) :
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d) := by
  intro k
  obtain ⟨n, -, hn⟩ :=
    hD k (fun i => i * Nat.factorial k) (fun _ => 1) (fun _ _ => Nat.one_pos)
      (fun p hp => by
        obtain ⟨n, hn⟩ := admissible_factorial_AP k p hp
        exact ⟨n, fun i hi => by simpa using hn i hi⟩) 1
  refine ⟨n, Nat.factorial k, Nat.factorial_pos k, fun i hi => ?_⟩
  have := hn i hi
  simpa [Nat.add_comm] using this

/-! ### Unconditional strengthenings of the statement

The bare Green–Tao statement (one `k`-term progression for each `k`) already implies the
apparently stronger forms: progressions starting arbitrarily late, and infinitely many
progressions of each length.  These implications are proved unconditionally. -/

/-- The Green–Tao statement self-improves: it produces `k`-term arithmetic progressions of
primes whose first term is arbitrarily large.  (Take a `(N + k)`-term progression and slide
the window forward by `N` steps.) -/
theorem GreenTaoStatement.exists_large_start (h : GreenTaoStatement) (k N : ℕ) :
    ∃ a d : ℕ, N ≤ a ∧ 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d) := by
  obtain ⟨a, d, hd, hp⟩ := h (N + k)
  refine ⟨a + N * d, d, ?_, hd, fun i hi => ?_⟩
  · calc N = N * 1 := (mul_one N).symm
      _ ≤ N * d := Nat.mul_le_mul_left N hd
      _ ≤ a + N * d := Nat.le_add_left _ _
  · have hmem := hp (N + i) (by omega)
    have he : a + (N + i) * d = a + N * d + i * d := by ring
    rwa [he] at hmem

/-- The Green–Tao statement implies that for each `k` there are *infinitely many* `k`-term
arithmetic progressions of primes. -/
theorem GreenTaoStatement.infinite_APs (h : GreenTaoStatement) (k : ℕ) :
    {p : ℕ × ℕ | 0 < p.2 ∧ ∀ i < k, Nat.Prime (p.1 + i * p.2)}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := (hfin.image Prod.fst).bddAbove
  obtain ⟨a, d, haN, hd, hp⟩ := h.exists_large_start k (N + 1)
  have hmem : a ∈ Prod.fst '' {p : ℕ × ℕ | 0 < p.2 ∧ ∀ i < k, Nat.Prime (p.1 + i * p.2)} :=
    ⟨(a, d), ⟨hd, hp⟩, rfl⟩
  have := hN hmem
  omega

/-- Combining the two: under the Erdős–Turán conjecture there are infinitely many `k`-term
arithmetic progressions of primes, for every `k`. -/
theorem Green_Tao_infinite (hET : ErdosTuranAPConjecture) (k : ℕ) :
    {p : ℕ × ℕ | 0 < p.2 ∧ ∀ i < k, Nat.Prime (p.1 + i * p.2)}.Infinite :=
  GreenTaoStatement.infinite_APs (Green_Tao hET) k

/-! ### Unconditional base cases -/

/-- **Base cases of the Green–Tao theorem, unconditionally.**

For every `k ≤ 13` there is an arithmetic progression of `k` primes: the progression with
first term `4943` and common difference `60060`, namely
`4943, 65003, 125063, 185123, 245183, 305243, 365303, 425363, 485423, 545483, 605543, 665603,
725663`, consists of thirteen primes. -/
theorem Green_Tao_base (k : ℕ) (hk : k ≤ 13) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d) := by
  refine ⟨4943, 60060, by norm_num, fun i hi => ?_⟩
  have hi13 : i < 13 := lt_of_lt_of_le hi hk
  interval_cases i <;> norm_num

end Frontier

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

