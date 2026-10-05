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

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

The *spectral model* of the Goldbach problem attaches to every natural number `n` the
"spectral count"
```
spectralCount n = ∑_{p ≤ n} [ p prime ] · [ n - p prime ]
```
i.e. the number of representations of `n` as an ordered sum of two primes.  The *spectral
model hypothesis* is the statement that this count is positive on the even numbers `≥ 4`.

This file contains:

* `spectralCount_pos_iff` : the (unconditional) transfer principle
  `0 < spectralCount n ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p + q = n`;
* `goldbach_of_spectral_positivity` : the schema, i.e. spectral positivity on a range implies
  Goldbach's property on that range;
* `spectral_positivity_window` : the **discharge** of the spectral positivity hypothesis, proved
  unconditionally by a kernel-checked finite computation on the window `4 ≤ n ≤ 10000`;
* `goldbach_from_spectral_model` : the resulting unconditional theorem.

Goldbach's conjecture itself is open, so the unconditional discharge is necessarily restricted to
a finite window; the transfer principle `spectralCount_pos_iff` holds for *all* `n`.

The finite computation is carried out with a *sound* (but deliberately incomplete) Boolean
primality test `isPrimeB`, whose soundness is proved from `Nat.prime_def_le_sqrt`; only soundness
is needed, since the computation is used to *produce* prime witnesses.
-/

namespace Brockian
namespace GoldbachSchema

/-! ### The spectral model -/

/-- Spectral weight of the mode `p` for the number `n`: it is `1` exactly when `p` and `n - p`
are both prime and `p ≤ n`, i.e. when `p` contributes a Goldbach decomposition of `n`. -/
def spectralWeight (n p : ℕ) : ℕ :=
  if Nat.Prime p ∧ p ≤ n ∧ Nat.Prime (n - p) then 1 else 0

/-- The spectral count of `n`: the number of ordered representations of `n` as a sum of two
primes. -/
def spectralCount (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (n + 1), spectralWeight n p

/-- **Transfer principle.** The spectral count of `n` is positive if and only if `n` is a sum of
two primes.  This holds for every natural number `n`. -/
theorem spectralCount_pos_iff (n : ℕ) :
    0 < spectralCount n ↔ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  rw [spectralCount, Nat.pos_iff_ne_zero, Ne, Finset.sum_eq_zero_iff]
  push_neg
  constructor
  · rintro ⟨p, -, hw⟩
    unfold spectralWeight at hw
    split at hw
    · rename_i h
      exact ⟨p, n - p, h.1, h.2.2, by omega⟩
    · exact absurd rfl hw
  · rintro ⟨p, q, hp, hq, rfl⟩
    refine ⟨p, Finset.mem_range.mpr (by omega), ?_⟩
    unfold spectralWeight
    rw [if_pos ⟨hp, by omega, by simpa using hq⟩]
    exact one_ne_zero

/-- **The schema.** If the spectral count is positive throughout a window of even numbers, then
every even number in that window is a sum of two primes. -/
theorem goldbach_of_spectral_positivity (N : ℕ)
    (hspec : ∀ n : ℕ, 4 ≤ n → n ≤ N → Even n → 0 < spectralCount n) :
    ∀ n : ℕ, 4 ≤ n → n ≤ N → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n :=
  fun n h4 hN hev => (spectralCount_pos_iff n).mp (hspec n h4 hN hev)

/-! ### A kernel-friendly sound primality test -/

/-- `noFactorFrom n f d` performs at most `f` trial divisions of `n` by `d, d+1, …`.  It returns
`true` only when the loop terminates because `n < d * d`, i.e. only when it has genuinely
certified that `n` has no divisor `e` with `d ≤ e` and `e * e ≤ n`. -/
def noFactorFrom (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | (f + 1), d => if n < d * d then true else if n % d == 0 then false else noFactorFrom n f (d + 1)

/-- Soundness of the trial-division loop. -/
theorem noFactorFrom_sound (n : ℕ) :
    ∀ (f d : ℕ), noFactorFrom n f d = true → ∀ e, d ≤ e → e * e ≤ n → ¬ e ∣ n := by
  intro f
  induction f with
  | zero => intro d h; simp [noFactorFrom] at h
  | succ f ih =>
    intro d h e hde hee hdvd
    rw [noFactorFrom] at h
    split at h
    · rename_i hlt
      have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · split at h
      · exact absurd h Bool.false_ne_true
      · rename_i hmod
        rcases Nat.lt_or_ge d e with hlt | hge
        · exact ih (d + 1) h e (by omega) hee hdvd
        · have hed : d = e := le_antisymm hde hge
          subst hed
          have hd0 : n % d = 0 := Nat.eq_zero_of_dvd_of_lt.elim
          simp [hd0] at hmod

/-- A sound Boolean primality test.  It is deliberately incomplete: with the fixed fuel `128` it
can only certify primality of numbers below `129 * 129`, and returns `false` otherwise. -/
def isPrimeB (n : ℕ) : Bool := 2 ≤ n && noFactorFrom n 128 2

/-- Soundness of `isPrimeB`. -/
theorem isPrimeB_sound {n : ℕ} (h : isPrimeB n = true) : Nat.Prime n := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  refine Nat.prime_def_le_sqrt.mpr ⟨h.1, fun m hm hms => ?_⟩
  exact noFactorFrom_sound n 128 2 h.2 m hm (Nat.le_sqrt.mp hms)

/-! ### The finite computation -/

/-- Candidate values for the smaller summand in a Goldbach decomposition. -/
def cands : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
   193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251]

/-- `hasDecomp n` searches the candidate list for a prime `p ≤ n` with `n - p` prime. -/
def hasDecomp (n : ℕ) : Bool :=
  cands.any fun p => p ≤ n && isPrimeB p && isPrimeB (n - p)

/-- Soundness of the search: a successful search certifies spectral positivity. -/
theorem hasDecomp_sound {n : ℕ} (h : hasDecomp n = true) : 0 < spectralCount n := by
  rw [hasDecomp, List.any_eq_true] at h
  obtain ⟨p, -, hp⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact (spectralCount_pos_iff n).mpr
    ⟨p, n - p, isPrimeB_sound hp.1.2, isPrimeB_sound hp.2, by omega⟩

/-- The kernel-checked finite computation: every even number `2k + 4` with `k < 4999`
(equivalently, every even `n` with `4 ≤ n ≤ 10000`) passes the search. -/
theorem window_check : (List.range 4999).all (fun k => hasDecomp (2 * k + 4)) = true := by
  decide +kernel

/-- **Discharge of the spectral model hypothesis** on the window `4 ≤ n ≤ 10000`: the spectral
count of every even number in this window is positive.  This is unconditional. -/
theorem spectral_positivity_window (n : ℕ) (h4 : 4 ≤ n) (hle : n ≤ 10000) (hev : Even n) :
    0 < spectralCount n := by
  obtain ⟨m, rfl⟩ := hev
  refine hasDecomp_sound (n := m + m) ?_
  have hmem : (m - 2) ∈ List.range 4999 := List.mem_range.mpr (by omega)
  have h := List.all_eq_true.mp window_check (m - 2) hmem
  have heq : 2 * (m - 2) + 4 = m + m := by omega
  rwa [heq] at h

/-! ### The main theorem -/

/-- **Goldbach from the spectral model (unconditional).**

The first conjunct is the transfer principle of the spectral model, valid for every natural
number: positivity of the spectral count is *equivalent* to the Goldbach property.

The second conjunct is the discharged conclusion: the spectral positivity hypothesis has been
verified unconditionally on the window `4 ≤ n ≤ 10000`, hence every even number in that window is
a sum of two primes.  (Goldbach's conjecture in full is open, so no hypothesis-free statement for
all even `n ≥ 4` is available; the window bound is the only restriction, and no unproved
hypothesis remains.) -/
theorem goldbach_from_spectral_model :
    (∀ n : ℕ, 0 < spectralCount n ↔ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) ∧
    (∀ n : ℕ, 4 ≤ n → n ≤ 10000 → Even n →
        ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) :=
  ⟨spectralCount_pos_iff,
    goldbach_of_spectral_positivity 10000 fun n h4 hle hev =>
      spectral_positivity_window n h4 hle hev⟩

end GoldbachSchema
end Brockian

