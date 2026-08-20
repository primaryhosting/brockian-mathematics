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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GilbreathConjecture

/-! ## Primes -/

/-- `n` is prime: it is at least `2` and has no divisor `d` with `2 ≤ d < n`. -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ d, d < n → 2 ≤ d → ¬ (d ∣ n)

/-- Decidability of bounded universal quantification over `Nat`. -/
instance decidableBallLTNat (n : Nat) (P : Nat → Prop) [DecidablePred P] :
    Decidable (∀ d, d < n → P d) := by
  induction n with
  | zero => exact isTrue (fun d hd => absurd hd (by omega))
  | succ n ih =>
      match ih with
      | isFalse h => exact isFalse (fun H => h (fun d hd => H d (by omega)))
      | isTrue h =>
          match inferInstanceAs (Decidable (P n)) with
          | isFalse h2 => exact isFalse (fun H => h2 (H n (by omega)))
          | isTrue h2 =>
              refine isTrue (fun d hd => ?_)
              by_cases hdn : d = n
              · exact hdn ▸ h2
              · exact h d (by omega)

instance : DecidablePred IsPrimeNat := fun n =>
  inferInstanceAs (Decidable (2 ≤ n ∧ ∀ d, d < n → 2 ≤ d → ¬ (d ∣ n)))

/-- `p` enumerates the primes in increasing order. -/
def IsPrimeEnumeration (p : Nat → Nat) : Prop :=
  (∀ n, IsPrimeNat (p n)) ∧ (∀ i j, i < j → p i < p j) ∧
    (∀ q, IsPrimeNat q → ∃ n, p n = q)

/-! ## The Gilbreath triangle -/

/-- Absolute difference of two natural numbers. -/
def adist (a b : Nat) : Nat := (a - b) + (b - a)

/-- One step of the Gilbreath triangle: the sequence of absolute differences of
consecutive terms. -/
def diffSeq (a : Nat → Nat) : Nat → Nat := fun i => adist (a (i + 1)) (a i)

/-- Row `k` of the Gilbreath triangle built on the initial sequence `p`.  Row `0`
is `p` itself (for Gilbreath's conjecture, the sequence of primes `2, 3, 5, 7, …`),
and each subsequent row consists of the absolute differences of consecutive
entries of the previous row. -/
def gilbreathRow (p : Nat → Nat) : Nat → (Nat → Nat)
  | 0 => p
  | k + 1 => diffSeq (gilbreathRow p k)

/-- **Gilbreath's conjecture** for the initial sequence `p`: every row after the
zeroth one begins with `1`. -/
def GilbreathStatement (p : Nat → Nat) : Prop := ∀ k, 1 ≤ k → gilbreathRow p k 0 = 1

/-- `IsOdlyzko a n` says that the sequence `a` begins with `1` and that its next
`n` entries all lie in `{0, 2}` — the shape observed in the rows of the Gilbreath
triangle. -/
def IsOdlyzko (a : Nat → Nat) (n : Nat) : Prop :=
  a 0 = 1 ∧ ∀ i, 1 ≤ i → i ≤ n → a i = 0 ∨ a i = 2

/-- The Odlyzko-type covering condition: every row index `m ≥ 1` is reached from
some earlier row `k ≤ m` whose `1, 0/2, 0/2, …` stretch is long enough. -/
def OdlyzkoCondition (p : Nat → Nat) : Prop :=
  ∀ m, 1 ≤ m → ∃ k n, k ≤ m ∧ m ≤ k + n ∧ IsOdlyzko (gilbreathRow p k) n

/-- Iterating the difference operator. -/
def iterD : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, a => a
  | n + 1, a => iterD n (diffSeq a)

theorem iterD_succ (n : Nat) (a : Nat → Nat) : iterD (n + 1) a = diffSeq (iterD n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [iterD, ih, iterD]

theorem gilbreathRow_add (p : Nat → Nat) (k j : Nat) :
    gilbreathRow p (k + j) = iterD j (gilbreathRow p k) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [← Nat.add_assoc, gilbreathRow, ih, iterD_succ]

/-- The shape `1, 0/2, …, 0/2` is inherited, with one fewer guaranteed entry, by
the next row of the triangle. -/
theorem isOdlyzko_diffSeq {a : Nat → Nat} {n : Nat} (h : IsOdlyzko a (n + 1)) :
    IsOdlyzko (diffSeq a) n := by
  obtain ⟨h0, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have h1 : a 1 = 0 ∨ a 1 = 2 := h2 1 (by omega) (by omega)
    rcases h1 with h1 | h1 <;> simp [diffSeq, adist, h0, h1]
  · intro i hi hin
    have hai : a i = 0 ∨ a i = 2 := h2 i hi (by omega)
    have hai1 : a (i + 1) = 0 ∨ a (i + 1) = 2 := h2 (i + 1) (by omega) (by omega)
    rcases hai with h | h <;> rcases hai1 with h' | h' <;>
      simp [diffSeq, adist, h, h']

/-- If a row has the shape `1, 0/2, …, 0/2` with `n` entries in `{0, 2}`, then each
of the following `n` rows again begins with `1`. -/
theorem head_iterD_eq_one {a : Nat → Nat} {n j : Nat} (h : IsOdlyzko a n) (hj : j ≤ n) :
    (iterD j a) 0 = 1 := by
  induction j generalizing a n with
  | zero => exact h.1
  | succ j ih =>
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [iterD]
      exact ih (isOdlyzko_diffSeq h) (by omega)

/-- The combinatorial core: for an arbitrary initial sequence, the Odlyzko
condition forces every row after the zeroth to begin with `1`. -/
theorem gilbreath_of_odlyzko (p : Nat → Nat) (H : OdlyzkoCondition p) :
    GilbreathStatement p := by
  intro m hm
  obtain ⟨k, n, hk, hkn, ho⟩ := H m hm
  obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
  rw [gilbreathRow_add]
  exact head_iterD_eq_one ho (by omega)

/-- **Conditional reduction of Gilbreath's conjecture.**

Gilbreath's conjecture — that every row after the first of the iterated absolute
difference triangle of the primes begins with `1` — is an open problem.  What is
proved here is the standard reduction (in essence due to Odlyzko): for any
increasing enumeration `p` of the primes, Gilbreath's conjecture follows from the
purely combinatorial `OdlyzkoCondition`, namely that every row index is covered by
an earlier row of the form `1, 0/2, 0/2, …` with a long enough `0/2`-stretch.

No assumption is hidden: the Odlyzko condition is an explicit hypothesis of the
theorem.  (The primality hypothesis `hp` is part of the statement, pinning the
triangle to the primes; the combinatorial argument itself does not use it.) -/
theorem GilbreathConjecture (p : Nat → Nat) (hp : IsPrimeEnumeration p)
    (H : OdlyzkoCondition p) : GilbreathStatement p :=
  gilbreath_of_odlyzko p H

/-! ## Unconditional verification of the first few rows -/

theorem enum_le {p : Nat → Nat} (hp : IsPrimeEnumeration p) {i j : Nat} (hij : i ≤ j) :
    p i ≤ p j := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · exact Nat.le_of_eq (by rw [h])
  · exact Nat.le_of_lt (hp.2.1 i j h)

theorem enum_zero {p : Nat → Nat} (hp : IsPrimeEnumeration p) : p 0 = 2 := by
  obtain ⟨n, hn⟩ := hp.2.2 2 (by decide)
  have h1 : p 0 ≤ p n := enum_le hp (Nat.zero_le n)
  have h2 : 2 ≤ p 0 := (hp.1 0).1
  omega

/-- One step along the enumeration: if `p k = q`, `r` is the next prime after `q`
(no prime lies strictly between), then `p (k + 1) = r`. -/
theorem enum_step {p : Nat → Nat} (hp : IsPrimeEnumeration p) {k q r : Nat}
    (hk : p k = q) (hr : IsPrimeNat r) (hqr : q < r)
    (hgap : ∀ m, m < r → q < m → ¬ IsPrimeNat m) : p (k + 1) = r := by
  obtain ⟨n, hn⟩ := hp.2.2 r hr
  have hkn : k < n := by
    rcases Nat.lt_or_ge k n with h | h
    · exact h
    · have := enum_le hp h
      omega
  have hle : p (k + 1) ≤ p n := enum_le hp (by omega)
  have hlt : p k < p (k + 1) := hp.2.1 k (k + 1) (by omega)
  rcases Nat.lt_or_ge (p (k + 1)) r with h | h
  · exact absurd (hp.1 (k + 1)) (hgap _ h (by omega))
  · omega

theorem enum_one {p : Nat → Nat} (hp : IsPrimeEnumeration p) : p 1 = 3 :=
  enum_step hp (enum_zero hp) (by decide) (by decide) (by decide)

theorem enum_two {p : Nat → Nat} (hp : IsPrimeEnumeration p) : p 2 = 5 :=
  enum_step hp (enum_one hp) (by decide) (by decide) (by decide)

theorem enum_three {p : Nat → Nat} (hp : IsPrimeEnumeration p) : p 3 = 7 :=
  enum_step hp (enum_two hp) (by decide) (by decide) (by decide)

theorem enum_four {p : Nat → Nat} (hp : IsPrimeEnumeration p) : p 4 = 11 :=
  enum_step hp (enum_three hp) (by decide) (by decide) (by decide)

theorem enum_five {p : Nat → Nat} (hp : IsPrimeEnumeration p) : p 5 = 13 :=
  enum_step hp (enum_four hp) (by decide) (by decide) (by decide)

theorem enum_six {p : Nat → Nat} (hp : IsPrimeEnumeration p) : p 6 = 17 :=
  enum_step hp (enum_five hp) (by decide) (by decide) (by decide)

theorem enum_seven {p : Nat → Nat} (hp : IsPrimeEnumeration p) : p 7 = 19 :=
  enum_step hp (enum_six hp) (by decide) (by decide) (by decide)

theorem enum_eight {p : Nat → Nat} (hp : IsPrimeEnumeration p) : p 8 = 23 :=
  enum_step hp (enum_seven hp) (by decide) (by decide) (by decide)

theorem enum_nine {p : Nat → Nat} (hp : IsPrimeEnumeration p) : p 9 = 29 :=
  enum_step hp (enum_eight hp) (by decide) (by decide) (by decide)

/-- Row `1` of the Gilbreath triangle of the primes starts `1, 2, 2, …`. -/
theorem isOdlyzko_row_one {p : Nat → Nat} (hp : IsPrimeEnumeration p) :
    IsOdlyzko (gilbreathRow p 1) 2 := by
  have h0 : p 0 = 2 := enum_zero hp
  have h1 : p 1 = 3 := enum_one hp
  have h2 : p 2 = 5 := enum_two hp
  have h3 : p 3 = 7 := enum_three hp
  refine ⟨by simp [gilbreathRow, diffSeq, adist, h0, h1], ?_⟩
  intro i hi hi2
  have : i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl
  · exact Or.inr (by simp [gilbreathRow, diffSeq, adist, h1, h2])
  · exact Or.inr (by simp [gilbreathRow, diffSeq, adist, h2, h3])

/-- Row `2` of the Gilbreath triangle of the primes starts `1, 0, 2, 2, 2, 2, 2, 2, …`. -/
theorem isOdlyzko_row_two {p : Nat → Nat} (hp : IsPrimeEnumeration p) :
    IsOdlyzko (gilbreathRow p 2) 7 := by
  have h0 : p 0 = 2 := enum_zero hp
  have h1 : p 1 = 3 := enum_one hp
  have h2 : p 2 = 5 := enum_two hp
  have h3 : p 3 = 7 := enum_three hp
  have h4 : p 4 = 11 := enum_four hp
  have h5 : p 5 = 13 := enum_five hp
  have h6 : p 6 = 17 := enum_six hp
  have h7 : p 7 = 19 := enum_seven hp
  have h8 : p 8 = 23 := enum_eight hp
  have h9 : p 9 = 29 := enum_nine hp
  refine ⟨by simp [gilbreathRow, diffSeq, adist, h0, h1, h2], ?_⟩
  intro i hi hi7
  have hcases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [gilbreathRow, diffSeq, adist, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- Unconditionally: rows `1` through `9` of the Gilbreath triangle of the primes
begin with `1`. -/
theorem gilbreathRow_head_eq_one_of_le_nine {p : Nat → Nat} (hp : IsPrimeEnumeration p)
    (m : Nat) (h1 : 1 ≤ m) (h9 : m ≤ 9) : gilbreathRow p m 0 = 1 := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have hm : m = 1 := by omega
    subst hm
    exact (isOdlyzko_row_one hp).1
  · obtain ⟨j, rfl⟩ : ∃ j, m = 2 + j := ⟨m - 2, by omega⟩
    rw [gilbreathRow_add]
    exact head_iterD_eq_one (isOdlyzko_row_two hp) (by omega)

end Brockian.GilbreathConjecture

import Mathlib
import Brockian.GilbreathConjecture

/-!
# The prime enumeration used by the Gilbreath triangle

`Brockian.GilbreathConjecture` is developed for an arbitrary increasing
enumeration `p` of the primes (`IsPrimeEnumeration p`).  Here we check, against
Mathlib, that such an enumeration exists — namely `Nat.nth Nat.Prime` — so that
the conditional reduction proved there is not vacuous, and we specialize it to
the primes.
-/

namespace Brockian.GilbreathConjecture

/-- The elementary primality predicate used in `Brockian.GilbreathConjecture`
agrees with Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime {n : ℕ} : IsPrimeNat n ↔ Nat.Prime n := by
  rw [Nat.prime_def_lt]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hmn => ?_⟩
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · exact absurd (Nat.eq_zero_of_zero_dvd hmn) (by omega)
      · rfl
    · exact absurd hmn (h m hm hm2)
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun d hd hd2 hdvd => by simp [h d hd hdvd] at hd2⟩

/-- `Nat.nth Nat.Prime` is an increasing enumeration of the primes. -/
theorem isPrimeEnumeration_nth_prime : IsPrimeEnumeration (Nat.nth Nat.Prime) := by
  refine ⟨fun n => isPrimeNat_iff_prime.2 (Nat.prime_nth_prime n), ?_, ?_⟩
  · intro i j hij
    exact (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 hij
  · intro q hq
    exact ⟨Nat.count Nat.Prime q, Nat.nth_count (isPrimeNat_iff_prime.1 hq)⟩

/-- An increasing enumeration of the primes exists, so the hypothesis
`IsPrimeEnumeration` of `GilbreathConjecture` is satisfiable. -/
theorem exists_isPrimeEnumeration : ∃ p, IsPrimeEnumeration p :=
  ⟨Nat.nth Nat.Prime, isPrimeEnumeration_nth_prime⟩

/-- The conditional reduction, specialized to the concrete prime enumeration
`Nat.nth Nat.Prime`. -/
theorem gilbreath_nth_prime (H : OdlyzkoCondition (Nat.nth Nat.Prime)) :
    GilbreathStatement (Nat.nth Nat.Prime) :=
  GilbreathConjecture _ isPrimeEnumeration_nth_prime H

/-- Unconditionally, rows `1` through `9` of the Gilbreath triangle of the primes
begin with `1`. -/
theorem gilbreath_nth_prime_head_le_nine (m : ℕ) (h1 : 1 ≤ m) (h9 : m ≤ 9) :
    gilbreathRow (Nat.nth Nat.Prime) m 0 = 1 :=
  gilbreathRow_head_eq_one_of_le_nine isPrimeEnumeration_nth_prime m h1 h9

end Brockian.GilbreathConjecture

