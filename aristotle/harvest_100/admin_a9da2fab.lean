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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.GoldbachSchema

/-! ## The statements -/

/-- `GoldbachPair n` : `n` is a sum of two primes. -/
def GoldbachPair (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- `TernaryRep n` : `n` is a sum of three primes. -/
def TernaryRep (n : ℕ) : Prop := ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n

/-- `GoldbachModel N` : the binary Goldbach property, verified for all even numbers
between `4` and `N`.  (For `N` unbounded this is Goldbach's conjecture.) -/
def GoldbachModel (N : ℕ) : Prop := ∀ n : ℕ, 4 ≤ n → n ≤ N → Even n → GoldbachPair n

/-! ## The schema: a binary model reaches three primes for odd numbers beyond it -/

/-- **Schema.** A Goldbach model valid up to `N` yields a representation as a sum of three
primes for every odd number `n` with `9 ≤ n ≤ N + 3`, i.e. reaching `3` beyond the range
of the model. -/
theorem ternary_of_model {N : ℕ} (model : GoldbachModel N) :
    ∀ n : ℕ, Odd n → 9 ≤ n → n ≤ N + 3 → TernaryRep n := by
  intro n hodd h9 hle
  obtain ⟨k, hk⟩ := hodd
  have heven : Even (n - 3) := ⟨k - 1, by omega⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := model (n - 3) (by omega) (by omega) heven
  exact ⟨p, q, 3, hp, hq, Nat.prime_three, by omega⟩

/-! ## A kernel-checkable primality certificate -/

/-- `noDiv n k = true` iff no `m` with `2 ≤ m ≤ k` divides `n`. -/
def noDiv (n : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | (k + 1) => (n % (k + 1) != 0) && noDiv n k

theorem noDiv_iff (n : ℕ) : ∀ k : ℕ, noDiv n k = true ↔ ∀ m : ℕ, 2 ≤ m → m ≤ k → ¬ (m ∣ n) := by
  intro k
  induction k with
  | zero => simp [noDiv]; omega
  | succ k ih =>
    match k with
    | 0 => simp [noDiv]; omega
    | (j + 1) =>
      simp only [noDiv, Bool.and_eq_true, bne_iff_ne, ne_eq, ih]
      constructor
      · rintro ⟨h1, h2⟩ m hm hmk
        rcases Nat.lt_or_ge m (j + 2) with h | h
        · exact h2 m hm (by omega)
        · have hmj : m = j + 2 := by omega
          subst hmj
          exact fun hd => h1 (Nat.mod_eq_zero_of_dvd hd)
      · intro h
        refine ⟨?_, fun m hm hmk => h m hm (by omega)⟩
        exact fun hc => h (j + 2) (by omega) (by omega) (Nat.dvd_of_mod_eq_zero hc)

/-- Trial-division primality certificate: `k` is a trial-division bound, valid whenever
`n < (k+1)^2`. -/
def primeCert (k n : ℕ) : Bool := (2 ≤ n) && (n < (k + 1) * (k + 1)) && noDiv n (min k (n - 1))

theorem primeCert_sound {k n : ℕ} (h : primeCert k n = true) : n.Prime := by
  simp only [primeCert, Bool.and_eq_true, decide_eq_true_eq, noDiv_iff] at h
  obtain ⟨⟨h2, hlt⟩, hnd⟩ := h
  refine Nat.prime_def_le_sqrt.mpr ⟨h2, fun m hm hms => hnd m hm ?_⟩
  have h1 : Nat.sqrt n < k + 1 := Nat.sqrt_lt'.mpr (by simpa [pow_two] using hlt)
  have h2' : Nat.sqrt n < n := Nat.sqrt_lt_self (by omega)
  omega

/-! ## The verified finite model -/

/-- The small primes used as the first summand of the Goldbach representations. -/
def smallP : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
   101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
   197, 199]

/-- Boolean search for a Goldbach representation of `n`, with trial-division bound `k`. -/
def gPair (k n : ℕ) : Bool := smallP.any (fun p => primeCert k p && primeCert k (n - p))

theorem gPair_sound {k n : ℕ} (h : gPair k n = true) : GoldbachPair n := by
  simp only [gPair, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨p, -, hp, hq⟩ := h
  have hp' : p.Prime := primeCert_sound hp
  have hq' : (n - p).Prime := primeCert_sound hq
  refine ⟨p, n - p, hp', hq', ?_⟩
  have := hq'.two_le
  omega

/-- `allBelow f M = true` iff `f m = true` for all `m < M`. -/
def allBelow (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | (m + 1) => f m && allBelow f m

theorem allBelow_sound {f : ℕ → Bool} : ∀ {M m : ℕ}, allBelow f M = true → m < M → f m = true := by
  intro M
  induction M with
  | zero => intro m _ hm; omega
  | succ M ih =>
    intro m h hm
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge m M with hlt | hge
    · exact ih h.2 hlt
    · have hmM : m = M := by omega
      subst hmM
      exact h.1

/-- Boolean check of the binary Goldbach property for all even `n = 2 * m + 4` with `m < M`. -/
def gCheck (k M : ℕ) : Bool := allBelow (fun m => gPair k (2 * m + 4)) M

theorem model_of_gCheck {k M : ℕ} (h : gCheck k M = true) : GoldbachModel (2 * M + 2) := by
  intro n h4 hle heven
  obtain ⟨t, ht⟩ := heven
  have hm : n = 2 * (t - 2) + 4 := by omega
  have hlt : t - 2 < M := by omega
  rw [hm]
  exact gPair_sound (allBelow_sound (f := fun m => gPair k (2 * m + 4)) h hlt)

/-- The binary Goldbach property, verified by kernel computation for every even number
between `4` and `2002`. -/
theorem goldbach_model_2002 : GoldbachModel 2002 :=
  model_of_gCheck (k := 44) (M := 1000) (by decide +kernel)

/-! ## The target: the model hypothesis discharged -/

/-- **Goldbach beyond, with the model hypothesis discharged.**

Every odd number `n` with `9 ≤ n ≤ 2005` is a sum of three primes.

This is the conclusion of the schema `ternary_of_model`, whose `GoldbachModel` hypothesis has
been discharged unconditionally (by the kernel-checked computation `goldbach_model_2002`), so
the statement below carries no hypotheses beyond the arithmetic constraints on `n`.
The corresponding statement for all odd `n ≥ 9` would follow from the schema applied to an
unbounded model, i.e. from Goldbach's conjecture, which remains open. -/
theorem goldbach_beyond_of_model (n : ℕ) (hodd : Odd n) (h9 : 9 ≤ n) (hle : n ≤ 2005) :
    TernaryRep n :=
  ternary_of_model goldbach_model_2002 n hodd h9 hle

end Brockian.GoldbachSchema

