import Mathlib
import RequestProject.GoldbachWheelK2_1051

/-!
# Bridge: the import-free primality predicate agrees with `Nat.Prime`

`RequestProject/GoldbachWheelK2_1051.lean` is import-free (so that the required header comment
is the first thing in the file) and therefore uses its own definition `Brockian.IsPrime`.
Here we check that this predicate is literally `Nat.Prime`, and restate the main theorem
in Mathlib's vocabulary.
-/

namespace Brockian

theorem isPrime_iff_nat_prime (n : ℕ) : IsPrime n ↔ Nat.Prime n := by
  rw [Nat.prime_def]
  rfl

/-- Mathlib-flavoured restatement of `Brockian.GoldbachWheelK2_1051`: every even `m` with
`4 ≤ m ≤ 2 * 1051` is a sum of two primes. -/
theorem GoldbachWheelK2_1051' (m : ℕ) (hm : Even m) (h4 : 4 ≤ m) (hle : m ≤ 2 * 1051) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = m := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    GoldbachWheelK2_1051 m (even_iff_two_dvd.mp hm) h4 hle
  exact ⟨p, q, (isPrime_iff_nat_prime p).mp hp, (isPrime_iff_nat_prime q).mp hq, hpq⟩

end Brockian

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Brockian

/-- Primality of a natural number, stated from first principles: `n` is prime when `2 ≤ n`
and its only divisors are `1` and `n`.  (This file is deliberately import-free, so that the
header comment above is the very first thing in the file; `Brockian.isPrime_iff_nat_prime`
in `RequestProject/GoldbachWheelK2_1051_Bridge.lean` shows this agrees with `Nat.Prime`.) -/
def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

/-- A kernel-friendly primality test: trial division by every `d` with `2 ≤ d ≤ 45`.
It is sound for inputs `n ≤ 2102`, since `46 * 46 = 2116 > 2102`. -/
def isPrimeSmall (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range' 2 44).all (fun d => n % d != 0 || n == d)

/-- Search for a decomposition `2 * n = p + q` into two primes with `p ≤ 200`. -/
def goldbachCheck (n : Nat) : Bool :=
  (List.range' 2 199).any (fun p => isPrimeSmall p && isPrimeSmall (2 * n - p))

/-- Soundness of the trial-division test on the relevant range. -/
theorem isPrimeSmall_correct {n : Nat} (hn : n ≤ 2102) (h : isPrimeSmall n = true) :
    IsPrime n := by
  rw [isPrimeSmall, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hall⟩ := h
  have key : ∀ d : Nat, 2 ≤ d → d ≤ 45 → d ∣ n → d = n := by
    intro d hd2 hd45 hdvd
    have hmem : d ∈ List.range' 2 44 := List.mem_range'.mpr ⟨d - 2, by omega, by omega⟩
    have hc := List.all_eq_true.mp hall d hmem
    simp only [bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true] at hc
    obtain ⟨k, hk⟩ := hdvd
    have hmod : n % d = 0 := by rw [hk]; exact Nat.mul_mod_right d k
    rcases hc with hc | hc
    · exact absurd hmod hc
    · omega
  refine ⟨h2, fun m hm => ?_⟩
  obtain ⟨e, he⟩ := hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at he; omega
  have he0 : e ≠ 0 := by rintro rfl; simp at he; omega
  rcases Nat.lt_or_ge m 2 with hlt | hm2
  · exact Or.inl (by omega)
  refine Or.inr ?_
  rcases Nat.lt_or_ge m 46 with hs | hbig
  · exact key m hm2 (by omega) ⟨e, he⟩
  · rcases Nat.lt_or_ge e 2 with he1 | he2
    · have hE : e = 1 := by omega
      subst hE
      omega
    · rcases Nat.lt_or_ge e 46 with hle45 | hbg
      · have hen : e = n := key e he2 (by omega) ⟨m, by rw [he]; exact Nat.mul_comm m e⟩
        subst hen
        have : 2 * e ≤ m * e := Nat.mul_le_mul_right e hm2
        omega
      · have h1 : 46 * 46 ≤ m * e := Nat.mul_le_mul hbig hbg
        rw [← he] at h1
        omega

/-- A successful search yields an honest Goldbach decomposition. -/
theorem goldbach_of_check {n : Nat} (hn : 2 ≤ n) (hle : n ≤ 1051) (h : goldbachCheck n = true) :
    ∃ p q : Nat, IsPrime p ∧ IsPrime q ∧ p + q = 2 * n := by
  rw [goldbachCheck, List.any_eq_true] at h
  obtain ⟨p, hp, hpc⟩ := h
  rw [Bool.and_eq_true] at hpc
  have hp200 : p ≤ 200 := by
    rw [List.mem_range'] at hp
    omega
  have hP : IsPrime p := isPrimeSmall_correct (by omega) hpc.1
  have hQ : IsPrime (2 * n - p) := isPrimeSmall_correct (by omega) hpc.2
  have hq2 : 2 ≤ 2 * n - p := hQ.1
  exact ⟨p, 2 * n - p, hP, hQ, by omega⟩

theorem mem_range'_of_le {s len n : Nat} (h1 : s ≤ n) (h2 : n < s + len) :
    n ∈ List.range' s len :=
  List.mem_range'.mpr ⟨n - s, by omega, by omega⟩

theorem check_chunk₁ : (List.range' 2 175).all goldbachCheck = true := by decide
theorem check_chunk₂ : (List.range' 177 175).all goldbachCheck = true := by decide
theorem check_chunk₃ : (List.range' 352 175).all goldbachCheck = true := by decide
theorem check_chunk₄ : (List.range' 527 175).all goldbachCheck = true := by decide
theorem check_chunk₅ : (List.range' 702 175).all goldbachCheck = true := by decide
theorem check_chunk₆ : (List.range' 877 175).all goldbachCheck = true := by decide

theorem goldbachCheck_of_le {n : Nat} (hn : 2 ≤ n) (hle : n ≤ 1051) : goldbachCheck n = true := by
  have key : ∀ {s : Nat}, (List.range' s 175).all goldbachCheck = true → s ≤ n → n < s + 175 →
      goldbachCheck n = true := fun h h1 h2 =>
    List.all_eq_true.mp h n (mem_range'_of_le h1 h2)
  rcases (by omega : n < 177 ∨ (177 ≤ n ∧ n < 352) ∨ (352 ≤ n ∧ n < 527) ∨
      (527 ≤ n ∧ n < 702) ∨ (702 ≤ n ∧ n < 877) ∨ (877 ≤ n ∧ n < 1052)) with
    h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
  · exact key check_chunk₁ hn (by omega)
  · exact key check_chunk₂ h (by omega)
  · exact key check_chunk₃ h (by omega)
  · exact key check_chunk₄ h (by omega)
  · exact key check_chunk₅ h (by omega)
  · exact key check_chunk₆ h (by omega)

/-- **Goldbach wheel, `K = 2`, modulus `1051`:** every even number `m` with
`4 ≤ m ≤ 2 * 1051` is the sum of two primes. -/
theorem GoldbachWheelK2_1051 :
    ∀ m : Nat, 2 ∣ m → 4 ≤ m → m ≤ 2 * 1051 →
      ∃ p q : Nat, IsPrime p ∧ IsPrime q ∧ p + q = m := by
  intro m hm h4 hle
  obtain ⟨k, hk⟩ := hm
  have hk2 : 2 ≤ k := by omega
  have hk1051 : k ≤ 1051 := by omega
  obtain ⟨p, q, hp, hq, hpq⟩ := goldbach_of_check hk2 hk1051 (goldbachCheck_of_le hk2 hk1051)
  exact ⟨p, q, hp, hq, by omega⟩

end Brockian

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

