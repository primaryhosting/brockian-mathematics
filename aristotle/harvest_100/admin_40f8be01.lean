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

def noDiv (p : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | (k+2) => (p % (k+2) != 0) && noDiv p (k+1)
def isPrimeB (p : Nat) : Bool := 2 ≤ p && noDiv p (p-1)
def hasPrimeIn (a b : Nat) : Bool := (List.range b).any (fun p => decide (a < p) && isPrimeB p)
set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
theorem small : (List.range 101).all
    (fun n => decide (n < 2) || (hasPrimeIn (n*(n-1)) (n*n) && hasPrimeIn (n*n) (n*(n+1)))) = true := by
  decide

/-!
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.OppermannConjecture

/-! ## Primality

This file is deliberately import-free: the required header comment must be the very first
thing in the file, and Lean only accepts `import` lines before any other command.  We
therefore set up from scratch the small amount of primality theory that is needed.  The
companion file `Brockian/OppermannConjectureMathlib.lean` imports Mathlib and proves that
`IsPrimeNat` below agrees with `Nat.Prime`, and hence that `OppermannConjecture` is
equivalent to the statement of Oppermann's conjecture phrased with `Nat.Prime`. -/

/-- `p` is prime: `p ≥ 2` and its only divisors are `1` and `p`. -/
def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- Trial division of `p` by the candidates `k, k+1, …`, stopping as soon as the candidate
exceeds `√p`.  The last argument is a fuel bounding the number of candidates tried. -/
def noDivFrom : Nat → Nat → Nat → Bool
  | _, _, 0 => true
  | p, k, (fuel + 1) =>
      if p < k * k then true
      else if p % k == 0 then false
      else noDivFrom p (k + 1) fuel

/-- Boolean primality test by trial division up to `√p`. -/
def isPrimeB (p : Nat) : Bool := 2 ≤ p && noDivFrom p 2 p

theorem noDivFrom_spec (p : Nat) :
    ∀ fuel k, 0 < k → (noDivFrom p k fuel = true ↔
      ∀ m, k ≤ m → m < k + fuel → m * m ≤ p → p % m ≠ 0) := by
  intro fuel
  induction fuel with
  | zero => intro k hk; simp [noDivFrom]; omega
  | succ fuel ih =>
    intro k hk
    rw [show noDivFrom p k (fuel + 1) =
        (if p < k * k then true
         else if p % k == 0 then false
         else noDivFrom p (k + 1) fuel) from rfl]
    by_cases hlt : p < k * k
    · simp only [hlt, if_pos]
      constructor
      · intro _ m hm _ hmm
        exfalso
        have : k * k ≤ m * m := Nat.mul_le_mul hm hm
        omega
      · intro _; trivial
    · simp only [hlt, if_false]
      by_cases hmod : p % k = 0
      · simp only [hmod, beq_self_eq_true, if_pos]
        constructor
        · intro h; exact absurd h (by simp)
        · intro h
          exact absurd hmod (h k (Nat.le_refl _) (by omega) (by omega))
      · simp only [beq_iff_eq]
        rw [if_neg hmod, ih (k + 1) (by omega)]
        constructor
        · intro h m hm hm2 hmm
          rcases Nat.eq_or_lt_of_le hm with rfl | h1
          · exact hmod
          · exact h m (by omega) (by omega) hmm
        · intro h m hm hm2 hmm
          exact h m (by omega) (by omega) hmm

/-- If a number has a nontrivial divisor, it has one that is at most its square root. -/
theorem exists_small_divisor (p : Nat) :
    ∀ b m, m ≤ b → 2 ≤ m → m ∣ p → m < p → ∃ d, 2 ≤ d ∧ d ∣ p ∧ d * d ≤ p := by
  intro b
  induction b with
  | zero => intro m hmb h2; omega
  | succ b ih =>
    intro m hmb h2 hdvd hmp
    by_cases hsq : m * m ≤ p
    · exact ⟨m, h2, hdvd, hsq⟩
    · obtain ⟨e, he⟩ := hdvd
      have he0 : e ≠ 0 := by rintro rfl; simp at he; omega
      have he1 : e ≠ 1 := by rintro rfl; simp at he; omega
      have hlt : m * e < m * m := by rw [← he]; omega
      have hem : e < m := Nat.lt_of_mul_lt_mul_left hlt
      have hedvd : e ∣ p := ⟨m, by rw [he]; exact Nat.mul_comm m e⟩
      exact ih e (by omega) (by omega) hedvd (by omega)

theorem isPrimeB_iff (p : Nat) : isPrimeB p = true ↔ IsPrimeNat p := by
  constructor
  · intro h
    simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h2, hnd⟩ := h
    rw [noDivFrom_spec p p 2 (by omega)] at hnd
    refine ⟨h2, fun m hm => ?_⟩
    by_cases hm1 : m = 1
    · exact Or.inl hm1
    by_cases hmp : m = p
    · exact Or.inr hmp
    exfalso
    have hp0 : 0 < p := by omega
    have hle : m ≤ p := Nat.le_of_dvd hp0 hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact absurd (Nat.zero_dvd.mp hm) (by omega)
    obtain ⟨d, hd2, hdvd, hdsq⟩ :=
      exists_small_divisor p p m hle (by omega) hm (by omega)
    have hdp : d ≤ p := Nat.le_of_dvd hp0 hdvd
    exact hnd d hd2 (by omega) hdsq (Nat.dvd_iff_mod_eq_zero.mp hdvd)
  · rintro ⟨h2, hdiv⟩
    simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨h2, ?_⟩
    rw [noDivFrom_spec p p 2 (by omega)]
    intro m hm hmk hmm hmod
    rcases hdiv m (Nat.dvd_of_mod_eq_zero hmod) with h1 | h1
    · omega
    · subst h1
      have : 2 * m ≤ m * m := Nat.mul_le_mul_right m hm
      omega

/-! ## Statements -/

/-- **Oppermann's conjecture**: for every `n > 1` there is a prime strictly between
`n(n-1)` and `n²`, and a prime strictly between `n²` and `n(n+1)`.

This is a famous open problem: it is strictly stronger than Legendre's conjecture and than
Bertrand's postulate.  It is stated here as a `Prop`; below we give an unconditional
verification for `n ≤ 200`, a conditional reduction from a square-root prime-gap hypothesis,
and some consequences. -/
def OppermannConjecture : Prop :=
  ∀ n : Nat, 1 < n →
    (∃ p : Nat, IsPrimeNat p ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ p : Nat, IsPrimeNat p ∧ n * n < p ∧ p < n * (n + 1))

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between `n²` and
`(n+1)²`.  Also open. -/
def LegendreConjecture : Prop :=
  ∀ n : Nat, 1 ≤ n → ∃ p : Nat, IsPrimeNat p ∧ n * n < p ∧ p < (n + 1) * (n + 1)

/-- A square-root prime-gap hypothesis: for `m ≥ 1000`, every interval `(m, m + k)` with
`k² ≤ m` (i.e. of length at least `√m`) contains a prime.  This is a standard, still open,
conjectural strengthening of known prime-gap bounds; the threshold `1000` excludes the small
counterexamples (such as `m = 24`, where the interval `(24, 28)` contains no prime). -/
def SqrtGapHypothesis : Prop :=
  ∀ m k : Nat, 1000 ≤ m → k * k ≤ m → ∃ p : Nat, IsPrimeNat p ∧ m < p ∧ p < m + k

/-! ## Unconditional verification for small `n` -/

/-- `hasPrimeIn a b = true` witnesses a prime strictly between `a` and `b`. -/
def hasPrimeIn (a b : Nat) : Bool := (List.range' (a + 1) (b - a - 1)).any isPrimeB

theorem hasPrimeIn_spec {a b : Nat} (h : hasPrimeIn a b = true) :
    ∃ p : Nat, IsPrimeNat p ∧ a < p ∧ p < b := by
  simp only [hasPrimeIn, List.any_eq_true, List.mem_range'_1] at h
  obtain ⟨p, ⟨hp1, hp2⟩, hpp⟩ := h
  exact ⟨p, (isPrimeB_iff p).mp hpp, by omega, by omega⟩

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
/-- Kernel verification of both prime intervals for every `n ≤ 200`. -/
theorem oppermann_check_le_200 :
    (List.range 201).all
      (fun n => decide (n < 2) ||
        (hasPrimeIn (n * (n - 1)) (n * n) && hasPrimeIn (n * n) (n * (n + 1)))) = true := by
  decide

/-- Unconditional partial result: Oppermann's conjecture holds for `1 < n ≤ 200`. -/
theorem oppermann_of_le_200 (n : Nat) (hn : 1 < n) (hn' : n ≤ 200) :
    (∃ p : Nat, IsPrimeNat p ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ p : Nat, IsPrimeNat p ∧ n * n < p ∧ p < n * (n + 1)) := by
  have h := List.all_eq_true.mp oppermann_check_le_200 n (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with h | ⟨h1, h2⟩
  · omega
  · exact ⟨hasPrimeIn_spec h1, hasPrimeIn_spec h2⟩

/-! ## Conditional reduction -/

private theorem sq_pred_lt (n : Nat) (hn : 1 ≤ n) : n * (n - 1) + (n - 1) < n * n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_succ]
  exact Nat.add_lt_add_left (by omega) _

/-- **Conditional reduction**: the square-root prime-gap hypothesis implies Oppermann's
conjecture.  (The remaining small cases are verified unconditionally above.) -/
theorem oppermann_of_sqrtGap (H : SqrtGapHypothesis) : OppermannConjecture := by
  intro n hn
  by_cases hsmall : n ≤ 200
  · exact oppermann_of_le_200 n hn hsmall
  have h33 : 33 ≤ n := by omega
  constructor
  · have hk : (n - 1) * (n - 1) ≤ n * (n - 1) :=
      Nat.mul_le_mul_right _ (Nat.sub_le n 1)
    have hm : 1000 ≤ n * (n - 1) :=
      Nat.le_trans (by decide) (Nat.mul_le_mul h33 (by omega : 32 ≤ n - 1))
    obtain ⟨p, hp, hp1, hp2⟩ := H (n * (n - 1)) (n - 1) hm hk
    exact ⟨p, hp, hp1, Nat.lt_trans hp2 (sq_pred_lt n (by omega))⟩
  · have hm : 1000 ≤ n * n := Nat.le_trans (by decide) (Nat.mul_le_mul h33 h33)
    obtain ⟨p, hp, hp1, hp2⟩ := H (n * n) n hm (Nat.le_refl _)
    refine ⟨p, hp, hp1, ?_⟩
    rw [Nat.mul_succ]
    exact hp2

/-! ## Consequences -/

/-- Oppermann's conjecture implies Legendre's conjecture. -/
theorem legendre_of_oppermann (H : OppermannConjecture) : LegendreConjecture := by
  intro n hn
  by_cases h1 : n = 1
  · subst h1
    exact ⟨3, (isPrimeB_iff 3).mp (by decide), by omega, by omega⟩
  · obtain ⟨-, p, hp, hp1, hp2⟩ := H n (by omega)
    exact ⟨p, hp, hp1,
      Nat.lt_of_lt_of_le hp2 (Nat.mul_le_mul_right _ (Nat.le_succ n))⟩

/-- Oppermann's conjecture implies the strong Bertrand-type statement that there is a prime
strictly between `n²` and `n² + n`. -/
theorem exists_prime_between_sq_of_oppermann (H : OppermannConjecture) (n : Nat) (hn : 1 < n) :
    ∃ p : Nat, IsPrimeNat p ∧ n * n < p ∧ p < n * n + n := by
  obtain ⟨-, p, hp, hp1, hp2⟩ := H n hn
  rw [Nat.mul_succ] at hp2
  exact ⟨p, hp, hp1, hp2⟩

end Brockian.OppermannConjecture

import Mathlib
import Brockian.OppermannConjecture

/-!
# Bridge between the import-free Oppermann file and Mathlib

`Brockian/OppermannConjecture.lean` must begin with a fixed header comment, which forces it
to be import-free.  Here we check that its self-contained notion of primality coincides with
Mathlib's `Nat.Prime`, and consequently that `Brockian.OppermannConjecture.OppermannConjecture`
is equivalent to the statement of Oppermann's conjecture phrased with `Nat.Prime`.
-/

namespace Brockian.OppermannConjecture

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime (p : ℕ) : IsPrimeNat p ↔ Nat.Prime p :=
  Nat.prime_def.symm

/-- Oppermann's conjecture phrased with Mathlib's `Nat.Prime`. -/
def OppermannConjectureMathlib : Prop :=
  ∀ n : ℕ, 1 < n →
    (∃ p : ℕ, Nat.Prime p ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ p : ℕ, Nat.Prime p ∧ n * n < p ∧ p < n * (n + 1))

/-- The two formulations agree. -/
theorem oppermannConjecture_iff_mathlib :
    OppermannConjecture ↔ OppermannConjectureMathlib := by
  unfold OppermannConjecture OppermannConjectureMathlib
  simp only [isPrimeNat_iff_prime]

/-- The unconditional small-case verification, phrased with `Nat.Prime`. -/
theorem oppermann_mathlib_of_le_200 (n : ℕ) (hn : 1 < n) (hn' : n ≤ 200) :
    (∃ p : ℕ, Nat.Prime p ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ p : ℕ, Nat.Prime p ∧ n * n < p ∧ p < n * (n + 1)) := by
  simpa only [isPrimeNat_iff_prime] using oppermann_of_le_200 n hn hn'

end Brockian.OppermannConjecture

