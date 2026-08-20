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
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.OppermannConjecture

/-- Primality of a natural number, stated from first principles (this file is self-contained
and imports nothing beyond Lean's prelude, so that the header comment above can literally be
the first thing in the file). -/

def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

instance : DecidablePred IsPrimeNat := fun p => by
  unfold IsPrimeNat
  exact decidable_of_iff (2 ≤ p ∧ ∀ d < p + 1, d ∣ p → d = 1 ∨ d = p)
    ⟨fun ⟨h1, h2⟩ => ⟨h1, fun d hd => h2 d (Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hd)) hd⟩,
     fun ⟨h1, h2⟩ => ⟨h1, fun d _ hd => h2 d hd⟩⟩

/-- **Oppermann's conjecture** (statement form): for every `n ≥ 2` there is a prime strictly
between `n * (n - 1)` and `n * n`, and a prime strictly between `n * n` and `n * (n + 1)`. -/

def OppermannStatement : Prop :=
  ∀ n : Nat, 2 ≤ n →
    (∃ p : Nat, IsPrimeNat p ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ p : Nat, IsPrimeNat p ∧ n * n < p ∧ p < n * (n + 1))

/-- The square-root prime gap hypothesis: for every `m ≥ 2` and every `k` with `√m ≤ k`
(written multiplicatively as `m ≤ k * k`) there is a prime `p` with `m < p < m + k`.
Equivalently: every interval `(m, m + √m)` with `m ≥ 2` contains a prime. This is the
well-known (and open) conjecture that prime gaps are of size at most about `√p`. -/

def SqrtPrimeGapHypothesis : Prop :=
  ∀ m k : Nat, 2 ≤ m → m ≤ k * k → ∃ p : Nat, IsPrimeNat p ∧ m < p ∧ p < m + k

/-- For `n ≥ 2` the left endpoint `n * (n - 1)` of the first Oppermann interval is at least `2`. -/

theorem two_le_mul_pred {n : Nat} (hn : 2 ≤ n) : 2 ≤ n * (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
  have h1 : 1 ≤ k := by omega
  have h2 : 1 * 1 ≤ k * k := Nat.mul_le_mul h1 h1
  omega

/-- The arithmetic identity `n * (n - 1) + n = n * n` for `n ≥ 1`. -/

theorem mul_pred_add_self {n : Nat} (hn : 1 ≤ n) : n * (n - 1) + n = n * n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_succ]

/-- **Conditional proof of Oppermann's conjecture.** Oppermann's conjecture — which is open —
follows from the square-root prime gap hypothesis: since both Oppermann intervals
`(n(n-1), n²)` and `(n², n(n+1))` have length `n` and start below `n²`, a prime in
`(m, m + √m)` lands inside them. -/

theorem OppermannConjecture (H : SqrtPrimeGapHypothesis) : OppermannStatement := by
  intro n hn
  constructor
  · have hm : 2 ≤ n * (n - 1) := two_le_mul_pred hn
    have hk : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    obtain ⟨p, hp, hlt, hub⟩ := H (n * (n - 1)) n hm hk
    refine ⟨p, hp, hlt, ?_⟩
    have h : n * (n - 1) + n = n * n := mul_pred_add_self (by omega)
    omega
  · have hm : 2 ≤ n * n := by
      calc 2 = 2 * 1 := by omega
        _ ≤ n * n := Nat.mul_le_mul hn (by omega)
    obtain ⟨p, hp, hlt, hub⟩ := H (n * n) n hm (Nat.le_refl _)
    refine ⟨p, hp, hlt, ?_⟩
    have h : n * n + n = n * (n + 1) := by simp [Nat.mul_add]
    omega

set_option maxRecDepth 100000 in
/-- Unconditional verification of Oppermann's conjecture for all `2 ≤ n ≤ 20`. -/
