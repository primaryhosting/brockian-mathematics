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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.SophieGermain

/-- `p` is a *Sophie Germain prime* if both `p` and `2 * p + 1` are prime. -/
def IsSophieGermain (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

theorem isSophieGermain_two : IsSophieGermain 2 := by
  constructor <;> norm_num

theorem isSophieGermain_eleven : IsSophieGermain 11 := by
  constructor <;> norm_num

/-- A finite family `F` of linear forms, each pair `(a, b)` standing for the form
`n ↦ a * n + b`, is *admissible* when no prime divides the product of the values of the
forms at every integer point: for each prime `q` there is some `n` at which none of the
values is divisible by `q`. -/
def Admissible (F : List (ℕ × ℕ)) : Prop :=
  ∀ q : ℕ, q.Prime → ∃ n : ℕ, ∀ ab ∈ F, ¬ (q ∣ ab.1 * n + ab.2)

/-- **Dickson's conjecture** (in the special case of linear forms with natural number
coefficients): every admissible finite family of linear forms `n ↦ a * n + b` with `a ≥ 1`
takes simultaneously prime values at arbitrarily large `n`. This is a well-known open
conjecture; it is used here only as a hypothesis. -/
def DicksonHypothesis : Prop :=
  ∀ F : List (ℕ × ℕ), (∀ ab ∈ F, 1 ≤ ab.1) → Admissible F →
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∀ ab ∈ F, (ab.1 * n + ab.2).Prime

/-- The pair of forms `n ↦ n` and `n ↦ 2 * n + 1` relevant to Sophie Germain primes is
admissible. -/
theorem admissible_sophieGermain : Admissible [(1, 0), (2, 1)] := by
  intro q hq
  -- We must find `n` with `q ∤ n` and `q ∤ 2 * n + 1`.
  have key : ∃ n : ℕ, ¬ (q ∣ n) ∧ ¬ (q ∣ 2 * n + 1) := by
    rcases eq_or_ne q 2 with rfl | hq2
    · exact ⟨1, by decide⟩
    rcases eq_or_ne q 3 with rfl | hq3
    · exact ⟨2, by decide⟩
    have hq4 : q ≠ 4 := by rintro rfl; norm_num at hq
    have hq5 : 5 ≤ q := by
      have := hq.two_le
      omega
    have hnd : ∀ n : ℕ, 1 ≤ n → n ≤ 3 → ¬ (q ∣ n) := by
      intro n h1 h3 hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    by_cases h1 : q ∣ 2 * 1 + 1
    · refine ⟨2, hnd 2 (by norm_num) (by norm_num), ?_⟩
      intro h2
      have hsub : q ∣ (2 * 2 + 1) - (2 * 1 + 1) := Nat.dvd_sub h2 h1
      norm_num at hsub
      have := Nat.le_of_dvd (by norm_num) hsub
      omega
    · exact ⟨1, hnd 1 (by norm_num) (by norm_num), h1⟩
  obtain ⟨n, hn1, hn2⟩ := key
  refine ⟨n, ?_⟩
  intro ab hab
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl
  · simpa using hn1
  · simpa using hn2

/-- **Sophie Germain infinitude, conditional on Dickson's conjecture.**
If Dickson's conjecture holds for admissible families of linear forms with natural number
coefficients, then there are infinitely many Sophie Germain primes, i.e. infinitely many
primes `p` for which `2 * p + 1` is also prime. -/
theorem SophieGermainInfinitude (H : DicksonHypothesis) :
    {p : ℕ | IsSophieGermain p}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hnN, hn⟩ :=
    H [(1, 0), (2, 1)] (by intro ab hab; fin_cases hab <;> norm_num)
      admissible_sophieGermain N
  have h1 : (1 * n + 0 : ℕ).Prime := hn (1, 0) (by simp)
  have h2 : (2 * n + 1 : ℕ).Prime := hn (2, 1) (by simp)
  exact ⟨n, ⟨by simpa using h1, h2⟩, hnN⟩

end Brockian.SophieGermain

