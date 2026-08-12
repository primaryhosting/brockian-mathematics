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

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a *Sophie Germain prime* if both `p` and `2 * p + 1` are prime. -/
def IsSophieGermain (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

/-- The set of Sophie Germain primes. -/
def sophieGermainSet : Set ℕ := {p | IsSophieGermain p}

/-! ## Elementary reformulations -/

/-- The set of Sophie Germain primes is infinite iff there are arbitrarily large ones. -/
theorem infinite_sophieGermainSet_iff_unbounded :
    sophieGermainSet.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ IsSophieGermain p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hlt, hp⟩
  · intro h
    exact Set.infinite_of_forall_exists_gt (fun N => by
      obtain ⟨p, hlt, hp⟩ := h N
      exact ⟨p, hp, hlt⟩)

/-! ## Dickson's conjecture -/

/-- A finite family of linear forms `x ↦ aᵢ * x + bᵢ` (encoded as pairs `(aᵢ, bᵢ)`) is
*admissible* if for every prime `q` there is some `n` at which no form is divisible by `q`. -/
def Admissible {k : ℕ} (f : Fin k → ℕ × ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → ∃ n : ℕ, ∀ i, ¬ (q ∣ (f i).1 * n + (f i).2)

/-- **Dickson's conjecture**: any admissible finite family of linear forms with positive
leading coefficients takes simultaneously prime values at arbitrarily large arguments. -/
def DicksonsConjecture : Prop :=
  ∀ (k : ℕ) (f : Fin k → ℕ × ℕ), (∀ i, 0 < (f i).1) → Admissible f →
    ∀ N : ℕ, ∃ n, N < n ∧ ∀ i, ((f i).1 * n + (f i).2).Prime

/-- The pair of forms `x` and `2x + 1` used to define Sophie Germain primes. -/
def sgForms : Fin 2 → ℕ × ℕ := ![(1, 0), (2, 1)]

theorem sgForms_pos : ∀ i, 0 < (sgForms i).1 := by
  intro i
  fin_cases i <;> simp [sgForms]

/-- The pair `(x, 2x+1)` is admissible: no single prime divides one of the two values for
every `x`. -/
theorem admissible_sgForms : Admissible sgForms := by
  intro q hq
  by_cases h3 : q = 3
  · subst h3
    refine ⟨2, ?_⟩
    intro i
    fin_cases i <;> simp [sgForms]
  · refine ⟨1, ?_⟩
    intro i
    fin_cases i <;> simp [sgForms]
    · exact hq.one_lt.ne'
    · intro hdvd
      exact h3 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hdvd)

/-! ## The conditional reduction -/

/-- **Sophie Germain infinitude, conditional on Dickson's conjecture.**

Assuming Dickson's conjecture for admissible families of linear forms, there are infinitely
many Sophie Germain primes, i.e. infinitely many primes `p` with `2 * p + 1` also prime.

(The unconditional statement is a well-known open problem; this is a Lean-checked reduction.) -/
theorem SophieGermainInfinitude (hD : DicksonsConjecture) :
    {p : ℕ | IsSophieGermain p}.Infinite := by
  rw [show {p : ℕ | IsSophieGermain p} = sophieGermainSet from rfl,
    infinite_sophieGermainSet_iff_unbounded]
  intro N
  obtain ⟨n, hn, hprime⟩ := hD 2 sgForms sgForms_pos admissible_sgForms N
  refine ⟨n, hn, ?_, ?_⟩
  · have := hprime 0
    simpa [sgForms] using this
  · have := hprime 1
    simpa [sgForms] using this

/-! ## Unconditional partial results -/

/-- Explicit small Sophie Germain primes. -/
theorem isSophieGermain_examples :
    ∀ p ∈ ({2, 3, 5, 11, 23, 29, 41, 53, 83, 89} : Finset ℕ), IsSophieGermain p := by
  intro p hp
  fin_cases hp <;> exact ⟨by norm_num, by norm_num⟩

/-- The set of Sophie Germain primes is nonempty. -/
theorem sophieGermainSet_nonempty : sophieGermainSet.Nonempty :=
  ⟨2, by unfold sophieGermainSet IsSophieGermain; norm_num⟩

/-- If `p` is a prime with `p ≡ 1 [MOD 3]`, then `3 ∣ 2 * p + 1 < 2 * p + 1`, so `p` is
*not* a Sophie Germain prime. -/
theorem not_isSophieGermain_of_modEq_one_mod_three {p : ℕ} (hp : p.Prime)
    (h : p ≡ 1 [MOD 3]) : ¬ IsSophieGermain p := by
  rintro ⟨-, hq⟩
  have h3 : (3 : ℕ) ∣ 2 * p + 1 := by
    have hmod : p % 3 = 1 % 3 := h
    omega
  have hp2 : 2 ≤ p := hp.two_le
  have : (3 : ℕ) = 2 * p + 1 := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp h3
  omega

/-- **Unconditional partial result**: infinitely many primes are *not* Sophie Germain primes.
Indeed every prime `p ≡ 1 [MOD 3]` fails, and by Dirichlet's theorem there are infinitely
many of those. -/
theorem infinite_setOf_prime_not_sophieGermain :
    {p : ℕ | p.Prime ∧ ¬ IsSophieGermain p}.Infinite := by
  have h := Nat.infinite_setOf_prime_modEq_one (k := 3) (by norm_num)
  refine h.mono ?_
  rintro p ⟨hp, hmod⟩
  exact ⟨hp, not_isSophieGermain_of_modEq_one_mod_three hp hmod⟩

end Brockian.SophieGermain

