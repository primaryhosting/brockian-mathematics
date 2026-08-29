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
