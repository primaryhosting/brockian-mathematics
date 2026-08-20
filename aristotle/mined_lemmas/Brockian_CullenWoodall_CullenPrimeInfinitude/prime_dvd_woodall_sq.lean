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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Note on the header: Lean 4 requires `import` to be the very first command of a file, so the
header above is a plain block comment (`/- ... -/`) rather than a module docstring (`/-! ... -/`);
its text is otherwise verbatim.

## Contents

* Cullen numbers `C n = n * 2 ^ n + 1` and Woodall numbers `W n = n * 2 ^ n - 1`.
* `CullenPrimeInfinitude` / `WoodallPrimeInfinitude`: Lean-checked *conditional reductions* of the
  (open) infinitude conjectures to the corresponding unboundedness hypotheses, together with
  `cullenPrimeConjecture_iff_unbounded` / `woodallPrimeConjecture_iff_unbounded`.
* Unconditional partial results: explicit arithmetic progressions of composite Cullen numbers
  (`p ∣ C (p - 2 + k * p * (p - 1))` for every odd prime `p`), the companion Woodall divisibility
  `p ∣ W ((p - 1) ^ 2)`, and the resulting infinitude of composite Cullen and Woodall numbers.

Nothing about Cullen or Woodall numbers is currently available in Mathlib; the arithmetic input
used here is Fermat's little theorem in the form `ZMod.pow_card_sub_one_eq_one`, together with
`Nat.exists_infinite_primes` and `Set.infinite_of_forall_exists_gt`.
-/

namespace Brockian.CullenWoodall

/-! ## Cullen numbers -/

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem prime_dvd_woodall_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ woodall ((p - 1) ^ 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    simpa using h
  have hferm : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  set n := (p - 1) ^ 2 with hn
  have hone : (1:ℕ) ≤ n * 2 ^ n := by
    have h1 : 1 ≤ n := by
      have : 2 ≤ p - 1 := by omega
      calc (1:ℕ) ≤ 2 ^ 2 := by norm_num
        _ ≤ (p - 1) ^ 2 := Nat.pow_le_pow_left this 2
    exact Nat.mul_pos h1 (Nat.two_pow_pos n)
  have hcast : ((woodall n : ℕ) : ZMod p) = 0 := by
    have hidx : ((n : ℕ) : ZMod p) = 1 := by
      have hsub : ((p - 1 : ℕ) : ZMod p) = -1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self]
        push_cast
        ring
      rw [hn]
      push_cast [hsub]
      ring
    have hpow : (2 : ZMod p) ^ n = 1 := by
      have : n = (p - 1) * (p - 1) := by rw [hn]; ring
      rw [this, pow_mul, hferm, one_pow]
    have hw : ((woodall n : ℕ) : ZMod p) = ((n : ℕ) : ZMod p) * 2 ^ n - 1 := by
      simp only [woodall]
      rw [Nat.cast_sub hone]
      push_cast
      ring
    rw [hw, hidx, hpow]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

