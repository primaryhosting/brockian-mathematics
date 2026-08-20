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

theorem prime_dvd_cullen_progression {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    p ∣ cullen (p - 2 + k * (p * (p - 1))) := by
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
  set n := p - 2 + k * (p * (p - 1)) with hn
  have hcast : ((cullen n : ℕ) : ZMod p) = 0 := by
    have hidx : ((n : ℕ) : ZMod p) = -2 := by
      have hsub : ((p - 2 : ℕ) : ZMod p) = -2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ p), ZMod.natCast_self]
        push_cast
        ring
      have : ((n : ℕ) : ZMod p) = ((p - 2 : ℕ) : ZMod p) + k * ((p : ZMod p) * ((p - 1 : ℕ))) := by
        rw [hn]; push_cast; ring
      rw [this, hsub, ZMod.natCast_self]
      ring
    have hpow : (2 : ZMod p) ^ n = 2 ^ (p - 2) := by
      have hsplit : n = (p - 2) + (p - 1) * (k * p) := by
        rw [hn]; ring
      rw [hsplit, pow_add, pow_mul, hferm, one_pow, mul_one]
    have hexp : (2 : ZMod p) * 2 ^ (p - 2) = 2 ^ (p - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hkey : (-2 : ZMod p) * 2 ^ (p - 2) = -(2 ^ (p - 1)) := by
      rw [← hexp]; ring
    have : ((cullen n : ℕ) : ZMod p) = ((n : ℕ) : ZMod p) * 2 ^ n + 1 := by
      simp [cullen]
    rw [this, hidx, hpow, hkey, hferm]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

/-- For every odd prime `p`, the prime `p` divides the Cullen number `C (p - 2)`. -/
