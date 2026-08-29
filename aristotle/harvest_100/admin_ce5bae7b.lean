/-!
# Two Squares 109
Category: Pure Mathematics
Target: Math.two_squares_109
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Primality of a natural number, stated elementarily: `n` is at least `2` and its only
proper divisor is `1`.  (See `Math.isPrimeNat_iff_prime` in `RequestProject.MathMathlib`
for the proof that this agrees with Mathlib's `Nat.Prime`.) -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m < n → m ∣ n → m = 1

/-- **Two squares, 109.**  The prime `109` is a sum of two squares: `109 = 10 ^ 2 + 3 ^ 2`. -/
theorem two_squares_109 : IsPrimeNat 109 ∧ ∃ a b : Nat, 109 = a ^ 2 + b ^ 2 :=
  ⟨⟨by decide, by decide⟩, 10, 3, by decide⟩

end Math

import Mathlib
import RequestProject.Math

/-!
# Two Squares 109 — Mathlib companion file

`RequestProject.Math` states and proves the target `Math.two_squares_109` in a
self-contained way (Lean requires `import` lines to precede every other command, so the
target file, which must begin with its header comment, carries no imports).

Here we connect it to Mathlib: `Math.IsPrimeNat` agrees with `Nat.Prime`, and the
existence of a two-square representation also follows abstractly from Mathlib's
`Nat.Prime.sq_add_sq` (Fermat's two-square theorem) since `109 % 4 = 1 ≠ 3`.
-/

namespace Math

/-- The elementary primality predicate used in the target statement agrees with
Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime (n : ℕ) : IsPrimeNat n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨hn, h⟩
    refine Nat.prime_def.mpr ⟨hn, fun m hm => ?_⟩
    rcases lt_or_eq_of_le (Nat.le_of_dvd (by omega) hm) with hlt | heq
    · exact Or.inl (h m hlt hm)
    · exact Or.inr heq
  · intro hp
    refine ⟨hp.two_le, fun m hm hmd => ?_⟩
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp m hmd) with h | h
    · exact h
    · omega

/-- `109` is prime, in Mathlib's sense. -/
theorem prime_109 : Nat.Prime 109 := (isPrimeNat_iff_prime 109).mp two_squares_109.1

/-- The abstract route: Fermat's two-square theorem `Nat.Prime.sq_add_sq` applied to `109`,
which is `1 mod 4`. -/
theorem sq_add_sq_109_of_mathlib : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 109 :=
  haveI : Fact (Nat.Prime 109) := ⟨prime_109⟩
  Nat.Prime.sq_add_sq (by norm_num)

end Math

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

