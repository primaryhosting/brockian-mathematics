import Mathlib
import RequestProject.TwoSquares73

/-!
# Two Squares 73 — Mathlib phrasing

Restatements of `Math.two_squares_73` using Mathlib's `Nat.Prime`, over `ℕ` and `ℤ`,
together with a derivation of the existence part from Fermat's two-squares theorem
(`Nat.Prime.sq_add_sq`).
-/

namespace Math

/-- The prime `73` is a sum of two squares: `73 = 3 ^ 2 + 8 ^ 2`. -/
theorem two_squares_73_prime : Nat.Prime 73 ∧ ∃ a b : ℕ, 73 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, two_squares_73.2⟩

/-- The integer version: `73` is prime and a sum of two integer squares. -/
theorem two_squares_73_int : Prime (73 : ℤ) ∧ ∃ a b : ℤ, (73 : ℤ) = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 3, 8, by norm_num⟩

/-- The existence part, obtained instead from Fermat's two-squares theorem: since `73`
is prime and `73 % 4 ≠ 3`, it is a sum of two squares. -/
theorem two_squares_73_of_fermat : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 73 :=
  haveI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  Nat.Prime.sq_add_sq (p := 73) (by norm_num)

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

/-!
# Two Squares 73
Category: Pure Mathematics
Target: Math.two_squares_73
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file must literally begin with the header comment above, so it cannot contain
any `import` command (Lean requires imports to precede every other command,
including module documentation).  The proof below is therefore self-contained and
uses only the Lean 4 core library; primality of `73` is spelled out explicitly.
A Mathlib-phrased corollary, stated with `Nat.Prime`, is proved in
`RequestProject/TwoSquares73Mathlib.lean`.
-/

namespace Math

/-- **73 is a prime that is a sum of two squares.**
Primality is stated elementarily (`1 < 73` and every divisor of `73` is `1` or `73`),
and the representation is `73 = 3 ^ 2 + 8 ^ 2`. -/
theorem two_squares_73 :
    (1 < 73 ∧ ∀ m : Nat, m ∣ 73 → m = 1 ∨ m = 73) ∧ ∃ a b : Nat, 73 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 3, 8, by decide⟩
  have key : ∀ m : Nat, m < 74 → m ∣ 73 → m = 1 ∨ m = 73 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

end Math

