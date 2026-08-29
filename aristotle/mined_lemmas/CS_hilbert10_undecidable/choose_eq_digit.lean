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
import RequestProject.H10.Factorial

/-!
# The product `∏_{k=1}^{y} (a + b*k)` is Diophantine

This is the last of the classical auxiliary Diophantine functions needed for the
Davis–Putnam–Robinson elimination of bounded universal quantifiers.

The idea is that modulo a large `N` coprime to `b`, one has
`∏_{k=1}^{y} (a + b k) ≡ b^y ∏_{k=1}^{y} (m + k) = b^y y! binom(m+y, y)`
where `m` is the residue `a * b⁻¹ mod N`.
-/

namespace H10

open Nat Finset Dioph

/-- `prodAB a b y = (a + b) * (a + 2b) * ⋯ * (a + y b)`. -/

theorem choose_eq_digit (n k u : ℕ) (hu : 2 ^ n < u) :
    n.choose k = digit ((u + 1) ^ n) u k := by
  have hexp : (u + 1) ^ n = ∑ i ∈ range (n + 1), n.choose i * u ^ i := by
    rw [add_pow]; simp [mul_comm]
  have hlt : ∀ i, n.choose i < u := fun i => lt_of_le_of_lt (Nat.choose_le_two_pow n i) hu
  rw [hexp, digit_ofSum u _ hlt]
  by_cases h : k < n + 1
  · rw [if_pos h]
  · rw [if_neg h, Nat.choose_eq_zero_of_lt (by omega)]

end H10

import Mathlib

/-!
# Auxiliary facts about `Poly` and `Dioph`

* `isPoly_support`: a polynomial depends on finitely many variables;
* `isPoly_majorant`: a polynomial is dominated by a monotone polynomial;
* `isPoly_modEq`: polynomials respect congruences;
* `dioph_fin_dummies`: a Diophantine set can be defined using finitely many dummy variables.
-/

namespace H10

open Dioph

local infixr:65 " ⊗ " => Sum.elim

/-- A polynomial depends only on finitely many of its variables. -/
