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

theorem dioph_factorial {α : Type} {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    DiophFn fun v => (f v)! := by
  have key : ∀ v : α → ℕ, (f v)! =
      (2 * (f v + 1) ^ (f v + 3)) ^ (f v) / (2 * (f v + 1) ^ (f v + 3)).choose (f v) :=
    fun v => factorial_eq_div _ _ (factorial_bound (f v))
  have dr : DiophFn fun v => 2 * (f v + 1) ^ (f v + 3) :=
    (D.2) D* (pow_dioph (df D+ (D.1)) (df D+ (D.3)))
  have : DiophFn fun v =>
      (2 * (f v + 1) ^ (f v + 3)) ^ (f v) / (2 * (f v + 1) ^ (f v + 3)).choose (f v) :=
    (pow_dioph dr df) D/ (dioph_choose dr df)
  simpa [key] using this

end H10

import Mathlib
import RequestProject.H10.Bounded

/-!
# Diophantine sets are closed under bounded universal quantification

This is the Davis–Putnam–Robinson theorem, the last missing ingredient (besides Matiyasevic's
theorem `Dioph.pow_dioph`, already in Mathlib) for the negative solution of Hilbert's tenth
problem.
-/

namespace H10

open Nat Dioph Vector3 Sum Fin2

local infixr:65 " ⊗ " => Sum.elim

