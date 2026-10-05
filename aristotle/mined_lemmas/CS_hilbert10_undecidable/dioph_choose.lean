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

theorem dioph_choose {α : Type} {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => (f v).choose (g v) := by
  have key : ∀ v : α → ℕ, (f v).choose (g v) =
      (((2 ^ f v + 1) + 1) ^ f v / (2 ^ f v + 1) ^ g v) % (2 ^ f v + 1) := by
    intro v
    have := choose_eq_digit (f v) (g v) (2 ^ f v + 1) (by omega)
    simpa [digit] using this
  have d2 : DiophFn fun v => (2 : ℕ) ^ f v + 1 := (pow_dioph (D.2) df) D+ (D.1)
  have : DiophFn fun v => ((2 ^ f v + 1) + 1) ^ f v / (2 ^ f v + 1) ^ g v % (2 ^ f v + 1) :=
    ((pow_dioph (d2 D+ (D.1)) df) D/ (pow_dioph d2 dg)) D% d2
  simpa [key] using this

/-- A Bernoulli-type estimate: `r ^ (n+1) ≤ (r - a) ^ (n+1) + (n+1) * a * r ^ n`. -/
