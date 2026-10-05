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

theorem isPoly_modEq {γ : Type} {p : (γ → ℕ) → ℤ} (hp : IsPoly p) {N : ℤ} {v w : γ → ℕ}
    (h : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD N]) : p v ≡ p w [ZMOD N] := by
  induction hp with
  | proj i => exact h i
  | const n => rfl
  | sub _ _ ih1 ih2 => exact ih1.sub ih2
  | mul _ _ ih1 ih2 => exact ih1.mul ih2

/-- Every Diophantine set can be defined with finitely many dummy variables. -/
