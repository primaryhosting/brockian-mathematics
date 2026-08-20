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

set_option autoImplicit false

/-!
# Parallel β-reduction has the diamond property

We formalize the untyped λ-calculus with de Bruijn indices, define parallel
one-step β-reduction `CS.Par`, and prove that it satisfies the diamond
property (Takahashi's method of complete developments).
-/

namespace CS

/-- λ-terms with de Bruijn indices. -/
inductive Term : Type
  | var : ℕ → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq

namespace Term

/-- Lifting of a renaming under a binder. -/

theorem up_ren_comp (r : ℕ → ℕ) (s : ℕ → Term) :
    up (ren r ∘ s) = ren (upr r) ∘ up s := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    have h : upr r ∘ Nat.succ = Nat.succ ∘ r := by funext m; rfl
    simp [up, Function.comp, ren_ren, h]

/-- Renaming a substituted term. -/
