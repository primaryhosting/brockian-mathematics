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

theorem Beta.toPar {t u : Term} (h : Beta t u) : Par t u := by
  induction h with
  | beta t u => exact Par.beta (Par.refl t) (Par.refl u)
  | appLeft u _ ih => exact ih.app (Par.refl u)
  | appRight t _ ih => exact (Par.refl t).app ih
  | lam _ ih => exact ih.lam

/-- Parallel reduction is stable under renaming. -/
