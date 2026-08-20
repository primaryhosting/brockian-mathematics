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

theorem Par.triangle {t u : Term} (h : Par t u) : Par u (star t) := by
  induction h with
  | var n => exact Par.var n
  | @app t t' u u' ht hu iht ihu =>
    cases t with
    | var n =>
      cases ht
      simpa using (Par.var n).app ihu
    | app t₁ t₂ => simpa using iht.app ihu
    | lam t₀ =>
      cases ht with
      | lam ht₀ =>
        rename_i t₀'
        rw [star_app_lam]
        cases iht with
        | lam ih => exact Par.beta ih ihu
  | lam _ ih => exact ih.lam
  | beta _ _ iht ihu =>
    rw [star_app_lam]
    exact iht.inst ihu

/-- **Diamond property of parallel β-reduction.** If `t` parallel-reduces in one
step to both `u` and `v`, then `u` and `v` have a common parallel reduct. -/
