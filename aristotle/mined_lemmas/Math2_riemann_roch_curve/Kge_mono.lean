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
General linear algebra helpers: quotients `b / a` of nested submodules and additivity
of their dimensions along chains.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Math2

open Submodule

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The quotient `b / a` of two submodules (interesting when `a ≤ b`). -/
abbrev Qt (a b : Submodule k M) : Type _ := b ⧸ a.submoduleOf b

/-- `b / ⊥ ≃ b`. -/

lemma Kge_mono {P : Place} {m n : ℤ} (h : m ≤ n) : V.Kge P n ≤ V.Kge P m := by
  intro x hx
  simp only [mem_Kge] at *
  exact le_trans (by exact_mod_cast h) hx

end PlaceData

end Math2

/-
Divisors, degrees, Riemann-Roch spaces `L(D)`, and the local dimension computation
`dim_k (Kge P m / Kge P n) = (n - m) * deg P`.
-/
import RequestProject.RR.Basic
import RequestProject.RR.Aux

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Math2

namespace PlaceData

variable {k K Place : Type*} [Field k] [Field K] [Algebra k K] (V : PlaceData k K Place)

/-! ### Powers and elements of prescribed valuation -/

