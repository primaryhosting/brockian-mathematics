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
import RequestProject.RS.Degree

/-!
# Probabilistic polynomial approximation of `AC⁰[q]` circuits

The Razborov–Smolensky approximation lemma: a circuit of size `s` and depth `d` over
`{¬, ∧, ∨, MOD q}` can be approximated over a field of characteristic `q` by a function of
degree `(ℓ (q-1))^d` which errs on at most `s · 2^(n-ℓ)` inputs.
-/

set_option maxHeartbeats 1000000

namespace CS

open Finset

variable {F : Type*} [Field F] {n q : ℕ}

/-- The set of inputs on which `g` differs from the Boolean function `h`. -/

def cnt {k : ℕ} (b : Fin k → Bool) : ℕ := #{i | b i = true}

/-- The unbounded fan-in gate types: `AND`, `OR` and `MOD q`. -/
inductive GateType
  | and
  | or
  | mod
  deriving DecidableEq

/-- Boolean circuits with `n` inputs over the basis `{¬, ∧, ∨, MOD q}`,
with unbounded fan-in `∧`, `∨` and `MOD q` gates. -/
inductive Circuit (n : ℕ) : Type
  | var : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | gate : GateType → (k : ℕ) → (Fin k → Circuit n) → Circuit n

namespace Circuit

variable {n m : ℕ}

/-- The number of gates of a circuit (negations included). -/
