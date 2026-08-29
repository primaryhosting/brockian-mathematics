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

/-!
## Characters and low-degree functions over `𝔽₃`

Boolean inputs are encoded multiplicatively: `true ↦ -1`, `false ↦ 1` (`CS.sgn`),
and also additively `true ↦ 1`, `false ↦ 0` (`CS.bit`).

For `S : Finset (Fin n)` the *character* `chi S` is the multilinear monomial
`x ↦ ∏ i ∈ S, sgn (x i)`; `V n D` is the space of functions `(Fin n → Bool) → 𝔽₃`
spanned by characters of degree at most `D`.
-/

namespace CS

/-- The field with three elements. -/
abbrev F : Type := ZMod 3

/-- Boolean inputs on `n` variables. -/
abbrev Inp (n : ℕ) : Type := Fin n → Bool

/-- Multiplicative (`±1`) encoding of a bit. -/

def bit (b : Bool) : F := if b then 1 else 0

