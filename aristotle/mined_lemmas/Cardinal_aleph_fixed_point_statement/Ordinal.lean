import Mathlib

/-!
# Aleph Fixed Point Statement
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.aleph_fixed_point_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

universe u

open Ordinal Cardinal in
/-- **Fixed point lemma for normal functions**: every normal function on the ordinals
has a fixed point, namely the next fixed point `nfp f 0` above `0`. -/

theorem Ordinal.exists_fixed_point_of_isNormal {f : Ordinal.{u} → Ordinal.{u}}
    (hf : Order.IsNormal f) : ∃ a : Ordinal.{u}, f a = a :=
  ⟨Ordinal.nfp f 0, Ordinal.nfp_fp hf 0⟩

open Ordinal Cardinal in
/-- **The aleph function has a fixed point.**  Since `Cardinal.aleph` maps ordinals to
cardinals, being a fixed point is expressed through the order isomorphism `Cardinal.ord`:
there is an ordinal `o` with `(ℵ_ o).ord = o`, equivalently `ω_ o = o`.

This follows from the fixed point lemma for normal functions applied to the normal
function `Ordinal.omega = fun o => (ℵ_ o).ord`. -/
