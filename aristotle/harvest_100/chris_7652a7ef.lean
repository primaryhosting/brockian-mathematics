/-
# Aleph Fixed Point Statement
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.aleph_fixed_point_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Lean requires `import` to precede any module docstring, so the required header is
reproduced verbatim as a module docstring immediately after the import below.)
-/

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

/-- **Fixed point lemma for normal functions, and the aleph fixed point.**

The first conjunct states that every normal function `f : Ordinal → Ordinal` has a fixed
point (obtained as the next fixed point `Ordinal.nfp f 0` above `0`).

The second conjunct is the aleph fixed point: there is an ordinal `o` with
`(Cardinal.aleph o).ord = o`, i.e. `o` is the `o`-th infinite initial ordinal.  This is obtained
by applying the fixed point lemma to the normal function `Ordinal.omega = fun o => (ℵ_ o).ord`. -/
theorem Cardinal.aleph_fixed_point_statement :
    (∀ f : Ordinal → Ordinal, Order.IsNormal f → ∃ a : Ordinal, f a = a) ∧
      ∃ o : Ordinal, (Cardinal.aleph o).ord = o := by
  constructor
  · -- The fixed point lemma: `Ordinal.nfp f 0` is a fixed point of any normal `f`.
    intro f hf
    exact ⟨Ordinal.nfp f 0, Ordinal.nfp_fp hf 0⟩
  · -- Apply it to `Ordinal.omega`, which is normal and satisfies `ω_ o = (ℵ_ o).ord`.
    refine ⟨Ordinal.nfp Ordinal.omega 0, ?_⟩
    rw [Cardinal.ord_aleph]
    exact Ordinal.nfp_fp Ordinal.isNormal_omega 0

#print axioms Cardinal.aleph_fixed_point_statement

