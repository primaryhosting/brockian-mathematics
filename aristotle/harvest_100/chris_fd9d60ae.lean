/-
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`,
-- so the header above is written as a plain block comment.)
import Mathlib

open scoped BigOperators

namespace Math

/-- **Chinese Remainder Theorem.**

For a finite family `a : ι → ℕ` of pairwise coprime moduli, the ring `ZMod (∏ i, a i)`
is isomorphic, as a ring, to the product `∀ i, ZMod (a i)`.  Moreover the isomorphism is
the canonical one: its `i`-th component is the reduction map
`ZMod.castHom : ZMod (∏ i, a i) →+* ZMod (a i)`.

The existence of the isomorphism is `ZMod.prodEquivPi` from Mathlib; the identification of
its components with the canonical reduction maps follows from the uniqueness of ring
homomorphisms out of `ZMod n` (`RingHom.ext_zmod`). -/
theorem chinese_remainder {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hcop : Pairwise (Function.onFun Nat.Coprime a)) :
    ∃ e : ZMod (∏ i, a i) ≃+* (∀ i, ZMod (a i)),
      ∀ (x : ZMod (∏ i, a i)) (i : ι),
        e x i =
          ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i)) x := by
  refine ⟨ZMod.prodEquivPi a hcop, fun x i => ?_⟩
  have h :
      (Pi.evalRingHom (fun i => ZMod (a i)) i).comp
          (ZMod.prodEquivPi a hcop : ZMod (∏ i, a i) →+* (∀ i, ZMod (a i)))
        = ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i)) :=
    RingHom.ext_zmod _ _
  exact RingHom.congr_fun h x

end Math

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

