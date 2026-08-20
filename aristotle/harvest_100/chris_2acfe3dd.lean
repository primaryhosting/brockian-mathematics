import Mathlib

/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
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

namespace Math

/-- The canonical ring homomorphism `ZMod (∏ i, n i) →+* Π i, ZMod (n i)`,
whose `i`-th component is reduction modulo `n i`. -/
def crtHom {ι : Type*} [Fintype ι] (n : ι → ℕ) :
    ZMod (∏ i, n i) →+* Π i, ZMod (n i) :=
  Pi.ringHom fun i =>
    ZMod.castHom (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) (ZMod (n i))

/-- **Chinese Remainder Theorem.** For pairwise coprime moduli `n i`, the canonical
reduction map `ZMod (∏ i, n i) → Π i, ZMod (n i)` is a bijection; in particular
`ZMod (∏ i, n i) ≃+* Π i, ZMod (n i)` as rings. -/
theorem chinese_remainder {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (h : Pairwise (Function.onFun Nat.Coprime n)) :
    Function.Bijective (crtHom n) ∧
      Nonempty (ZMod (∏ i, n i) ≃+* Π i, ZMod (n i)) := by
  classical
  have e : ZMod (∏ i, n i) ≃+* Π i, ZMod (n i) := ZMod.prodEquivPi n h
  have hcoe : (e : ZMod (∏ i, n i) →+* Π i, ZMod (n i)) = crtHom n :=
    RingHom.ext_zmod _ _
  refine ⟨?_, ⟨e⟩⟩
  have hfun : (crtHom n : ZMod (∏ i, n i) → Π i, ZMod (n i)) = e := by
    rw [← hcoe]; rfl
  rw [hfun]
  exact e.bijective

end Math

