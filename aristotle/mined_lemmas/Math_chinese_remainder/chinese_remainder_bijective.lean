/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Function -- for the scoped `on` notation

namespace Math

/-- Each modulus of a finite family divides the product of the family. -/

theorem chinese_remainder_bijective {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on n)) :
    Function.Bijective
      (fun (x : ZMod (∏ i, n i)) (i : ι) =>
        ZMod.castHom (dvd_prod_of_family n i) (ZMod (n i)) x) := by
  obtain ⟨e, he⟩ := chinese_remainder n hcop
  have : (fun (x : ZMod (∏ i, n i)) (i : ι) =>
      ZMod.castHom (dvd_prod_of_family n i) (ZMod (n i)) x) = e := by
    funext x i
    exact (he x i).symm
  rw [this]
  exact e.bijective

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

