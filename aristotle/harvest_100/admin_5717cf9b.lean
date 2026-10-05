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
theorem dvd_prod_of_family {ι : Type*} [Fintype ι] (n : ι → ℕ) (i : ι) :
    n i ∣ ∏ j, n j :=
  Finset.dvd_prod_of_mem n (Finset.mem_univ i)

/-- Any ring homomorphism out of `ZMod N` into `ZMod m`, where `m ∣ N`, is the canonical
reduction map. (`ZMod N` is a quotient of the initial ring `ℤ`, so such a map is unique.) -/
theorem ringHom_to_zmod_eq_castHom {N m : ℕ} (h : m ∣ N) (f : ZMod N →+* ZMod m) :
    f = ZMod.castHom h (ZMod m) :=
  RingHom.ext_zmod f (ZMod.castHom h (ZMod m))

/-- **Chinese Remainder Theorem.**  For a finite family `n : ι → ℕ` of pairwise coprime moduli,
the ring `ZMod (∏ i, n i)` is isomorphic to the product ring `Π i, ZMod (n i)`; moreover the
isomorphism is the canonical one, given componentwise by reduction mod `n i`. -/
theorem chinese_remainder {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on n)) :
    ∃ e : ZMod (∏ i, n i) ≃+* (Π i, ZMod (n i)),
      ∀ (x : ZMod (∏ i, n i)) (i : ι),
        e x i = ZMod.castHom (dvd_prod_of_family n i) (ZMod (n i)) x := by
  refine ⟨ZMod.prodEquivPi n hcop, fun x i => ?_⟩
  have h := ringHom_to_zmod_eq_castHom (dvd_prod_of_family n i)
    ((Pi.evalRingHom (fun i => ZMod (n i)) i).comp
      (ZMod.prodEquivPi n hcop : ZMod (∏ i, n i) →+* Π i, ZMod (n i)))
  exact congrArg (fun g : ZMod (∏ i, n i) →+* ZMod (n i) => g x) h

/-- The canonical reduction homomorphism `ZMod (∏ i, n i) →+* Π i, ZMod (n i)` is bijective
for pairwise coprime moduli. -/
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

