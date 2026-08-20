/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Statement: Matrix elements of tensor operators factor into a Clebsch–Gordan × reduced element (Wigner–Eckart).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

open TensorProduct

variable {G : Type*} [Monoid G]

/-- `f` intertwines the representations `ρ` and `σ`. -/

noncomputable def sanityEquiv : (ℂ ⊗[ℂ] ℂ) ≃ₗ[ℂ] ℂ × PUnit.{1} :=
  (TensorProduct.lid ℂ ℂ).trans
    { toFun := fun x => (x, PUnit.unit)
      map_add' := by intro a b; apply Prod.ext <;> simp
      map_smul' := by intro c a; apply Prod.ext <;> simp
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := fun _ => by apply Prod.ext <;> simp }

/-- Non-vacuity check: the hypotheses of `Phys.wigner_eckart` are satisfiable, here in the
simplest instance (trivial group, one-dimensional final space, `T = 3 • C`). -/
example : ∃! r : ℂ, ∀ (bra : Module.Dual ℂ ℂ) (q m : ℂ),
    bra (((3 : ℂ) • LinearMap.mul ℂ ℂ) q m) = r * bra ((LinearMap.mul ℂ ℂ) q m) := by
  refine Phys.wigner_eckart (G := Unit) (Vk := ℂ) (Vj := ℂ) (Vf := ℂ) (K := PUnit.{1})
    1 1 1 1 ⟨inferInstance, fun S _ => Ideal.eq_bot_or_top S⟩ sanityEquiv ?_ ?_
    (LinearMap.mul ℂ ℂ) ((3 : ℂ) • LinearMap.mul ℂ ℂ) ?_ ?_ ?_
  · intro g v
    simp
  · intro f _
    exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero]; rfl
  · intro g q m
    simp
  · intro g q m
    simp
  · intro h
    have : (LinearMap.mul ℂ ℂ) 1 1 = 0 := by rw [h]; rfl
    simp at this

end Sanity
#print axioms Phys.wigner_eckart
#print axioms Phys.wigner_eckart_abstract
#print axioms Phys.schur_scalar

