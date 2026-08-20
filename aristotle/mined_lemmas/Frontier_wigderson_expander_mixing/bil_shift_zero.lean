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

namespace Frontier

section Mixing

variable {V : Type*} [Fintype V]

/-- The bilinear form associated with a weight matrix `A : V → V → ℝ`. -/

lemma bil_shift_zero (A : V → V → ℝ) (d : ℝ) (hsymm : ∀ u v, A u v = A v u)
    (hreg : ∀ u, ∑ v, A u v = d) (p q : V → ℝ) (hp : ∑ v, p v = 0) (hq : ∑ v, q v = 0)
    (al be : ℝ) :
    bil A (fun x => p x + al) (fun x => q x + be)
      = bil A p q + al * be * d * (Fintype.card V : ℝ) := by
  have hone : ∀ (r : V → ℝ) (c : ℝ), (fun x => r x + c) = (fun x => r x + c * (1 : ℝ)) := by
    intro r c; funext x; ring
  rw [hone p al, hone q be]
  rw [bil_add_left, bil_add_right, bil_add_right]
  have h1 : bil A p (fun x => be * (1 : ℝ)) = 0 := by
    rw [show (fun x : V => be * (1 : ℝ)) = (fun x : V => be * (fun _ : V => (1:ℝ)) x) from rfl,
      bil_smul_right, bil_one_right A d hreg, hp]
    ring
  have hq1 : bil A (fun x : V => al * (1 : ℝ)) q = 0 := by
    rw [show (fun x : V => al * (1 : ℝ)) = (fun x : V => al * (fun _ : V => (1:ℝ)) x) from rfl,
      bil_smul_left, bil_symm A hsymm, bil_one_right A d hreg, hq]
    ring
  have h11 : bil A (fun x : V => al * (1 : ℝ)) (fun x : V => be * (1 : ℝ))
      = al * be * d * (Fintype.card V : ℝ) := by
    rw [show (fun x : V => al * (1 : ℝ)) = (fun x : V => al * (fun _ : V => (1:ℝ)) x) from rfl,
      show (fun x : V => be * (1 : ℝ)) = (fun x : V => be * (fun _ : V => (1:ℝ)) x) from rfl,
      bil_smul_left, bil_smul_right, bil_one_right A d hreg]
    simp [Finset.card_univ]
    ring
  rw [h1, hq1, h11]
  ring

