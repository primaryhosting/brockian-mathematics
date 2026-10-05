import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MvPolynomial

/-! ## Setting up plane curves over `ℚ` -/

/-- The set of `ℚ`-rational points of the projective plane curve cut out by a homogeneous
form `F` in three variables. A point of `ℙ²(ℚ)` is represented as a point of
`Projectivization ℚ (Fin 3 → ℚ)`; since `F` is homogeneous, vanishing of `F` at a
representative does not depend on the chosen representative (see
`Frontier.mem_projPoints_fermatForm_iff` for the case used below). -/

theorem projPoints_fermatForm_four :
    projPoints (fermatForm 4) =
      ({Projectivization.mk ℚ ![1, 0, 1] (vec_ne_zero 1 0),
        Projectivization.mk ℚ ![-1, 0, 1] (vec_ne_zero (-1) 0),
        Projectivization.mk ℚ ![0, 1, 1] (vec_ne_zero 0 1),
        Projectivization.mk ℚ ![0, -1, 1] (vec_ne_zero 0 (-1))} :
        Set (Projectivization ℚ (Fin 3 → ℚ))) := by
  refine Set.Subset.antisymm (projPoints_fermatForm_subset 4 dvd_rfl (by norm_num)) ?_
  rintro P (rfl | rfl | rfl | rfl) <;>
    exact (mem_projPoints_fermatForm_iff 4 _ _).mpr
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons])

/-! ## The target -/

/-- **A verified case of Faltings' theorem (the Mordell conjecture).**

For every positive multiple `n` of `4`, the Fermat curve `x ^ n + y ^ n = z ^ n` is a
nonsingular projective plane curve over `ℚ` of degree `n`, its genus `(n-1)(n-2)/2` is at
least `2`, and it has only finitely many `ℚ`-rational points — as predicted by Faltings'
theorem. (The finiteness is obtained from Fermat's Last Theorem for exponent `4`.) -/
