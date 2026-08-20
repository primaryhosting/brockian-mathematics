/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

namespace Frontier

/-- The support of a nearest-neighbour bond gate sitting on the bond `i` of the
spin chain `ℤ`: the two sites `i` and `i + 1`. -/

def twoSiteNet : LocalNet SpinPairMat where
  loc := locPair
  one_mem := fun _ => ⟨1, 1, by simp, fun _ => rfl, fun _ => rfl⟩
  mul_mem := by
    rintro S x y ⟨a, b, rfl, ha, hb⟩ ⟨c, d, rfl, hc, hd⟩
    exact ⟨a * c, b * d, (Matrix.mul_kronecker_mul a c b d).symm,
      fun h => by rw [ha h, hc h, mul_one], fun h => by rw [hb h, hd h, mul_one]⟩
  mono := by
    rintro S T hST x ⟨a, b, rfl, ha, hb⟩
    exact ⟨a, b, rfl, fun h => ha fun h' => h (hST h'), fun h => hb fun h' => h (hST h')⟩
  commute_of_disjoint := by
    rintro S T x y h ⟨a, b, rfl, ha, hb⟩ ⟨c, d, rfl, hc, hd⟩
    have h0 : a * c = c * a := by
      by_cases h0 : (0 : ℤ) ∈ S
      · rw [hc fun hT => (Set.disjoint_left.mp h h0) hT]; simp
      · rw [ha h0]; simp
    have h1 : b * d = d * b := by
      by_cases h1 : (1 : ℤ) ∈ S
      · rw [hd fun hT => (Set.disjoint_left.mp h h1) hT]; simp
      · rw [hb h1]; simp
    rw [← Matrix.mul_kronecker_mul a c b d, ← Matrix.mul_kronecker_mul c a d b, h0, h1]

/-- The two-site net really is noncommutative: observables on the *same* site need
not commute, so the vanishing of commutators in `Frontier.lieb_robinson` is not
automatic. -/
