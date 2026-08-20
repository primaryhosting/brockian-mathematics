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

theorem conjList_mem {gs : List (Gate N)} (hp : IsLayer gs) {S : Set ℤ} {x : A}
    (hx : x ∈ N.loc S) : conjList gs x ∈ N.loc (reach gs S) := by
  induction gs with
  | nil =>
      refine N.mono ?_ hx
      exact subset_reach _ _
  | cons g gs ih =>
      obtain ⟨hg, hp'⟩ := List.pairwise_cons.mp hp
      have hz : conjList gs x ∈ N.loc (reach gs S) := ih hp'
      by_cases hd : Disjoint (edge g.bond) (reach gs S)
      · have h1 : g.u * conjList gs x = conjList gs x * g.u :=
          N.commute_of_disjoint hd g.u_mem hz
        have h2 : conjList (g :: gs) x = conjList gs x := by
          show g.u * conjList gs x * g.v = conjList gs x
          rw [h1, mul_assoc, g.uv, mul_one]
        rw [h2]
        exact N.mono (reach_mono_cons g gs S) hz
      · -- the gate's support must already meet `S`
        have hmeet : ¬ Disjoint (edge g.bond) S := by
          intro hSd
          apply hd
          rw [Set.disjoint_left]
          rintro p hpg (hpS | ⟨h, hh, _, hph⟩)
          · exact (Set.disjoint_left.mp hSd hpg) hpS
          · exact (Set.disjoint_left.mp (hg h hh) hpg) hph
        have hu : g.u ∈ N.loc (reach (g :: gs) S) :=
          N.mono (edge_subset_reach_cons hmeet) g.u_mem
        have hv : g.v ∈ N.loc (reach (g :: gs) S) :=
          N.mono (edge_subset_reach_cons hmeet) g.v_mem
        have hz' : conjList gs x ∈ N.loc (reach (g :: gs) S) :=
          N.mono (reach_mono_cons g gs S) hz
        exact N.mul_mem (N.mul_mem hu hz') hv

