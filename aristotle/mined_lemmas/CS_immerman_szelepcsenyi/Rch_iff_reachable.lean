import RequestProject.Counting

/-!
# Soundness of the counting machine

We define an invariant of the states of the counting machine which is satisfied by the
initial state and preserved by every transition, and which guarantees, in the accepting
phase, that no accepting vertex is reachable.
-/

open scoped Classical

namespace CS
namespace IS

open Data

variable (G : Data) (x : List Bool)

/-- The invariant of the inner loop: the vertices counted so far form a set `S` of vertices
`< u` reachable in `i` steps, and the flag correctly records whether one of them witnesses
the reachability of `v` in `i+1` steps. -/

lemma Rch_iff_reachable (v : ℕ) : G.Rch x G.N v ↔ G.Reachable x v := by
  constructor
  · intro h
    have key : ∀ i v, G.Rch x i v → G.Reachable x v := by
      intro i
      induction i with
      | zero => intro v hv; rw [Rch_zero] at hv; subst hv; exact Relation.ReflTransGen.refl
      | succ i ih =>
          intro v hv
          rcases hv with hv | ⟨u, hu, he⟩
          · exact ih v hv
          · exact (ih u hu).tail he
    exact key G.N v h
  · intro h
    obtain ⟨i, hi, hstab⟩ := exists_stab (G := G) (x := x)
    have key : ∀ w, G.Reachable x w → ∃ j, G.Rch x j w := by
      intro w hw
      induction hw with
      | refl => exact ⟨0, Rch_start⟩
      | tail _ he ih =>
          obtain ⟨j, hj⟩ := ih
          exact ⟨j + 1, Rch_step hj he⟩
    obtain ⟨j, hj⟩ := key v h
    rcases Nat.lt_or_ge j G.N with hjN | hjN
    · exact Rch_mono (by omega) hj
    · exact Rch_mono (by omega) (Rch_stab i hstab j v (by omega) hj)

end Data

end IS
end CS

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

