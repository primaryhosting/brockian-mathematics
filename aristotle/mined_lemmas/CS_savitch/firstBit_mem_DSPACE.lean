/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Savitch.Model
import RequestProject.Savitch.Stack

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

`NSPACE f ⊆ DSPACE (f²)`.

Given a nondeterministic machine with at most `2 ^ (c * f n + c)` configurations we build a
deterministic machine which decides, by Savitch's midpoint recursion, whether an accepting
configuration is reachable in the configuration graph.  The deterministic machine stores an
explicit recursion stack of depth `c * f n + c + 2`, each frame holding a constant number of
configurations and indices, hence it has `2 ^ O(f n ^ 2)` configurations.

As a corollary, `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

section Construction

variable (M : NMachine)

/-- The vertices of the configuration graph: the configurations of `M`, together with an extra
sink `none` which is reachable exactly from the accepting configurations.  Thus `M` accepts iff
the sink is reachable from the initial configuration. -/
abbrev Vtx (M : NMachine) (n : ℕ) : Type := Option (M.Conf n)

instance vtxFinite (n : ℕ) : Finite (Vtx M n) := by
  haveI := M.finite n; infer_instance

noncomputable instance vtxFintype (n : ℕ) : Fintype (Vtx M n) := Fintype.ofFinite _

noncomputable instance vtxDecEq (n : ℕ) : DecidableEq (Vtx M n) := Classical.decEq _

/-- An enumeration of the vertices of the configuration graph. -/

theorem firstBit_mem_dspace :
    (fun x : List Bool => readBit x 0 = true) ∈ DSPACE (fun _ => 0) := by
  refine ⟨firstBitMachine, 2, fun n => ?_, fun x => ?_⟩
  · simp [firstBitMachine, Nat.card_eq_fintype_card]
  · have hstep : ∀ q : Option Bool, firstBitMachine.stepFun x q = some (q.getD (readBit x 0)) :=
      fun _ => rfl
    constructor
    · intro hx
      refine ⟨1, ?_⟩
      rw [Function.iterate_one]
      simp [DMachine.stepFun, firstBitMachine, hx]
    · rintro ⟨t, ht⟩
      by_contra hx
      have hx' : readBit x 0 = false := by
        cases h : readBit x 0 with
        | false => rfl
        | true => exact absurd h hx
      have key : ∀ t : ℕ,
          ((firstBitMachine.stepFun x)^[t] (firstBitMachine.start x.length) : Option Bool) = none ∨
          ((firstBitMachine.stepFun x)^[t] (firstBitMachine.start x.length) : Option Bool) =
            some false := by
        intro t
        induction t with
        | zero => exact Or.inl rfl
        | succ t ih =>
          rw [Function.iterate_succ_apply', hstep]
          rcases ih with h | h <;> rw [h] <;> simp [hx']
      rcases key t with h | h <;> rw [h] at ht <;> simp [firstBitMachine] at ht

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

import Mathlib

/-!
# Walks in a finite digraph and the Savitch recursion

`PathTo adj m u v` says that there is a walk with exactly `m` edges from `u` to `v`.
`Reach adj k u v` is the predicate computed by Savitch's midpoint recursion; we show it is
equivalent to the existence of a walk of length at most `2 ^ k`, and that in a finite digraph
reachability is witnessed by a walk shorter than the number of vertices.
-/

namespace CS
namespace Savitch

variable {X : Type}

/-- There is a walk with exactly `m` edges from `u` to `v`. -/
