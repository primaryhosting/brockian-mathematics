/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede every declaration, including module
docstrings, so the header above is a plain block comment.)
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Walk
import RequestProject.Savitch.Sim
import RequestProject.Savitch.Semantics
import RequestProject.Savitch.Space

/-!
The space-bounded machine model, the classes `CS.NSPACE`, `CS.DSPACE`,
`CS.PSPACE` and `CS.NPSPACE`, and the simulator used in the proof are defined in
the files `RequestProject/Savitch/*.lean`.

A machine reads its input through a head whose position is determined by its
memory value, and it works in space `g` if on inputs of length `n` all reachable
memory values lie in a set of at most `2 ^ g n` values depending only on `n`
(the standard correspondence between `s` tape cells and `2 ^ O(s)`
configurations).  The classes `NSPACE g` and `DSPACE g` are closed under
constant factors by definition, as usual for space classes.

Savitch's theorem is proved for space bounds `f` with `n + 1 ≤ 2 ^ f n`
(i.e. `f n ≥ log₂ (n+1)`), the standard hypothesis `f (n) ≥ log n`.
-/

namespace CS

/-- **Savitch's theorem**: a language recognized by a nondeterministic machine in
space `f` (with `f n ≥ log₂ (n + 1)`) is recognized by a deterministic machine in
space `O(f²)`, i.e. `NSPACE f ⊆ DSPACE (f²)`. -/

theorem PSPACE_eq_NPSPACE : PSPACE = NPSPACE := by
  apply Set.eq_of_subset_of_subset
  · rintro L ⟨k, hk⟩
    exact ⟨k, DSPACE_subset_NSPACE _ hk⟩
  · rintro L ⟨k, hk⟩
    have hmono : L ∈ NSPACE (fun n => (n + 1) ^ (k + 1)) := by
      refine NSPACE_mono (fun n => ?_) hk
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hf : ∀ n, n + 1 ≤ 2 ^ ((n + 1) ^ (k + 1)) := by
      intro n
      refine le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by omega) ?_)
      exact Nat.le_self_pow (by omega) _
    have hd := savitch (fun n => (n + 1) ^ (k + 1)) hf hmono
    refine ⟨2 * (k + 1), ?_⟩
    have hfun : (fun n => ((n + 1) ^ (k + 1)) ^ 2) = (fun n : ℕ => (n + 1) ^ (2 * (k + 1))) := by
      funext n
      rw [← pow_mul, Nat.mul_comm]
    rwa [hfun] at hd

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

/-
# The Savitch predicate computes reachability

`CY n k a b` (the value computed by the simulator) holds exactly when `b` is
reachable from `a` in at most `2 ^ k` steps of `N`, using only intermediate
configurations from the candidate list.  Combined with the elementary distance
bound this shows that the simulator accepts exactly when `N` accepts.
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Walk
import RequestProject.Savitch.Sim

namespace CS

attribute [local instance] Classical.propDecidable

noncomputable section

variable {N : Machine} {S : ℕ → Finset N.Mem} {g : ℕ → ℕ} {x : List Bool}

