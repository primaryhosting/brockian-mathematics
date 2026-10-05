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
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS
namespace IS

/-!
## The reachability sets of a finite digraph

Throughout, the digraph has vertex set `{0, 1, ..., N-1} ⊆ ℕ` and edge relation `adj`.
`R N adj s i` is the set of vertices reachable from `s` using at most `i` edges.
-/

/-- The edge relation of the digraph on vertex set `{0,...,N-1}`. -/

theorem reachable_transport (step : C → C → Bool) (a b : C) :
    Relation.ReflTransGen (fun x y => step x y = true) a b ↔
      Relation.ReflTransGen (Edge (Fintype.card C) (adjOf step)) (enc C a : ℕ) (enc C b : ℕ) := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih =>
        refine ih.tail ⟨(enc C y).isLt, (enc C z).isLt, ?_⟩
        rw [adjOf_apply]
        exact hyz
  · intro h
    have key : ∀ z : ℕ, Relation.ReflTransGen (Edge (Fintype.card C) (adjOf step)) (enc C a : ℕ) z →
        ∃ y : C, z = (enc C y : ℕ) ∧ Relation.ReflTransGen (fun x y => step x y = true) a y := by
      intro z hz
      induction hz with
      | refl => exact ⟨a, rfl, .refl⟩
      | @tail p q _ hpq ih =>
          obtain ⟨y, rfl, hay⟩ := ih
          obtain ⟨-, hqlt, hadj⟩ := hpq
          refine ⟨(enc C).symm ⟨q, hqlt⟩, by simp, hay.tail ?_⟩
          rw [← adjOf_apply step y ((enc C).symm ⟨q, hqlt⟩)]
          simpa using hadj
    obtain ⟨y, hy, hay⟩ := key _ h
    have : b = y := (enc C).injective (Fin.val_injective hy)
    rwa [this]

/-- **Immerman–Szelepcsényi: `NL = coNL`.**

Let `step` be the one-step relation of a nondeterministic machine with (finitely many)
configurations `C`, let `a` be its initial and `b` its accepting configuration, so that the
machine *rejects* exactly when `b` is not reachable from `a`.

Then rejection is itself an acceptance condition of the same shape, for the explicitly
constructed machine `IS.Step`: `b` is unreachable from `a` if and only if the configuration
`IS.Cfg.acc` is reachable from `IS.start` in the configuration graph of `IS.Step`.

The new machine is built uniformly from `step` and (see
`CS.immerman_szelepcsenyi_space`) has at most `5 * (Fintype.card C + 2) ^ 8` reachable
configurations; so if the original machine runs in space `S ≥ log n`, the new one runs in
space `O(S)`.  With `S = log n` this is `NL = coNL`. -/
