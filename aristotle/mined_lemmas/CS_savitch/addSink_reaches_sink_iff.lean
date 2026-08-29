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

import RequestProject.Savitch.Machine

/-!
# Reduction to single-target reachability

`CS.addSink M` adds one new configuration (the *sink*) to `M`, with an edge from every
accepting configuration of `M` to the sink and no outgoing edge from the sink.  Then `M`
accepts iff the sink is reachable from the start configuration of `addSink M`, so that
deciding acceptance becomes deciding reachability between two *fixed* configurations.
-/

namespace CS

namespace Machine

/-- Add a sink configuration reachable exactly from the accepting configurations. -/

theorem addSink_reaches_sink_iff (M : Machine) :
    (M.addSink).Reaches (M.addSink).start (M.sink) ↔ M.Accepts := by
  constructor
  · intro h
    rcases addSink_reaches_aux M _ h with ⟨hy, -⟩ | ⟨-, hacc⟩
    · exact absurd hy (by simp [sink])
    · exact hacc
  · rintro ⟨c, hc, hacc⟩
    have hmap : ∀ z : Fin M.N, M.Reaches M.start z →
        (M.addSink).Reaches (M.addSink).start ⟨z.val, by simp only [addSink_N]; omega⟩ := by
      intro z hz
      induction hz with
      | refl => exact Relation.ReflTransGen.refl
      | @tail u v h hs ih =>
          refine ih.tail ?_
          rw [addSink_step_eq, dif_pos (show (u : ℕ) < M.N from u.isLt),
            dif_pos (show (v : ℕ) < M.N from v.isLt)]
          simpa using hs
    refine (hmap c hc).tail ?_
    rw [addSink_step_eq, dif_pos (show (c : ℕ) < M.N from c.isLt), dif_neg (by simp [sink])]
    simpa using hacc

end Machine

end CS

import Mathlib

/-!
# Configuration-graph machines and space classes

This file sets up the model of computation used for Savitch's theorem.

A `Machine` is the *configuration graph* of a space-bounded machine on a fixed input:
a finite set of configurations `Fin N`, a transition relation `step`, an initial
configuration `start`, and a set of accepting configurations `accept`.  The machine
accepts if some accepting configuration is reachable from `start`.  It is
*deterministic* when `step` is functional.

The space used is `log₂ N`: a machine running in space `s` (with `s ≥ log₂` of the
input length) has `2^{O(s)}` configurations, and conversely a configuration can be
stored in `log₂ N` bits.  Accordingly a language is in `DSPACE f` (resp. `NSPACE f`)
if it is decided by a family of (deterministic) configuration graphs with at most
`2 ^ f n` configurations on inputs of length `n`.
-/

namespace CS

/-- The configuration graph of a machine on a fixed input:
`N` configurations, a transition relation, a start configuration and accepting
configurations. -/
structure Machine where
  /-- Number of configurations. -/
  N : ℕ
  /-- The transition relation between configurations. -/
  step : Fin N → Fin N → Bool
  /-- The initial configuration. -/
  start : Fin N
  /-- The accepting configurations. -/
  accept : Fin N → Bool

namespace Machine

/-- Reachability in the configuration graph. -/
