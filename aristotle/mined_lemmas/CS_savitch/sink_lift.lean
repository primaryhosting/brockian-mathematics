import RequestProject.Savitch.Machine

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

We model a space-`s` machine by its configuration graph: it has at most `2 ^ s`
configurations (`s` bits of workspace), a start configuration, an acceptance
predicate, and a transition relation (a relation for nondeterministic machines, a
function for deterministic ones).  A nondeterministic machine accepts when some
accepting configuration is reachable from the start configuration; a deterministic
machine accepts when its (unique) run visits an accepting configuration.

The main theorem `CS.savitch` states `NSPACE f ⊆ DSPACE (9 * (f + 1) ^ 2)`, i.e.
nondeterministic space `f` is contained in deterministic space `O(f ^ 2)`, and
`CS.PSPACE_eq_NPSPACE` deduces `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

/-- A nondeterministic machine using space `s`: at most `2 ^ s` configurations. -/
structure NMachine (s : ℕ) where
  /-- Number of configurations. -/
  size : ℕ
  /-- The space bound: `s` bits of workspace. -/
  hsize : size ≤ 2 ^ s
  /-- The (nondeterministic) transition relation. -/
  step : Fin size → Fin size → Bool
  /-- The initial configuration. -/
  start : Fin size
  /-- The accepting configurations. -/
  acc : Fin size → Bool

/-- A nondeterministic machine accepts if some accepting configuration is reachable. -/

theorem sink_lift {c : Fin M.size}
    (h : Relation.ReflTransGen (fun x y => M.step x y = true) M.start c) :
    Relation.ReflTransGen (fun x y => sinkRel M x y = true)
      (Fin.castSucc M.start) (Fin.castSucc c) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z _ hyz ih =>
    refine ih.tail ?_
    rw [sinkRel, dif_pos (by simp : ((Fin.castSucc y : Fin (M.size + 1)) : ℕ) < M.size),
      dif_pos (by simp : ((Fin.castSucc z : Fin (M.size + 1)) : ℕ) < M.size)]
    simpa using hyz

