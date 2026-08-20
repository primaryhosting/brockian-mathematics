import Mathlib

/-!
# A formal model of a privilege-isolation engine

We model an *isolation policy* on a finite set of compartments `C` as a boolean
edge relation `edge : C → C → Bool`, where `edge a b = true` means that a
principal running in compartment `a` is permitted to influence / reach
compartment `b` (a channel that is *not* isolated).

The *ground truth* semantics of privilege escape is reachability
(`PCA.Isolation.Policy.Reach`, the reflexive transitive closure of `edge`).

The *engine* is a concrete computation: iterate a one-step expansion
`Policy.step` starting from `{s}`, `Fintype.card C` times
(`Policy.escape`).  We prove:

* `Policy.escape_sound`    – the engine never over-approximates,
* `Policy.escape_complete` – the engine never under-approximates,
* `Policy.mem_escape_iff`  – hence the engine decides reachability exactly,
* `PCA.Isolation.priv_escape_monotone` – weakening the isolation (adding
  permitted edges) can only increase the set of privileges reachable from a
  compartment.
-/

namespace PCA.Isolation

open Finset

/-- An isolation policy on a set of compartments `C`: `edge a b` says that
compartment `a` may influence compartment `b`. -/
structure Policy (C : Type*) where
  /-- `edge a b = true` means the channel from `a` to `b` is *not* isolated. -/
  edge : C → C → Bool

variable {C A : Type*} [Fintype C] [DecidableEq C]

/-- Privilege escape, semantically: `Reach P s d` iff `d` is reachable from `s`
along permitted channels. -/

theorem Policy.reach_mono {P Q : Policy C} (h : ∀ a b, P.edge a b = true → Q.edge a b = true)
    {s d : C} (hr : P.Reach s d) : Q.Reach s d :=
  Relation.ReflTransGen.mono (fun a b hab => h a b hab) hr

/-- **Privilege escape is monotone in the policy**: if every channel permitted by
`P` is also permitted by `Q` (i.e. `Q` isolates no more than `P` does), then every
privilege escapable from `s` under `P` is escapable from `s` under `Q`. -/
