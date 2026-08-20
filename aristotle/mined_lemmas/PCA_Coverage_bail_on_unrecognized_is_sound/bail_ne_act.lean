import Mathlib
import RequestProject.Main

/-!
Mathlib-side sanity check: the development in `RequestProject.Main` elaborates and is
axiom-clean inside a full Mathlib environment, and instantiates to concrete engines.
-/

set_option autoImplicit false

#print axioms PCA.Coverage.bail_on_unrecognized_is_sound

namespace PCA.Coverage

/-- A concrete instance: an engine over `ℕ`-tagged requests that only recognizes even
tags, together with the policy "never act on an odd tag". -/
example :
    ∀ r : ℕ,
      (Policy.mk (fun (r : ℕ) (o : Outcome ℕ) => o = Outcome.bail ∨ Even r)
        (fun _ => Or.inl rfl)).safe r
        ((Engine.mk (fun r : ℕ => Even r) (fun r => r + 1)).dispatch r) :=
  bail_on_unrecognized_is_sound _ _ (fun _ hr => Or.inr hr)

end PCA.Coverage

/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 requires `import` commands to be the very first thing in a file,
before any module documentation.  Since the required header above is a module doc comment,
this file carries no `import` line.  None is needed: the development below is stated and
proved entirely in core Lean 4 / `Init`, so it is fully compatible with (and usable from) a
Mathlib project — see `RequestProject/MathlibCheck.lean`, which imports Mathlib together
with this file and re-checks the target theorem's axioms.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## The model

An *isolation engine* receives requests from an untrusted environment.  It carries a
`recognizes` predicate describing the fragment of the request language that it actually
understands, and a `handle` function producing the effect it would perform on such a
request.  The engine's dispatch loop is *bail-on-unrecognized*: any request outside the
recognized fragment produces the inert outcome `Outcome.bail`, performing no effect at all.

The soundness statement is that such a dispatcher satisfies an arbitrary safety policy
`safe` as soon as

* the policy accepts bailing (bailing is always allowed — it performs nothing), and
* the handler is correct *on the recognized fragment only*.

In other words, verification effort only has to cover the recognized fragment: coverage of
the (unbounded, untrusted) rest of the request language is discharged by bailing.
-/

namespace PCA

universe u v

/-- The outcome of dispatching a single request: either the engine bails, performing no
effect at all, or it performs a concrete effect. -/
inductive Outcome (Effect : Type u) where
  /-- The request was not recognized; the engine refuses to act. -/
  | bail : Outcome Effect
  /-- The request was recognized and the engine performs the given effect. -/
  | act : Effect → Outcome Effect
  deriving DecidableEq

namespace Outcome

variable {Effect : Type u}


@[simp] theorem bail_ne_act (e : Effect) : Outcome.bail ≠ Outcome.act e := by
  intro h; cases h

end Outcome

/-- An isolation engine over a request language `Request` with effects in `Effect`. -/
structure Engine (Request : Type u) (Effect : Type v) where
  /-- The fragment of the request language the engine claims to understand. -/
  recognizes : Request → Prop
  /-- The effect the engine would perform on a request.  Its behaviour on unrecognized
  requests is irrelevant: the dispatcher never calls it there. -/
  handle : Request → Effect

variable {Request : Type u} {Effect : Type v}

/-- The bail-on-unrecognized dispatch loop. -/
