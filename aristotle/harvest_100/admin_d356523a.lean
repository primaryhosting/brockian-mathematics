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

@[simp] theorem act_ne_bail (e : Effect) : Outcome.act e ≠ Outcome.bail := by
  intro h; cases h

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
noncomputable def Engine.dispatch (E : Engine Request Effect) (r : Request) :
    Outcome Effect :=
  open Classical in
  if E.recognizes r then Outcome.act (E.handle r) else Outcome.bail

@[simp] theorem Engine.dispatch_of_recognizes (E : Engine Request Effect) {r : Request}
    (h : E.recognizes r) : E.dispatch r = Outcome.act (E.handle r) := by
  unfold Engine.dispatch
  exact if_pos h

@[simp] theorem Engine.dispatch_of_not_recognizes (E : Engine Request Effect) {r : Request}
    (h : ¬ E.recognizes r) : E.dispatch r = Outcome.bail := by
  unfold Engine.dispatch
  exact if_neg h

/-- A safety policy: which outcomes are acceptable for which requests. -/
structure Policy (Request : Type u) (Effect : Type v) where
  /-- `safe r o` says outcome `o` is an acceptable response to request `r`. -/
  safe : Request → Outcome Effect → Prop
  /-- Bailing is always acceptable: refusing to act performs no effect. -/
  bail_safe : ∀ r : Request, safe r Outcome.bail

namespace Coverage

/-- **Bail-on-unrecognized is sound.**

If the engine's handler is verified on the fragment of the request language it claims to
recognize, then the bail-on-unrecognized dispatcher meets the safety policy on the *whole*
request language — including all the unrecognized requests, which are never verified.

Formally: for a policy `P` (whose `bail_safe` field records that refusing to act is always
acceptable) and an engine `E` whose handler is correct on `E.recognizes`, every request `r`
is dispatched to a `P`-safe outcome. -/
theorem bail_on_unrecognized_is_sound
    (E : Engine Request Effect) (P : Policy Request Effect)
    (hhandle : ∀ r : Request, E.recognizes r → P.safe r (Outcome.act (E.handle r))) :
    ∀ r : Request, P.safe r (E.dispatch r) := by
  intro r
  by_cases h : E.recognizes r
  · rw [E.dispatch_of_recognizes h]
    exact hhandle r h
  · rw [E.dispatch_of_not_recognizes h]
    exact P.bail_safe r

/-- **Isolation / containment.** The dispatcher performs an effect only on recognized
requests, and then only the effect prescribed by the handler.  Nothing outside the
recognized fragment can cause an effect. -/
theorem act_imp_recognizes
    (E : Engine Request Effect) {r : Request} {e : Effect}
    (h : E.dispatch r = Outcome.act e) : E.recognizes r ∧ e = E.handle r := by
  by_cases hr : E.recognizes r
  · rw [E.dispatch_of_recognizes hr] at h
    exact ⟨hr, by injection h with h; exact h.symm⟩
  · rw [E.dispatch_of_not_recognizes hr] at h
    exact absurd h.symm (Outcome.act_ne_bail e)

/-- **Completeness of the coverage condition.** The hypothesis of
`bail_on_unrecognized_is_sound` is not merely sufficient but necessary: if the dispatcher
is sound for the policy, then the handler must have been correct on the recognized
fragment.  Hence verifying the recognized fragment is exactly the required proof
obligation. -/
theorem sound_iff_handler_correct
    (E : Engine Request Effect) (P : Policy Request Effect) :
    (∀ r : Request, P.safe r (E.dispatch r)) ↔
      (∀ r : Request, E.recognizes r → P.safe r (Outcome.act (E.handle r))) := by
  constructor
  · intro hsound r hr
    have h := hsound r
    rwa [E.dispatch_of_recognizes hr] at h
  · exact bail_on_unrecognized_is_sound E P

/-- The engine that recognizes nothing is sound for *every* policy: with no recognized
requests there is no proof obligation left at all. -/
theorem bailAll_is_sound (P : Policy Request Effect) (handle : Request → Effect) :
    ∀ r : Request,
      P.safe r ((Engine.mk (fun _ : Request => False) handle).dispatch r) :=
  bail_on_unrecognized_is_sound _ P (fun _ h => h.elim)

end Coverage

end PCA

#print axioms PCA.Coverage.bail_on_unrecognized_is_sound
#print axioms PCA.Coverage.act_imp_recognizes
#print axioms PCA.Coverage.sound_iff_handler_correct
#print axioms PCA.Coverage.bailAll_is_sound

