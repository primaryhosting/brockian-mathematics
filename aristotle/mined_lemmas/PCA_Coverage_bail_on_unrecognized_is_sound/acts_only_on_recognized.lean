/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/- This development is self-contained: it needs nothing beyond Lean core, so the
file has no `import` line (a module doc comment must precede any import). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Coverage

universe u v

/-- The result the isolation engine may return: either it performs an action it
recognized as safe, or it *bails out* (refuses to act). -/
inductive Outcome (Action : Type v) : Type v
  | act : Action → Outcome Action
  | bail : Outcome Action
  deriving DecidableEq

/-- A model of the isolation engine.

* `recognize` is the (partial) recognizer: it returns the action to perform on
  inputs it understands, and `none` on inputs outside its coverage.
* `safe i a` is the specification: performing `a` on input `i` is safe.
* `recognized_is_safe` is the *proof carried by the app*: whenever the engine
  claims to recognize an input, the action it proposes meets the specification.

Note that nothing is assumed about the behaviour of `safe` on unrecognized
inputs; coverage of the recognizer is deliberately left partial. -/
structure Engine (Input : Type u) (Action : Type v) where
  recognize : Input → Option Action
  safe : Input → Action → Prop
  recognized_is_safe : ∀ i a, recognize i = some a → safe i a

variable {Input : Type u} {Action : Type v}

/-- The engine's dispatch loop: act on recognized inputs, bail on everything else. -/

theorem acts_only_on_recognized (E : Engine Input Action) (i : Input)
    (h : E.run i ≠ Outcome.bail) : ∃ a : Action, E.recognize i = some a := by
  cases hr : E.recognize i with
  | none => exact absurd ((E.run_eq_bail_iff i).2 hr) h
  | some a => exact ⟨a, rfl⟩

end PCA.Coverage

