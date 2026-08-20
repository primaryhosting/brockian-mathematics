import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS


theorem reflTransGen_equiv {α β : Type} (e : α ≃ β) (R : α → α → Prop) (a b : α) :
    Relation.ReflTransGen R a b ↔
      Relation.ReflTransGen (fun u v => R (e.symm u) (e.symm v)) (e a) (e b) := by
  constructor
  · intro h
    exact h.lift (f := fun a => e a) (fun u v huv => by simpa using huv)
  · intro h
    have := h.lift (f := fun u => e.symm u) (fun u v huv => huv)
    simpa using this

end CS

import RequestProject.ISModel

/-!
# A sanity check on the model

The class `NL` defined in `RequestProject/ISModel.lean` is not degenerate: it contains
languages that genuinely depend on the input.  Here we check that the language "the first
input bit is `true`" is in `NL`.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS

/-- A two-configuration machine testing the first input bit. -/
