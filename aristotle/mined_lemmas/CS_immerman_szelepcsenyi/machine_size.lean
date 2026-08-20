import RequestProject.Counting

/-!
# Soundness of the counting machine

We define an invariant of the states of the counting machine which is satisfied by the
initial state and preserved by every transition, and which guarantees, in the accepting
phase, that no accepting vertex is reachable.
-/

open scoped Classical

namespace CS
namespace IS

open Data

variable (G : Data) (x : List Bool)

/-- The invariant of the inner loop: the vertices counted so far form a set `S` of vertices
`< u` reachable in `i` steps, and the flag correctly records whether one of them witnesses
the reachability of `v` in `i+1` steps. -/

@[simp] lemma machine_size : (machine G).size = Fintype.card (Aux G.N) := rfl

end Machine

end IS
end CS

import Mathlib

/-!
# The machine model : polynomial size nondeterministic branching programs

This file sets up the computational model used to state `NL = coNL`.

A *nondeterministic branching program* (`CS.NBP`) has a finite set of states.  Each state
carries a position `read` of the input tape; a transition out of a state may depend on the
input only through the symbol found at that position (`none` if the position is beyond the
end of the input).  A word is accepted if some accepting state is reachable from the start
state.

The class `CS.NL` consists of the languages `L ⊆ List Bool` for which there is a family of
such programs, one for each input length, of size polynomial in the input length, accepting
exactly the words of `L`.  This is the standard (non-uniform) characterisation of
nondeterministic logarithmic space: a nondeterministic machine using space `s(n)` has
`2^{O(s(n))}` configurations, and the configuration graph is exactly a nondeterministic
branching program of that size.
-/

open scoped Classical

namespace CS

/-- A nondeterministic branching program: a finite state set, a position of the input tape
read at each state, a nondeterministic transition relation depending on the symbol read,
a start state and a set of accepting states. -/
structure NBP where
  /-- The (finite) set of states. -/
  State : Type
  /-- Finiteness of the state set. -/
  fintypeState : Fintype State
  /-- The input position which is read at a given state. -/
  read : State → ℕ
  /-- The transition relation: `step q b q'` says that from `q`, having read the symbol `b`,
  the program may move to `q'`. -/
  step : State → Option Bool → State → Prop
  /-- The initial state. -/
  start : State
  /-- The accepting states. -/
  acc : State → Prop

attribute [instance] NBP.fintypeState

/-- The size of a branching program is its number of states. -/
