/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Savitch.Model
import RequestProject.Savitch.Reach
import RequestProject.Savitch.Interp
import RequestProject.Savitch.BigStep
import RequestProject.Savitch.Invariant
import RequestProject.Savitch.Encode

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

`NSPACE(f) ⊆ DSPACE(f²)`, and consequently `PSPACE = NPSPACE` (Savitch's theorem).

The model of computation is the standard configuration-graph model, set up in
`RequestProject.Savitch.Model`: configurations are natural numbers (binary strings), a machine
runs in space `f` on input `x` if all configurations reachable on `x` are `< 2 ^ f |x|`, and
one step may depend on the current configuration together with the single input symbol scanned
by the input head, whose position is determined by the configuration.  The initial
configuration may depend on the input length (the usual assumption that the space bound is
constructible).  No computability assumption is imposed on the transition functions.

The deterministic simulator is built explicitly: it performs the depth-first evaluation of
Savitch's divide-and-conquer recursion, its states are recursion stacks of depth at most `s`,
each frame holding boundedly many numbers `< 2 ^ s`, and the whole state is encoded as a
natural number `< 2 ^ (42 * (s + 1) ^ 2)`.  Hence a nondeterministic machine running in space
`f` is simulated deterministically in space `42 * (f + 1) ^ 2`.
-/

namespace CS

open Classical

variable {Γ : Type}

/-! ### Deterministic machines are nondeterministic machines -/

/-- A deterministic machine, viewed as a nondeterministic one. -/

theorem decSt_encSt {st : St} (h : Good st) : decSt (encSt st) = st := by
  have hex : ∃ st', Good st' ∧ encSt st' = encSt st := ⟨st, h, rfl⟩
  rw [decSt, dif_pos hex]
  obtain ⟨hgood, heq⟩ := hex.choose_spec
  exact encSt_injective hgood h heq

end CS

import Mathlib

/-!
# The divide-and-conquer reachability predicate

For a directed graph `edge` on the natural numbers and a "space bound" `s`, we define
`Reach s edge k a b`, the Savitch predicate: `b` can be reached from `a` by a path of
length at most `2 ^ k` all of whose intermediate vertices are `< 2 ^ s`.  It obeys the
divide-and-conquer recursion which is the heart of Savitch's theorem.

The main results are:

* `CS.Reach.sound`: `Reach s edge k a b` implies `b` is reachable from `a`;
* `CS.Reach.complete`: if every vertex reachable from `a` is `< 2 ^ s`, then reachability
  from `a` implies `Reach s edge s a b`.
-/

namespace CS

/-- The Savitch reachability predicate: `Reach s edge k a b` says that `b` can be reached
from `a` by a path of length at most `2 ^ k` whose intermediate vertices are all `< 2 ^ s`. -/
