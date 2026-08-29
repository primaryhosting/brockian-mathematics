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

theorem iter_a₀ (N : NMachine Γ) (x : List Γ) :
    ∀ (t : ℕ) (st : St), (iter N x t st).a₀ = st.a₀ := by
  intro t
  induction t with
  | zero => intro st; rfl
  | succ t ih => intro st; rw [iter]; rw [ih]; exact step_a₀ N _ st

end CS

import RequestProject.Savitch.Model
import RequestProject.Savitch.Reach

/-!
# The Savitch simulator, as an abstract stack machine

Given a nondeterministic machine `N` we describe a *deterministic* procedure which decides
acceptance of `N` by depth-first evaluation of the Savitch recursion, using an explicit
stack of recursion frames.  This file defines the states of that procedure and its one-step
transition function, and proves the "big-step" correctness lemmas: from a state which asks
for the value of `Reach s edge k a b`, the procedure reaches, after finitely many steps, the
state which returns the correct boolean, with the rest of the stack untouched.
-/

namespace CS

open Classical

/-- A recursion frame: we are computing `Reach s edge (k+1) a b`, currently trying the
midpoint `m`; `ph = false` means we await the value of `Reach s edge k a m`, and `ph = true`
means the first half succeeded and we await `Reach s edge k m b`. -/
structure Frame where
  /-- source vertex -/
  a : ℕ
  /-- target vertex -/
  b : ℕ
  /-- recursion level of the awaited value -/
  k : ℕ
  /-- current midpoint -/
  m : ℕ
  /-- phase of the frame -/
  ph : Bool
deriving DecidableEq

/-- The control state of the simulator. -/
inductive Ctrl where
  /-- start the test of the current target configuration -/
  | init : Ctrl
  /-- compute `Reach s edge k a b` -/
  | eval : ℕ → ℕ → ℕ → Ctrl
  /-- return the value `v` to the top frame -/
  | ret : Bool → Ctrl
  /-- halt with verdict `v` -/
  | halt : Bool → Ctrl
deriving DecidableEq

/-- A state of the simulator: the space bound `s`, the initial configuration `a₀` of the
simulated machine, the target configuration currently being tested, the control state, and
the recursion stack. -/
structure St where
  /-- space bound of the simulated machine -/
  s : ℕ
  /-- initial configuration of the simulated machine -/
  a₀ : ℕ
  /-- configuration currently tested for acceptance -/
  target : ℕ
  /-- control state -/
  ctrl : Ctrl
  /-- recursion stack -/
  stack : List Frame
deriving DecidableEq

variable {Γ : Type}

/-- One step of the simulator, given the currently scanned input symbol `σ`. -/
