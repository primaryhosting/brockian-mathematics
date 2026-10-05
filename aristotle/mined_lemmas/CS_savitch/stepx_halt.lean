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

theorem stepx_halt (x : List Γ) :
    stepx N x ⟨s, a₀, tg, .halt v, S⟩ = ⟨s, a₀, tg, .halt v, S⟩ := rfl

end StepLemmas

end CS

import Mathlib

/-!
# A configuration-graph model of space-bounded computation

This file sets up the model of space-bounded computation used to state and prove
Savitch's theorem.

A machine works on inputs `x : List Γ`.  Its *configurations* are natural numbers,
thought of as binary strings: a machine "uses space `s`" on `x` if every configuration
reachable on input `x` is `< 2 ^ s` (i.e. fits in `s` bits).  A configuration determines
the position `head c` of the read-only input head, and the machine's transition may
depend on the configuration together with the single input symbol currently scanned
(`none` if the head is outside the input).  The initial configuration may depend on the
length of the input (this is the usual assumption that the space bound is constructible).

No computability assumption is placed on the transition functions; the model is therefore
the standard configuration-graph abstraction of space-bounded computation.
-/

namespace CS



/-- A nondeterministic space-bounded machine over input alphabet `Γ`. -/
structure NMachine (Γ : Type) where
  /-- Initial configuration, as a function of the input length. -/
  start : ℕ → ℕ
  /-- Position of the input head in a given configuration. -/
  head : ℕ → ℕ
  /-- Successor configurations, given the current configuration and the scanned symbol. -/
  next : ℕ → Option Γ → Set ℕ
  /-- Accepting configurations. -/
  accept : ℕ → Prop

/-- A deterministic space-bounded machine over input alphabet `Γ`. -/
structure DMachine (Γ : Type) where
  /-- Initial configuration, as a function of the input length. -/
  start : ℕ → ℕ
  /-- Position of the input head in a given configuration. -/
  head : ℕ → ℕ
  /-- Successor configuration, given the current configuration and the scanned symbol. -/
  next : ℕ → Option Γ → ℕ
  /-- `some b` on halting configurations with verdict `b`, `none` otherwise. -/
  result : ℕ → Option Bool

namespace NMachine

variable {Γ : Type}

/-- One computation step on input `x`. -/
