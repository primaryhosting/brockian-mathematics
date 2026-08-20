import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We model space bounded computation by machines whose *memory* is a finite type `M`; the space
used is `log₂ (card M)`, so that "logarithmic space" means "polynomially many memory states".
A machine inspects, in each memory state, at most one position of its input, and updates its
memory state according to the bit read.

* `CS.DetMachine` is a deterministic such machine; it accepts an input when its (unique)
  computation reaches an accepting memory state.
* `CS.SymMachine` is a *symmetric* nondeterministic machine in the sense of Lewis and
  Papadimitriou: its transition relation is symmetric, so its configuration graph is an
  undirected graph, and it accepts an input when an accepting memory state is connected to
  the initial one in that graph.
* `CS.Lclass` and `CS.SLclass` are the corresponding classes of languages, a language being
  decided by a family of machines with polynomially many memory states, one for each input
  length.  (The families are not required to be uniformly generated.)
* `CS.UstconLogspace` is Reingold's theorem: undirected `s`-`t` connectivity, on graphs given
  by their adjacency matrix, is decided by deterministic machines with polynomially many
  memory states.  Its proof — the zig-zag construction of expanders — is *not* formalised
  here; it is taken as an explicit hypothesis of the main theorem.

The main theorem `CS.reingold_sl_l` derives `SL = L` from it.  Both inclusions are proved:

* `CS.inSL_of_inL` (`L ⊆ SL`, unconditional) simulates a deterministic machine by a symmetric
  one after adding a step counter, so that the configuration graph becomes a forest whose
  components are trees rooted at the final configurations;
* `CS.inL_of_inSL` (`SL ⊆ L`) runs the connectivity algorithm on the configuration graph of a
  symmetric machine, each adjacency query being answered by reading two bits of the input.

Finally `CS.ustconLogspace_iff_symSimDet` shows that the hypothesis is not stronger than what
is being proved: it is *equivalent* to the machine-level form of `SL = L`, because undirected
connectivity is itself decided by a symmetric machine with quadratically many memory states.
-/

namespace CS

/-- Reading the bit of the input `x` at an optional position: a machine state that queries no
position reads the default value `false`. -/

def readBit {I : Type} (x : I → Bool) : Option I → Bool
  | none => false
  | some i => x i

/-- A deterministic space bounded machine working on an input `x : I → Bool`.

The memory of the machine is the finite type `M`; the *space* used by the machine is
`log₂ (card M)`, so that "logarithmic space" means "polynomially many memory states".
At each step the machine reads (at most) one bit of the input, the position being determined
by the current memory state, and updates its memory state accordingly. It accepts if it ever
enters a memory state marked as accepting. -/
structure DetMachine (I : Type) where
  /-- The finite memory of the machine. -/
  M : Type
  [fintypeM : Fintype M]
  /-- The initial memory state. -/
  start : M
  /-- The input position inspected in a given memory state (`none` = no position). -/
  query : M → Option I
  /-- The memory update, as a function of the current state and of the bit just read. -/
  next : M → Bool → M
  /-- The accepting memory states. -/
  acc : M → Bool

attribute [instance] DetMachine.fintypeM

namespace DetMachine

variable {I : Type}

/-- One computation step of a deterministic machine on input `x`. -/
