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

theorem inSL_of_inL {P : Lang} (h : inL P) : inSL P := by
  obtain ⟨c, hc⟩ := h
  refine ⟨2 * c + 3, fun n => ?_⟩
  obtain ⟨D, hcard, hdec⟩ := hc n
  refine ⟨symOfDet D, ?_, fun x => (symOfDet_accepts_iff D x).trans (hdec x)⟩
  have hone : 1 ≤ (n + 2) ^ c := Nat.one_le_pow _ _ (by omega)
  have h8 : 8 ≤ (n + 2) ^ 3 := by
    have := Nat.pow_le_pow_left (show 2 ≤ n + 2 by omega) 3
    simpa using this
  calc Fintype.card (symOfDet D).M
      = Fintype.card D.M * 2 * (Fintype.card D.M + 2) := symOfDet_card D
    _ ≤ (n + 2) ^ c * 2 * ((n + 2) ^ c + 2) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_right _ hcard) (by omega)
    _ ≤ 8 * ((n + 2) ^ c * (n + 2) ^ c) := by nlinarith
    _ ≤ (n + 2) ^ 3 * ((n + 2) ^ c * (n + 2) ^ c) := Nat.mul_le_mul_right _ h8
    _ = (n + 2) ^ (2 * c + 3) := by ring


/-- The machine-level form of `SL = L`: every symmetric machine can be simulated by a
deterministic machine with polynomially many memory states, i.e. with the same space up to a
constant factor. -/
