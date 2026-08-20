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

theorem inL_of_inSL (hR : UstconLogspace) {P : Lang} (h : inSL P) : inL P := by
  obtain ⟨c, hc⟩ := symSimDet_of_ustcon hR
  obtain ⟨cS, hS⟩ := h
  refine ⟨(cS + 2) * c, fun n => ?_⟩
  obtain ⟨S, hcard, hdec⟩ := hS n
  obtain ⟨D, hDcard, hD⟩ := hc (Fin n) S
  refine ⟨D, ?_, fun x => (hD x).trans (hdec x)⟩
  have hone : 1 ≤ (n + 2) ^ cS := Nat.one_le_pow _ _ (by omega)
  have hfour : 4 ≤ (n + 2) ^ 2 := by
    have := Nat.pow_le_pow_left (show 2 ≤ n + 2 by omega) 2
    simpa using this
  have h1 : Fintype.card S.M + 2 ≤ (n + 2) ^ (cS + 2) := by
    calc Fintype.card S.M + 2 ≤ (n + 2) ^ cS + 2 := by omega
      _ ≤ 4 * (n + 2) ^ cS := by omega
      _ ≤ (n + 2) ^ 2 * (n + 2) ^ cS := Nat.mul_le_mul_right _ hfour
      _ = (n + 2) ^ (cS + 2) := by ring
  calc Fintype.card D.M ≤ (Fintype.card S.M + 2) ^ c := hDcard
    _ ≤ ((n + 2) ^ (cS + 2)) ^ c := Nat.pow_le_pow_left h1 c
    _ = (n + 2) ^ ((cS + 2) * c) := by rw [← pow_mul]

/-!
## Undirected connectivity is a symmetric-logspace problem

Conversely, undirected `s`-`t` connectivity is decided by a symmetric machine whose memory
stores a current vertex together with a candidate neighbour, hence with quadratically many
memory states.  Consequently Reingold's theorem is not merely sufficient but also necessary
for the simulation of symmetric machines by deterministic ones.
-/

section UstconSym

/-- A symmetric machine deciding undirected `s`-`t` connectivity: its memory stores the
current vertex and a candidate neighbour, it may change the candidate freely, and it may
move to the candidate along an edge. -/
