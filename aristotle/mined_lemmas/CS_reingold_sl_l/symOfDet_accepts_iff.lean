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

theorem symOfDet_accepts_iff : (symOfDet D).Accepts x ↔ D.Accepts x := by
  classical
  obtain ⟨hr1, hr2, hr3⟩ := layRun_iterate_start D x (Fintype.card D.M + 1) le_rfl
  constructor
  · rintro ⟨Q, hQ, hacc⟩
    have haccQ : ((Q.2 : ℕ) = Fintype.card D.M + 1 ∧ Q.1.2 = true) := by
      simpa [symOfDet] using hacc
    have hfix : layRoot D x Q = Q := by
      have : layRun D x Q = Q := layRun_fixed D x Q haccQ.1
      simpa [layRoot] using Function.iterate_fixed this (Fintype.card D.M + 1)
    have hroot : layRoot D x (symOfDet D).start = Q := by
      rw [layRoot_of_reach D x hQ, hfix]
    have : ((layRun D x)^[Fintype.card D.M + 1] (symOfDet D).start).1.2 = true := by
      rw [show ((layRun D x)^[Fintype.card D.M + 1] (symOfDet D).start) = Q from hroot]
      exact haccQ.2
    obtain ⟨i, _, hi⟩ := hr3.1 this
    exact ⟨i, hi⟩
  · rintro ⟨k, hk⟩
    obtain ⟨k', hk', hk'eq⟩ :=
      exists_iterate_le_card (D.stepFun x) D.start k
    have hacc' : D.acc (D.run x k') = true := by
      rw [show D.run x k' = D.run x k from hk'eq]
      exact hk
    refine ⟨layRoot D x (symOfDet D).start, reach_layRun_iterate D x _ _, ?_⟩
    have hflag : ((layRun D x)^[Fintype.card D.M + 1] (symOfDet D).start).1.2 = true :=
      hr3.2 ⟨k', by omega, hacc'⟩
    have hlayer := layRoot_layer D x (symOfDet D).start
    simp only [symOfDet, decide_eq_true_eq]
    exact ⟨hlayer, hflag⟩

