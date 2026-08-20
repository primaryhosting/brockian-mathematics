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

lemma ustconSym_reach_of_graph (hsym : ∀ i j, adjB i j = adjB j i) (u : Fin N)
    (h : Relation.ReflTransGen (fun i j => adjB i j = true) s u) :
    Relation.ReflTransGen ((ustconSym N t s).rel (fun p => adjB p.1 p.2))
      ((s, s) : Fin N × Fin N) ((u, u) : Fin N × Fin N) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail v w _ hvw ih =>
    have e1 : (ustconSym N t s).rel (fun p => adjB p.1 p.2) ((v, v) : Fin N × Fin N)
        ((v, w) : Fin N × Fin N) := (ustconSym_rel N s t adjB _ _).2 (Or.inl rfl)
    have e2 : (ustconSym N t s).rel (fun p => adjB p.1 p.2) ((v, w) : Fin N × Fin N)
        ((w, v) : Fin N × Fin N) :=
      (ustconSym_rel N s t adjB _ _).2 (Or.inr ⟨rfl, rfl, hvw, by rw [hsym]; exact hvw⟩)
    have e3 : (ustconSym N t s).rel (fun p => adjB p.1 p.2) ((w, v) : Fin N × Fin N)
        ((w, w) : Fin N × Fin N) := (ustconSym_rel N s t adjB _ _).2 (Or.inl rfl)
    exact ((ih.tail e1).tail e2).tail e3

