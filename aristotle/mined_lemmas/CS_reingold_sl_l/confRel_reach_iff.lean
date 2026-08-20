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

theorem confRel_reach_iff :
    Relation.ReflTransGen (confRel S x) (some S.start) none ↔ S.Accepts x := by
  constructor
  · intro h
    have key : ∀ v, Relation.ReflTransGen (confRel S x) (some S.start) v →
        (S.Accepts x ∨ ∃ r, v = some r ∧ Relation.ReflTransGen (S.rel x) S.start r) := by
      intro v hv
      induction hv with
      | refl => exact Or.inr ⟨S.start, rfl, Relation.ReflTransGen.refl⟩
      | @tail b c _ hbc ih =>
        rcases ih with hacc | ⟨r, hr, hrun⟩
        · exact Or.inl hacc
        · subst hr
          rcases confRel_some_cases S x r c hbc with ⟨hc, hacc⟩ | ⟨t, hc, hrt⟩
          · exact Or.inl ⟨r, hrun, hacc⟩
          · exact Or.inr ⟨t, hc, hrun.tail hrt⟩
    rcases key none h with h1 | ⟨r, hr, _⟩
    · exact h1
    · exact absurd hr (by simp)
  · rintro ⟨q, hq, hacc⟩
    have : Relation.ReflTransGen (confRel S x) (some S.start) (some q) :=
      Relation.ReflTransGen.lift (r := S.rel x) some
        (fun a b hab => (confRel_some_some S x a b).2 hab) hq
    exact this.tail ((confRel_some_none S x q).2 hacc)

end ConfGraph

/-!
## `L ⊆ SL`

A deterministic machine is simulated by a symmetric one by adding a step counter: the
configuration graph of the layered machine is a functional graph all of whose orbits reach a
fixed point (a configuration of the last layer), hence each of its connected components is a
tree rooted at such a fixed point.  Consequently, undirected reachability in the layered
graph coincides with the deterministic computation.
-/

section LtoSL

variable {I : Type} (D : DetMachine I) (x : I → Bool)

/-- The successor on layers, stationary on the last layer. -/
