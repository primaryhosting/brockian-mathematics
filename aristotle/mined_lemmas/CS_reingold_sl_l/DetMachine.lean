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

lemma DetMachine.pullback :
    ∃ D' : DetMachine I, Fintype.card D'.M ≤ 4 * Fintype.card D.M ∧
      ∀ x : I → Bool, (D'.Accepts x ↔ D.Accepts (pullbackInput f g x)) := by
  refine ⟨pullbackMachine D f g, ?_, ?_⟩
  · show Fintype.card (D.M × Option Bool) ≤ _
    simp [Fintype.card_prod]
    omega
  · intro x
    constructor
    · rintro ⟨K, hK⟩
      obtain ⟨k, h | ⟨j, hj, h⟩⟩ := pullback_inv D f g x K
      · exact ⟨k, by rw [show D.run (pullbackInput f g x) k
          = (((pullbackMachine D f g).stepFun x)^[K] ((D.start, none) : D.M × Option Bool)).1 from
          by rw [h]]; exact hK⟩
      · exact ⟨k, by rw [show D.run (pullbackInput f g x) k
          = (((pullbackMachine D f g).stepFun x)^[K] ((D.start, none) : D.M × Option Bool)).1 from
          by rw [h]]; exact hK⟩
    · rintro ⟨k, hk⟩
      obtain ⟨K, hK⟩ := pullback_reach D f g x k
      exact ⟨K, by
        show (pullbackMachine D f g).acc _ = true
        rw [show ((pullbackMachine D f g).run x K) = (((pullbackMachine D f g).stepFun x)^[K]
          ((D.start, none) : D.M × Option Bool)) from rfl, hK]
        exact hk⟩

end Pullback

/-!
## The configuration graph of a symmetric machine

The configuration graph of a symmetric machine `S` on an input `x` is an undirected graph on
the memory states of `S`; we add one extra vertex `none`, joined to all accepting states, so
that `S` accepts `x` exactly when the two distinguished vertices `some S.start` and `none`
are connected.
-/

section ConfGraph

variable {I : Type} (S : SymMachine I)

open scoped Classical in
/-- The adjacency of the configuration graph, as a function of the two bits read at its two
endpoints. -/
