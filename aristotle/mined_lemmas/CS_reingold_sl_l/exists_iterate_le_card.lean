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

lemma exists_iterate_le_card {M : Type} [Fintype M] (g : M → M) (a : M) (k : ℕ) :
    ∃ k' ≤ Fintype.card M, g^[k'] a = g^[k] a := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k ≤ Fintype.card M
    · exact ⟨k, hk, rfl⟩
    push_neg at hk
    have hni : ¬ Function.Injective (fun i : Fin (Fintype.card M + 1) => g^[(i : ℕ)] a) := by
      intro hinj
      have := Fintype.card_le_of_injective _ hinj
      simp at this
    rw [Function.not_injective_iff] at hni
    obtain ⟨i, j, hij, hne⟩ := hni
    set p := min (i : ℕ) (j : ℕ) with hp
    set q := max (i : ℕ) (j : ℕ) with hq
    have hpq : p < q := by
      have : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
      omega
    have hqle : q ≤ Fintype.card M := by
      have hi := i.isLt
      have hj := j.isLt
      omega
    have hpqeq : g^[p] a = g^[q] a := by
      rcases le_total (i : ℕ) (j : ℕ) with h | h
      · simp only [hp, hq, min_eq_left h, max_eq_right h]
        exact hij
      · simp only [hp, hq, min_eq_right h, max_eq_left h]
        exact hij.symm
    have hkq : q ≤ k := le_of_lt (lt_of_le_of_lt hqle hk)
    have key : g^[k - (q - p)] a = g^[k] a := by
      have h1 : g^[k] a = g^[(k - q) + q] a := by
        congr 1
        omega
      have h2 : g^[(k - q) + q] a = g^[k - q] (g^[q] a) := by
        rw [Function.iterate_add_apply]
      have h3 : g^[k - q] (g^[p] a) = g^[(k - q) + p] a := by
        rw [Function.iterate_add_apply]
      have h4 : (k - q) + p = k - (q - p) := by omega
      rw [h1, h2, ← hpqeq, h3, h4]
    obtain ⟨k', hk', hk'eq⟩ := ih (k - (q - p)) (by omega)
    exact ⟨k', hk', by rw [hk'eq, key]⟩

/-!
## Pulling a machine back along a 2-local reduction

If the bits of the input of a machine `D` are each computable from at most two bits of another
input `x` (a "2-local reduction"), then `D` can be simulated on `x` at the cost of a constant
factor in the number of memory states: the simulating machine reads the two relevant bits of
`x` in two consecutive steps.
-/

section Pullback

variable {I J : Type} (D : DetMachine J) (f : J → Option I × Option I)
  (g : J → Bool → Bool → Bool) (x : I → Bool)

/-- The input of `D` obtained from `x` through a 2-local reduction. -/
