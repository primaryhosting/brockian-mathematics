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

theorem symSimDet_of_ustcon (hR : UstconLogspace) : SymSimDet := by
  classical
  obtain ⟨c, hc⟩ := hR
  refine ⟨2 * c + 2, fun I S => ?_⟩
  obtain ⟨DU, hDUcard, hDU⟩ :=
    hc (Fintype.card (Option S.M)) ((Fintype.equivFin (Option S.M)) (some S.start))
      ((Fintype.equivFin (Option S.M)) none)
  obtain ⟨D', hD'card, hD'⟩ := DetMachine.pullback DU
    (fun ij => (confQuery S ((Fintype.equivFin (Option S.M)).symm ij.1),
      confQuery S ((Fintype.equivFin (Option S.M)).symm ij.2)))
    (fun ij a b => confAdj S ((Fintype.equivFin (Option S.M)).symm ij.1) a
      ((Fintype.equivFin (Option S.M)).symm ij.2) b)
  refine ⟨D', ?_, ?_⟩
  · -- the size bound
    have hcardO : Fintype.card (Option S.M) = Fintype.card S.M + 1 := by
      simp [Fintype.card_option]
    have hsq : Fintype.card S.M + 3 ≤ (Fintype.card S.M + 2) ^ 2 := by nlinarith
    have hfour : 4 ≤ (Fintype.card S.M + 2) ^ 2 := by nlinarith
    calc Fintype.card D'.M ≤ 4 * Fintype.card DU.M := hD'card
      _ ≤ 4 * (Fintype.card (Option S.M) + 2) ^ c := Nat.mul_le_mul_left _ hDUcard
      _ = 4 * (Fintype.card S.M + 3) ^ c := by rw [hcardO]
      _ ≤ 4 * ((Fintype.card S.M + 2) ^ 2) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsq c)
      _ = 4 * (Fintype.card S.M + 2) ^ (2 * c) := by rw [← pow_mul]
      _ ≤ (Fintype.card S.M + 2) ^ 2 * (Fintype.card S.M + 2) ^ (2 * c) :=
          Nat.mul_le_mul_right _ hfour
      _ = (Fintype.card S.M + 2) ^ (2 * c + 2) := by ring
  · intro x
    rw [hD' x]
    have hsymm : ∀ i j : Fin (Fintype.card (Option S.M)),
        pullbackInput
          (fun ij => (confQuery S ((Fintype.equivFin (Option S.M)).symm ij.1),
            confQuery S ((Fintype.equivFin (Option S.M)).symm ij.2)))
          (fun ij a b => confAdj S ((Fintype.equivFin (Option S.M)).symm ij.1) a
            ((Fintype.equivFin (Option S.M)).symm ij.2) b) x (i, j)
        = pullbackInput
          (fun ij => (confQuery S ((Fintype.equivFin (Option S.M)).symm ij.1),
            confQuery S ((Fintype.equivFin (Option S.M)).symm ij.2)))
          (fun ij a b => confAdj S ((Fintype.equivFin (Option S.M)).symm ij.1) a
            ((Fintype.equivFin (Option S.M)).symm ij.2) b) x (j, i) := by
      intro i j
      exact confAdj_symm S _ _ _ _
    rw [hDU _ hsymm]
    exact (reflTransGen_congr (Fintype.equivFin (Option S.M)) (confRel S x) (some S.start)
      none).trans (confRel_reach_iff S x)

/-- `SL ⊆ L`, given Reingold's theorem. -/
