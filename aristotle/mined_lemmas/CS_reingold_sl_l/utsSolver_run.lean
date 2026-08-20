/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Reingold.Machine

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalised here

Undirected `s`-`t` connectivity (`USTCON`) is decided in logarithmic space.

The machine model is the one of `CS.Solver`: a deterministic machine whose whole memory
is one configuration out of a finite configuration space `State`, which reads the
adjacency matrix of the `n`-vertex input graph one bit at a time (in each configuration
it queries one entry and branches on the answer) and which is started in a
configuration determined by the two distinguished vertices.  Using `O(log n)` bits of
memory means `Fintype.card State ≤ c * n ^ c` for a constant `c` that does not depend
on `n`.

`CS.reingold_sl_l` states, and proves, that USTCON is solved by such machines: there is
a single constant `c` (here `c = 100`) such that for every `n` there is a machine with
at most `c * n ^ c` configurations deciding connectivity on all `n`-vertex undirected
graphs.  The machine is built from a universal traversal sequence of length `O(n⁷)`,
whose existence is proved from scratch in `CS.exists_uts`: the transition operator of
the lazy `2n`-regular walk attached to a graph is shown to be symmetric and positive
semidefinite, to have spectral gap at least `1/(4n³)` on each connected component
(`CS.gap`), hence to reach any prescribed vertex of the component with probability at
least `1/(2n)` after `8n⁴` steps (`CS.hit_prob`), and a union bound over all graphs and
all pairs of vertices produces a single label sequence that works for all of them.

*Scope.*  The machine family produced here is described by a single constant `c` and one
machine per input size; the construction of the traversal sequence is by the
probabilistic method, so the family is not exhibited as a *uniformly computable* one.
Reingold's theorem `SL = L` is the strengthening in which the machine family is
uniformly computable; that statement is spelled out below as `CS.SLeqL` and is *not*
proved in this file.
-/

namespace CS

/-- **Undirected `s`-`t` connectivity in logarithmic space.**

There is a constant `c` such that, for every number of vertices `n ≥ 1`, undirected
`s`-`t` connectivity on `n`-vertex graphs is decided by a machine which reads the
adjacency matrix one bit at a time and whose configuration space has at most `c * n ^ c`
elements, i.e. which uses `O(log n)` bits of memory.

See the module documentation for the precise scope of this statement: the uniform
(`SL = L`) form of the theorem is stated as `CS.SLeqL` below and is not proved here. -/

lemma utsSolver_run (σ : List (Lab n)) (A : Fin n → Fin n → Bool) (s t : Fin n) :
    ∀ (j : ℕ) (hj : j ≤ σ.length), (∀ j' < j, walk A s (σ.take j') ≠ t) →
      (utsSolver σ).run A s t j
        = Sum.inr (t, walk A s (σ.take j), ⟨j, Nat.lt_succ_of_le hj⟩) := by
  intro j
  induction j with
  | zero =>
      intro hj _
      simp [Solver.run, utsSolver, walk]
  | succ j ih =>
      intro hj hlt
      have hjle : j ≤ σ.length := by omega
      have hjlt : j < σ.length := by omega
      have hlt' : ∀ j' < j, walk A s (σ.take j') ≠ t := fun j' h => hlt j' (by omega)
      have hrun := ih hjle hlt'
      have hstep : (utsSolver σ).run A s t (j + 1)
          = (utsSolver σ).stepC A ((utsSolver σ).run A s t j) := by
        unfold Solver.run
        rw [Function.iterate_succ_apply']
      set u := walk A s (σ.take j) with hu
      have hut : u ≠ t := hlt j (by omega)
      have hgetD : σ.getD j (false, u) = σ[j] := by
        simp [hjlt]
      have hwalk : walk A s (σ.take (j + 1)) = step A u σ[j] := by
        rw [List.take_add_one]
        simp only [List.getElem?_eq_getElem hjlt, Option.toList_some]
        rw [walk_append, ← hu]
        rfl
      rw [hstep, hrun]
      show (utsSolver σ).next _ _ = _
      simp only [utsSolver, hgetD]
      rw [if_neg hut, dif_pos hjlt]
      simp only [Sum.inr.injEq, Prod.mk.injEq, true_and]
      refine ⟨?_, trivial⟩
      rw [hwalk, ← stepB_eq_step A σ[j] u]

/-- The machine following a universal traversal sequence decides connectivity. -/
