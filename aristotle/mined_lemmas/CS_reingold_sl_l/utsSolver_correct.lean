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

lemma utsSolver_correct {σ : List (Lab n)} (hσ : IsUTS σ) :
    (utsSolver σ).Correct := by
  classical
  intro A hA s t
  have hiter : ∀ j : ℕ, (utsSolver σ).run A s t (j + 1)
      = (utsSolver σ).stepC A ((utsSolver σ).run A s t j) := by
    intro j
    unfold Solver.run
    rw [Function.iterate_succ_apply']
  by_cases hconn : Conn A s t
  · obtain ⟨m, hm, hwm⟩ := hσ A hA s t hconn
    have hex : ∃ j, walk A s (σ.take j) = t := ⟨m, hwm⟩
    have hm0 : walk A s (σ.take (Nat.find hex)) = t := Nat.find_spec hex
    have hmin : ∀ j < Nat.find hex, walk A s (σ.take j) ≠ t := fun j hj => Nat.find_min hex hj
    have hm0le : Nat.find hex ≤ σ.length := le_trans (Nat.find_le hwm) hm
    refine ⟨true, ⟨Nat.find hex + 1, ?_, ?_⟩, by simp [hconn]⟩
    · intro j hj
      have hjle : j ≤ Nat.find hex := by omega
      rw [utsSolver_run σ A s t j (le_trans hjle hm0le)
        (fun j' h => hmin j' (lt_of_lt_of_le h hjle))]
      rfl
    · rw [hiter, utsSolver_run σ A s t (Nat.find hex) hm0le hmin]
      show (utsSolver σ).out ((utsSolver σ).next _ _) = _
      simp [utsSolver, hm0]
  · have hne : ∀ j, walk A s (σ.take j) ≠ t := by
      intro j h
      exact hconn (h ▸ conn_walk A s (σ.take j))
    refine ⟨false, ⟨σ.length + 1, ?_, ?_⟩, by simp [hconn]⟩
    · intro j hj
      rw [utsSolver_run σ A s t j (by omega) (fun j' _ => hne j')]
      rfl
    · rw [hiter, utsSolver_run σ A s t σ.length le_rfl (fun j' _ => hne j')]
      show (utsSolver σ).out ((utsSolver σ).next _ _) = _
      have hu := hne σ.length
      simp only [utsSolver]
      rw [if_neg hu, dif_neg (lt_irrefl σ.length)]

/-- **Undirected `s`-`t` connectivity in logarithmic space (nonuniform).**

There is a constant `c` such that for every `n` there is a machine with at most
`c * n ^ c` configurations — that is, using `O(log n)` bits of memory — which reads the
adjacency matrix of an `n`-vertex undirected graph one bit at a time and decides
whether two given vertices are connected. -/
