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

lemma count_walk_eq (A : Fin n → Fin n → Bool) (T : ℕ) (u v : Fin n) :
    ((((seqs n T).filter (fun σ => walk A u σ = v)).card : ℝ))
      = (2 * n) ^ T * Pit A T (delta v) u := by
  classical
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hn' : (0:ℝ) < 2 * n := by
    have : (0:ℝ) < n := by exact_mod_cast hn
    linarith
  induction T generalizing u with
  | zero =>
      have : (seqs n 0).filter (fun σ => walk A u σ = v)
          = if u = v then {([] : List (Lab n))} else ∅ := by
        by_cases h : u = v <;> simp [seqs, walk, h, Finset.filter_singleton]
      rw [this]
      by_cases h : u = v <;> simp [Pit_zero, delta, h]
  | succ T ih =>
      rw [count_walk_split A T u v]
      have hstep : Pit A (T + 1) (delta v) u
          = (∑ a : Lab n, Pit A T (delta v) (step A u a)) / (2 * n) := by
        rw [Pit_succ]
        rfl
      rw [hstep]
      push_cast
      rw [Finset.sum_congr rfl (fun a _ => ih (step A u a)), ← Finset.mul_sum]
      field_simp
      ring

/-- Counting version of the hitting estimate. -/
