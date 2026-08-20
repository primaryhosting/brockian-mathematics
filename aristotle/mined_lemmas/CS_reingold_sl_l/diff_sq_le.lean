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

lemma diff_sq_le (hA : Sym A) (x : Fin n → ℝ) {u v : Fin n} (h : Conn A u v) :
    (x u - x v) ^ 2 ≤ (n : ℝ) * Dform A x := by
  obtain ⟨w⟩ := conn_reachable (A := A) h
  set p := w.bypass with hp
  have hpath : p.IsPath := w.bypass_isPath
  have hnodup : p.darts.Nodup := SimpleGraph.Walk.darts_nodup_of_support_nodup hpath.support_nodup
  have htel : ∑ d ∈ p.darts.toFinset, (x d.fst - x d.snd) = x u - x v := by
    rw [List.sum_toFinset _ hnodup]
    exact telescope x p
  have hcard : (p.darts.toFinset.card : ℝ) ≤ n := by
    have h1 : p.darts.toFinset.card = p.darts.length := List.toFinset_card_of_nodup hnodup
    have h2 : p.darts.length = p.length := p.length_darts
    have h3 : p.length < Fintype.card (Fin n) := hpath.length_lt
    have h4 : p.darts.toFinset.card ≤ n := by
      rw [h1, h2]; simpa using h3.le
    exact_mod_cast h4
  have hsq := sq_sum_le_card_mul_sum_sq (s := p.darts.toFinset)
    (f := fun d => x d.fst - x d.snd)
  rw [htel] at hsq
  have hle := dart_sum_le hA x p.darts.toFinset
  have hnn : 0 ≤ ∑ d ∈ p.darts.toFinset, (x d.fst - x d.snd) ^ 2 :=
    Finset.sum_nonneg fun d _ => sq_nonneg _
  calc (x u - x v)^2
      ≤ (p.darts.toFinset.card : ℝ) * ∑ d ∈ p.darts.toFinset, (x d.fst - x d.snd)^2 := hsq
    _ ≤ (n : ℝ) * ∑ d ∈ p.darts.toFinset, (x d.fst - x d.snd)^2 :=
        mul_le_mul_of_nonneg_right hcard hnn
    _ ≤ (n : ℝ) * Dform A x := mul_le_mul_of_nonneg_left hle (by positivity)

/-- The Poincaré inequality on the subspace `W`. -/
