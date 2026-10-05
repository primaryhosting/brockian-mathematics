/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Undirected s-t connectivity in logarithmic space (`SL = L`)

This file develops a self-contained formalisation of the statement
"undirected s-t connectivity is decidable in logarithmic space".

## The model of computation

A log-space machine working on `n`-vertex graphs is modelled by
`CS.GraphMachine`: a family of *configuration spaces* `Conf n`, one for each
input size, together with

* an initial configuration `init n s t` (the machine starts knowing the two
  distinguished vertices, which take `O(log n)` bits to write down);
* a *query* function, selecting the single entry of the adjacency matrix that
  the machine inspects in the current configuration (this is the read-only
  input head: the input is never stored in the configuration);
* a deterministic transition `step`, depending only on the current
  configuration and the bit that was read;
* an output function `out`, which is `none` while the machine is still running.

The machine runs in space `O(log n)` exactly when its configuration space has
polynomial size, which is what `CS.GraphMachine.PolySize` records.  This is the
standard configuration-graph characterisation of log-space computation.

`CS.InLogspace P` says that some polynomially-sized machine decides `P`, where
"decides" means that the *first* output produced by the machine is the correct
answer (`CS.GraphMachine.Decides`).

## The result

`CS.reingold_sl_l` shows that undirected s-t connectivity (`CS.USTCON`) is
decided by such a machine, assuming the combinatorial core of Reingold's
theorem, stated here as `CS.UESHypothesis`: for every vertex count `n` there is
a *universal exploration sequence* of polynomial length, i.e. a single sequence
of vertex names `u 0, u 1, …` such that the greedy walk
"move to `u k` if it is adjacent to the current vertex, otherwise stay put"
started anywhere visits the whole connected component of its starting point.

`CS.exists_universal_seq` proves unconditionally that universal exploration
sequences always exist (with no bound on their length), so the content of
`CS.UESHypothesis` is exactly the polynomial length bound, which is the
combinatorial heart of Reingold's theorem.
-/

namespace CS

/-! ## Undirected graphs and connectivity -/

/-- An undirected graph on the vertex set `Fin n`, given by a symmetric
adjacency matrix. -/

private lemma exists_seq_for_finset {n : ℕ} (hn : 0 < n)
    (S : Finset (UGraph n × Fin n × Fin n)) :
    ∃ (L : ℕ) (u : ℕ → Fin n), ∀ p ∈ S, Reach p.1 p.2.1 p.2.2 →
      ∃ k ≤ L, walk p.1 u p.2.1 k = p.2.2 := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨0, (fun _ => ⟨0, hn⟩), by simp⟩
  | insert p S _ ih =>
      obtain ⟨L, u, hu⟩ := ih
      obtain ⟨G, s, t⟩ := p
      by_cases hst : Reach G s t
      · have hv : Reach G (walk G u s L) t :=
          (reach_symm (reach_walk G u s L)).trans hst
        obtain ⟨m, w, hw⟩ := exists_seq_reaching G hv
        refine ⟨L + m, catSeq L u w, ?_⟩
        rintro q hq hq'
        rcases Finset.mem_insert.1 hq with rfl | hqS
        · refine ⟨L + m, le_rfl, ?_⟩
          rw [walk_catSeq_add G L u w s m, hw]
        · obtain ⟨k, hkL, hk⟩ := hu q hqS hq'
          exact ⟨k, by omega, by rw [walk_catSeq_le q.1 L u w q.2.1 hkL]; exact hk⟩
      · refine ⟨L, u, ?_⟩
        rintro q hq hq'
        rcases Finset.mem_insert.1 hq with rfl | hqS
        · exact absurd hq' hst
        · exact hu q hqS hq'

/-- **Universal exploration sequences exist.**  For every positive vertex count
there is a finite instruction sequence whose greedy walk explores the whole
connected component of its starting vertex, in every `n`-vertex undirected
graph and from every starting vertex. -/
