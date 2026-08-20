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

lemma Pv_mem_W (hA : Sym A) (hn : 0 < n) {x : Fin n → ℝ} (hx : InW A s x) :
    InW A s (Pv A x) := by
  have hn' : (0:ℝ) < 2 * n := by
    have : (0:ℝ) < n := by exact_mod_cast hn
    linarith
  constructor
  · intro u hu
    have : ∀ a : Lab n, x (step A u a) = 0 := by
      intro a
      exact hx.1 _ (fun h => hu ((step_conn_iff hA u a).1 h))
    simp [Pv, this]
  · -- the total mass is preserved
    have hsupp : ∀ u, ¬ Conn A s u → Pv A x u = 0 := by
      intro u hu
      have : ∀ a : Lab n, x (step A u a) = 0 := by
        intro a
        exact hx.1 _ (fun h => hu ((step_conn_iff hA u a).1 h))
      simp [Pv, this]
    have h1 : ∑ u ∈ comp A s, Pv A x u = ∑ u : Fin n, Pv A x u :=
      Finset.sum_subset (Finset.subset_univ _)
        (fun u _ hu => hsupp u (by simpa [mem_comp] using hu))
    have h2 : ∑ u : Fin n, Pv A x u = ∑ u : Fin n, x u := by
      unfold Pv
      rw [← Finset.sum_div, sum_step_const hA]
      field_simp
    have h3 : ∑ u : Fin n, x u = ∑ u ∈ comp A s, x u :=
      (Finset.sum_subset (Finset.subset_univ _)
        (fun u _ hu => hx.1 u (by simpa [mem_comp] using hu))).symm
    rw [h1, h2, h3, hx.2]

/-! ### A simple graph structure, used to extract simple paths -/

/-- The simple graph attached to the adjacency matrix `A`. -/
