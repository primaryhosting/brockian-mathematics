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

lemma uesMachine_run {n : ℕ} (hn : 0 < n) (G : UGraph n) (s t : Fin n) (k : ℕ) :
    (uesMachine C d f).run G ((uesMachine C d f).init n s t) k =
      (walk G (f n hn) s (min k (bnd C d n)), t,
        ⟨min k (bnd C d n), by omega⟩) := by
  induction k with
  | zero => simp [GraphMachine.run, uesMachine, walk]
  | succ k ih =>
      rw [GraphMachine.run, ih]
      by_cases hlt : min k (bnd C d n) < bnd C d n
      · have hk : k < bnd C d n := by omega
        have h1 : min k (bnd C d n) = k := by omega
        have h2 : min (k + 1) (bnd C d n) = k + 1 := by omega
        simp only [uesMachine, h1, useq_eq f hn]
        rw [dif_pos (by omega : k < bnd C d n)]
        simp only [h2, walk_succ]
      · have hk : min k (bnd C d n) = bnd C d n := by omega
        have h2 : min (k + 1) (bnd C d n) = bnd C d n := by omega
        simp only [uesMachine, hk, h2]
        rw [dif_neg (by omega : ¬ bnd C d n < bnd C d n)]

