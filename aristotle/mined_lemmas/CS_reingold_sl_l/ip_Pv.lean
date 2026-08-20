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

lemma ip_Pv (hA : Sym A) (x y : Fin n → ℝ) : ip (Pv A x) y = ip x (Pv A y) := by
  have key : ∑ p : Fin n × Lab n, x (step A p.1 p.2) * y p.1
      = ∑ p : Fin n × Lab n, x p.1 * y (step A p.1 p.2) := by
    have h := sum_rot hA (fun p => x (step A p.1 p.2) * y p.1)
    rw [← h]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h1 : (rot A p).1 = step A p.1 p.2 := rot_fst p
    have h2 : step A (rot A p).1 (rot A p).2 = p.1 := by
      have hh := rot_fst (A := A) (rot A p)
      rw [rot_involutive hA p] at hh
      exact hh.symm
    rw [h2, h1]
  have e1 : ∑ u : Fin n, (∑ a : Lab n, x (step A u a)) / (2 * n) * y u
      = (∑ p : Fin n × Lab n, x (step A p.1 p.2) * y p.1) / (2 * n) := by
    rw [Fintype.sum_prod_type, Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [div_mul_eq_mul_div, Finset.sum_mul]
  have e2 : ∑ u : Fin n, x u * ((∑ a : Lab n, y (step A u a)) / (2 * n))
      = (∑ p : Fin n × Lab n, x p.1 * y (step A p.1 p.2)) / (2 * n) := by
    rw [Fintype.sum_prod_type, Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_div_assoc', Finset.mul_sum]
  unfold ip Pv
  rw [e1, e2, key]

/-- Sum of squares is preserved by the step reindexing. -/
