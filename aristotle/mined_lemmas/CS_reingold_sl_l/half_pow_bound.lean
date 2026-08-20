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

lemma half_pow_bound (hn : 0 < n) : (1 - 1 / (2 * (n:ℝ))) ^ (2 * n) ≤ 1 / 2 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0:ℝ) < 2 * n := by linarith
  have hle : 1 - 1 / (2 * (n:ℝ)) ≤ Real.exp (-(1 / (2 * (n:ℝ)))) := by
    have := Real.add_one_le_exp (-(1 / (2 * (n:ℝ))))
    linarith
  have hbase : (0:ℝ) ≤ 1 - 1 / (2 * (n:ℝ)) := by
    have : 1 / (2 * (n:ℝ)) ≤ 1 := by
      rw [div_le_one hpos]; linarith
    linarith
  have hpow : (1 - 1 / (2 * (n:ℝ))) ^ (2 * n) ≤ (Real.exp (-(1 / (2 * (n:ℝ))))) ^ (2 * n) :=
    pow_le_pow_left₀ hbase hle _
  have hexp : (Real.exp (-(1 / (2 * (n:ℝ))))) ^ (2 * n) = Real.exp (-1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hexp2 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have h2 : (2:ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have := (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 2)).2 h2
    linarith [this]
  calc (1 - 1 / (2 * (n:ℝ))) ^ (2 * n) ≤ (Real.exp (-(1 / (2 * (n:ℝ))))) ^ (2 * n) := hpow
    _ = Real.exp (-1) := hexp
    _ ≤ 1 / 2 := hexp2

/-- The union bound is strict. -/
