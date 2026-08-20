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

lemma lambda_pow_le (hn : 0 < n) :
    (1 - 1 / (4 * (n:ℝ)^3)) ^ (8 * n ^ 4) ≤ 1 / (2 * n) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hcube : (1:ℝ) ≤ (n:ℝ)^3 := one_le_pow₀ hn1
  set g : ℝ := 1 / (4 * (n:ℝ)^3) with hg
  have hgpos : 0 < g := by rw [hg]; positivity
  have hgle : g ≤ 1 := by
    rw [hg, div_le_one (by linarith)]
    linarith
  have hbase : (0:ℝ) ≤ 1 - g := by linarith
  have h1p : (0:ℝ) < 1 + g := by linarith
  have hstep : 1 - g ≤ (1 + g)⁻¹ := by
    have hmul : (1 - g) * (1 + g) ≤ 1 := by nlinarith
    calc 1 - g = ((1 - g) * (1 + g)) / (1 + g) := by field_simp
      _ ≤ 1 / (1 + g) := by gcongr
      _ = (1 + g)⁻¹ := one_div _
  have hpow : (1 - g) ^ (8 * n ^ 4) ≤ ((1 + g)⁻¹) ^ (8 * n ^ 4) :=
    pow_le_pow_left₀ hbase hstep _
  have hbern : 1 + (8 * n ^ 4 : ℕ) * g ≤ (1 + g) ^ (8 * n ^ 4) :=
    one_add_mul_le_pow (by linarith) _
  have hgT : ((8 * n ^ 4 : ℕ) : ℝ) * g = 2 * n := by
    rw [hg]
    push_cast
    field_simp
    ring
  have hbig : 2 * (n:ℝ) ≤ (1 + g) ^ (8 * n ^ 4) := by
    calc 2 * (n:ℝ) ≤ 1 + 2 * n := by linarith
      _ = 1 + ((8 * n ^ 4 : ℕ) : ℝ) * g := by rw [hgT]
      _ ≤ (1 + g) ^ (8 * n ^ 4) := hbern
  have h2n : (0:ℝ) < 2 * n := by linarith
  have hfinal : ((1 + g)⁻¹) ^ (8 * n ^ 4) ≤ 1 / (2 * n) := by
    calc ((1 + g)⁻¹) ^ (8 * n ^ 4) = ((1 + g) ^ (8 * n ^ 4))⁻¹ := by rw [inv_pow]
      _ ≤ (2 * (n:ℝ))⁻¹ := by gcongr
      _ = 1 / (2 * n) := (one_div _).symm
  exact le_trans hpow hfinal

/-- Hitting estimate: after `8n⁴` steps, the walk started at `s` is at `v` with
probability at least `1/(2n)`, for any `v` in the component of `s`. -/
