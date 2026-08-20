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

lemma nsq_Pv_le (hA : Sym A) (hn : 0 < n) {x : Fin n → ℝ} (hx : InW A s x) :
    nsq (Pv A x) ≤ (1 - 1 / (4 * (n:ℝ)^3)) ^ 2 * nsq x := by
  set M : ℝ := 1 - 1 / (4 * (n:ℝ)^3) with hM
  have hMnn : (0:ℝ) ≤ M := by
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hcube : (1:ℝ) ≤ (n:ℝ)^3 := one_le_pow₀ hn'
    have h4 : 1 / (4 * (n:ℝ)^3) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    simp only [hM]; linarith
  have hy : InW A s (Pv A x) := Pv_mem_W hA hn hx
  have hcs := cauchy_schwarz_Pv hA hn x (Pv A x)
  have h1 : ip (Pv A x) x ≤ M * nsq x := gap hA hn hx
  have h2 : ip (Pv A (Pv A x)) (Pv A x) ≤ M * nsq (Pv A x) := gap hA hn hy
  have hnn2 : 0 ≤ ip (Pv A (Pv A x)) (Pv A x) := Pv_psd hA hn (Pv A x)
  have hcs2 : (nsq (Pv A x))^2 ≤ (M * nsq x) * (M * nsq (Pv A x)) := by
    calc (nsq (Pv A x))^2 = (ip (Pv A x) (Pv A x))^2 := rfl
      _ ≤ ip (Pv A x) x * ip (Pv A (Pv A x)) (Pv A x) := hcs
      _ ≤ (M * nsq x) * (M * nsq (Pv A x)) := by
          apply mul_le_mul h1 h2 hnn2 (by nlinarith [nsq_nonneg x])
  rcases eq_or_lt_of_le (nsq_nonneg (Pv A x)) with h0 | hpos
  · rw [← h0]; exact mul_nonneg (sq_nonneg M) (nsq_nonneg x)
  · have := nsq_nonneg x
    nlinarith [hcs2, hpos]

