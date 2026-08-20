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

lemma hit_prob (hA : Sym A) (hn : 0 < n) {v : Fin n} (hv : Conn A s v) :
    1 / (2 * (n:ℝ)) ≤ Pit A (8 * n ^ 4) (delta v) s := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set c : ℝ := ((comp A s).card : ℝ) with hcdef
  have hcpos : (0:ℝ) < c := by rw [hcdef]; exact_mod_cast comp_card_pos A s
  have hcle : c ≤ (n:ℝ) := by
    rw [hcdef]
    have : (comp A s).card ≤ n := by
      simpa using Finset.card_le_univ (comp A s)
    exact_mod_cast this
  set f : Fin n → ℝ := delta v - c⁻¹ • indC A s with hf
  have hfW : InW A s f := centred_mem_W hv
  have hdecomp : delta v = f + c⁻¹ • indC A s := by
    rw [hf]; abel
  have hind : indC A s s = 1 := by simp [indC, conn_refl A s]
  have hPit : Pit A (8 * n ^ 4) (delta v) s = Pit A (8 * n ^ 4) f s + c⁻¹ := by
    rw [hdecomp, Pit_add, Pit_smul, Pit_indC hA hn]
    simp [hind]
  set lam : ℝ := 1 - 1 / (4 * (n:ℝ)^3) with hlam
  have hlam0 : (0:ℝ) ≤ lam := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hcube : (1:ℝ) ≤ (n:ℝ)^3 := one_le_pow₀ hn1
    rw [hlam]
    have : 1 / (4 * (n:ℝ)^3) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  have hnsq : nsq (Pit A (8 * n ^ 4) f) ≤ (lam ^ (8 * n ^ 4)) ^ 2 := by
    have h1 := nsq_Pit_le (s := s) hA hn hfW (8 * n ^ 4)
    have h2 : nsq f ≤ 1 := nsq_centred_le_one hv
    have h3 : (0:ℝ) ≤ (lam ^ (8 * n ^ 4)) ^ 2 := by positivity
    nlinarith [nsq_nonneg f]
  have hsq : (Pit A (8 * n ^ 4) f s) ^ 2 ≤ (lam ^ (8 * n ^ 4)) ^ 2 :=
    le_trans (sq_le_nsq _ s) hnsq
  have hlamT0 : (0:ℝ) ≤ lam ^ (8 * n ^ 4) := pow_nonneg hlam0 _
  have hlamT : lam ^ (8 * n ^ 4) ≤ 1 / (2 * n) := lambda_pow_le hn
  have hlow : -(1 / (2 * (n:ℝ))) ≤ Pit A (8 * n ^ 4) f s := by
    nlinarith [hsq, hlamT0, hlamT]
  have hinv : 1 / (n:ℝ) ≤ c⁻¹ := by
    rw [one_div, inv_le_inv₀ hn' hcpos]
    exact hcle
  have hhalf : 1 / (2 * (n:ℝ)) + 1 / (2 * (n:ℝ)) = 1 / (n:ℝ) := by
    field_simp
    ring
  rw [hPit]
  linarith

/-- Counting version of the walk distribution: the number of label sequences of length
`T` driving the walk from `u` to `v` is `(2n)^T` times the corresponding entry of the
`T`-th power of the transition operator. -/
