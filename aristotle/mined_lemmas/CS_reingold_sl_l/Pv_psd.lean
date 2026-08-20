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

lemma Pv_psd (hA : Sym A) (hn : 0 < n) (x : Fin n → ℝ) : 0 ≤ ip (Pv A x) x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hsplit : ∀ u : Fin n, (∑ a : Lab n, x (step A u a))
      = (n : ℝ) * x u + ∑ i : Fin n, x (step A u (true, i)) := by
    intro u
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    have hfalse : ∑ i : Fin n, x (step A u (false, i)) = (n : ℝ) * x u := by
      simp [step, Finset.sum_const]
    rw [hfalse]; ring
  set S : ℝ := ∑ u : Fin n, (∑ i : Fin n, x (step A u (true, i))) * x u with hS
  have hcs : |S| ≤ (n : ℝ) * nsq x := by
    have h1 : S = ∑ p : Fin n × Fin n, x (step A p.1 (true, p.2)) * x p.1 := by
      rw [hS, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_mul]
    have hlazy : ∑ u : Fin n, ∑ _i : Fin n, (x (step A u (false, _i))) ^ 2
        = (n : ℝ) * nsq x := by
      have h : ∀ u : Fin n, ∑ _i : Fin n, (x (step A u (false, _i))) ^ 2 = (n : ℝ) * (x u) ^ 2 := by
        intro u
        simp [step, Finset.sum_const]
      rw [Finset.sum_congr rfl (fun u _ => h u), ← Finset.mul_sum]
      unfold nsq ip
      congr 1
      exact Finset.sum_congr rfl fun u _ => by ring
    have hsplit2 : ∑ u : Fin n, ∑ a : Lab n, (x (step A u a)) ^ 2
        = (∑ u : Fin n, ∑ i : Fin n, (x (step A u (false, i))) ^ 2)
          + ∑ u : Fin n, ∑ i : Fin n, (x (step A u (true, i))) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      ring
    have hsq1 : ∑ p : Fin n × Fin n, (x (step A p.1 (true, p.2))) ^ 2 = (n : ℝ) * nsq x := by
      rw [Fintype.sum_prod_type]
      have hall := sum_sq_step hA x
      rw [hsplit2, hlazy] at hall
      linarith
    have hsq2 : ∑ p : Fin n × Fin n, (x p.1) ^ 2 = (n : ℝ) * nsq x := by
      rw [Fintype.sum_prod_type]
      have h : ∀ u : Fin n, ∑ _i : Fin n, (x u) ^ 2 = (n : ℝ) * (x u) ^ 2 := by
        intro u; simp [Finset.sum_const]
      rw [Finset.sum_congr rfl (fun u _ => h u), ← Finset.mul_sum]
      unfold nsq ip
      congr 1
      exact Finset.sum_congr rfl fun u _ => by ring
    have hcs' := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin n × Fin n))
      (fun p => x (step A p.1 (true, p.2))) (fun p => x p.1)
    rw [← h1] at hcs'
    rw [hsq1, hsq2] at hcs'
    have hnn : 0 ≤ (n : ℝ) * nsq x := mul_nonneg (le_of_lt hn') (nsq_nonneg x)
    nlinarith [abs_nonneg S, sq_abs S]
  have hip : ip (Pv A x) x = ((n : ℝ) * nsq x + S) / (2 * n) := by
    have hterm : ∀ u : Fin n, (∑ a : Lab n, x (step A u a)) / (2 * n) * x u
        = ((n : ℝ) * (x u * x u) + (∑ i : Fin n, x (step A u (true, i))) * x u) / (2 * n) := by
      intro u
      rw [hsplit u]
      ring
    unfold ip Pv
    rw [Finset.sum_congr rfl (fun u _ => hterm u), ← Finset.sum_div]
    congr 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hS]
    rfl
  rw [hip]
  have hSle : -((n : ℝ) * nsq x) ≤ S := neg_le_of_abs_le hcs
  have h2n : (0:ℝ) < 2 * n := by linarith
  apply div_nonneg _ (le_of_lt h2n)
  linarith

end CS

/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Reingold.Operator

/-!
The spectral gap of the lazy walk on a connected component, and the resulting
contraction estimate for the iterated transition operator.
-/

namespace CS

open Finset

open scoped Classical

variable {n : ℕ} {A : Fin n → Fin n → Bool} {s : Fin n}

/-- The connected component of `s`. -/
