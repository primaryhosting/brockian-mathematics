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

theorem exists_uts (hn : 0 < n) :
    ∃ σ : List (Lab n), σ.length = utsLen n ∧ IsUTS σ := by
  classical
  set T : ℕ := blockLen n with hTdef
  set k : ℕ := numBlocks n with hkdef
  set R : ℕ := (2 * n) ^ T - (2 * n) ^ (T - 1) with hR
  set Tri : Finset ((Fin n → Fin n → Bool) × Fin n × Fin n) :=
    univ.filter (fun p => Sym p.1 ∧ Conn p.1 p.2.1 p.2.2) with hTri
  set Bad : ((Fin n → Fin n → Bool) × Fin n × Fin n) → Finset (List (Lab n)) :=
    fun p => badSet p.1 p.2.1 p.2.2 k T with hBad
  have hbadle : ∀ p ∈ Tri, (Bad p).card ≤ R ^ k := by
    intro p hp
    rw [hTri, Finset.mem_filter] at hp
    obtain ⟨-, hsym, hconn⟩ := hp
    refine badSet_card_le hsym ?_ k p.2.1 hconn
    intro u hu
    rw [hTdef, blockLen]
    exact hit_count hsym hn hu
  have hTricard : Tri.card ≤ 2 ^ (n * n) * n * n := by
    have h1 : Tri.card ≤ Fintype.card ((Fin n → Fin n → Bool) × Fin n × Fin n) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_univ Tri
    have hcardfun : Fintype.card (Fin n → Fin n → Bool) = 2 ^ (n * n) := by
      rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul]
    have h2 : Fintype.card ((Fin n → Fin n → Bool) × Fin n × Fin n) = 2 ^ (n * n) * n * n := by
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, hcardfun, mul_assoc]
    omega
  have hunion : (Tri.biUnion Bad).card < (seqs n (utsLen n)).card := by
    have h1 : (Tri.biUnion Bad).card ≤ ∑ p ∈ Tri, (Bad p).card := Finset.card_biUnion_le
    have h2 : ∑ p ∈ Tri, (Bad p).card ≤ Tri.card * R ^ k := by
      calc ∑ p ∈ Tri, (Bad p).card ≤ ∑ _p ∈ Tri, R ^ k := Finset.sum_le_sum hbadle
        _ = Tri.card * R ^ k := by rw [Finset.sum_const, smul_eq_mul]
    have h3 : Tri.card * R ^ k ≤ 2 ^ (n * n) * n * n * R ^ k :=
      Nat.mul_le_mul_right _ hTricard
    have h4 : 2 ^ (n * n) * n * n * R ^ k < (2 * n) ^ utsLen n := by
      rw [hR, hTdef, hkdef]
      exact uts_counting hn
    rw [card_seqs]
    omega
  obtain ⟨σ, hσmem, hσbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hunion
  refine ⟨σ, mem_seqs.1 hσmem, ?_⟩
  intro A hA s v hconn
  have hp : ((A, s, v) : (Fin n → Fin n → Bool) × Fin n × Fin n) ∈ Tri := by
    rw [hTri, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hA, hconn⟩
  have hnot : σ ∉ Bad (A, s, v) := fun h => hσbad (Finset.mem_biUnion.2 ⟨_, hp, h⟩)
  rw [hBad] at hnot
  simp only [badSet, Finset.mem_filter, mem_seqs, not_and, not_forall] at hnot
  have hlen : σ.length = k * T := by
    rw [mem_seqs.1 hσmem]
    rfl
  obtain ⟨j, hj⟩ := hnot hlen
  obtain ⟨hjk, hjv⟩ := hj
  refine ⟨j * T, ?_, not_not.1 hjv⟩
  rw [hlen]
  exact Nat.mul_le_mul_right _ hjk

end CS

/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
Basic setup: undirected graphs given by a symmetric adjacency predicate on `Fin n`,
the associated lazy `2n`-regular walk given by a rotation map, connectivity, label
sequences, and the space-bounded machine model.
-/

namespace CS

open Finset

/-- Labels for the lazy walk on an `n`-vertex graph: `(false, i)` is a lazy step
(stay put), `(true, i)` is an attempt to move to vertex `i`. -/
abbrev Lab (n : ℕ) : Type := Bool × Fin n

variable {n : ℕ}

/-- Symmetry of an adjacency predicate. -/
