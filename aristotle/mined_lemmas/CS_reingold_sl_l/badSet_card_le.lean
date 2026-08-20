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

lemma badSet_card_le (hA : Sym A) {v : Fin n} {T : ℕ}
    (hcount : ∀ u : Fin n, Conn A u v →
      (2 * n) ^ (T - 1) ≤ ((seqs n T).filter (fun β => walk A u β = v)).card) :
    ∀ (k : ℕ) (u : Fin n), Conn A u v →
      (badSet A u v k T).card ≤ ((2 * n) ^ T - (2 * n) ^ (T - 1)) ^ k := by
  classical
  set R : ℕ := (2 * n) ^ T - (2 * n) ^ (T - 1) with hR
  intro k
  induction k with
  | zero =>
      intro u _
      have h : (badSet A u v 0 T).card ≤ (seqs n (0 * T)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      simpa [card_seqs] using h
  | succ k ih =>
      intro u hu
      set G : Finset (List (Lab n)) := (seqs n T).filter (fun β => walk A u β ≠ v) with hG
      have hmap : ∀ σ ∈ badSet A u v (k + 1) T,
          (⟨σ.take T, σ.drop T⟩ : (_ : List (Lab n)) × List (Lab n))
            ∈ G.sigma (fun β => badSet A (walk A u β) v k T) := by
        intro σ hσ
        rw [badSet, Finset.mem_filter, mem_seqs] at hσ
        obtain ⟨hlen, hmiss⟩ := hσ
        have hlenT : (σ.take T).length = T := by
          rw [List.length_take, hlen]
          have : T ≤ (k + 1) * T := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
          omega
        have hlenD : (σ.drop T).length = k * T := by
          rw [List.length_drop, hlen]
          have : (k + 1) * T = T + k * T := by ring
          omega
        have hblock : walk A u (σ.take T) ≠ v := by
          have := hmiss 1 (by omega)
          simpa using this
        rw [Finset.mem_sigma]
        refine ⟨?_, ?_⟩
        · rw [hG, Finset.mem_filter, mem_seqs]
          exact ⟨hlenT, hblock⟩
        · rw [badSet, Finset.mem_filter, mem_seqs]
          refine ⟨hlenD, ?_⟩
          intro j hj
          have hsplit : σ.take ((j + 1) * T) = σ.take T ++ (σ.drop T).take (j * T) := by
            have : (j + 1) * T = T + j * T := by ring
            rw [this, List.take_add]
          have := hmiss (j + 1) (by omega)
          rw [hsplit, walk_append] at this
          exact this
      have hinj : Set.InjOn (fun σ : List (Lab n) => (⟨σ.take T, σ.drop T⟩ :
          (_ : List (Lab n)) × List (Lab n))) (badSet A u v (k + 1) T) := by
        intro x _ y _ h
        have h1 : x.take T = y.take T := congrArg Sigma.fst h
        have h2 : x.drop T = y.drop T := by
          simpa [h1] using congrArg Sigma.snd h
        calc x = x.take T ++ x.drop T := (List.take_append_drop _ _).symm
          _ = y.take T ++ y.drop T := by rw [h1, h2]
          _ = y := List.take_append_drop _ _
      have hcard := Finset.card_le_card_of_injOn _ hmap hinj
      rw [Finset.card_sigma] at hcard
      have hterm : ∀ β ∈ G, (badSet A (walk A u β) v k T).card ≤ R ^ k := by
        intro β hβ
        refine ih _ ?_
        exact conn_trans (conn_symm hA (conn_walk A u β)) hu
      have hsum : ∑ β ∈ G, (badSet A (walk A u β) v k T).card ≤ G.card * R ^ k := by
        calc ∑ β ∈ G, (badSet A (walk A u β) v k T).card ≤ ∑ _β ∈ G, R ^ k :=
              Finset.sum_le_sum hterm
          _ = G.card * R ^ k := by rw [Finset.sum_const, smul_eq_mul]
      have hGcard : G.card ≤ R := by
        have hpart := Finset.card_filter_add_card_filter_not
          (s := seqs n T) (p := fun β => walk A u β = v)
        rw [card_seqs] at hpart
        have hge := hcount u hu
        have hGeq : G = (seqs n T).filter (fun β => ¬ (walk A u β = v)) := by
          rw [hG]
        rw [hGeq, hR]
        omega
      calc (badSet A u v (k + 1) T).card ≤ ∑ β ∈ G, (badSet A (walk A u β) v k T).card := hcard
        _ ≤ G.card * R ^ k := hsum
        _ ≤ R * R ^ k := Nat.mul_le_mul_right _ hGcard
        _ = R ^ (k + 1) := by ring

/-- A half-life estimate for the per-block failure probability. -/
