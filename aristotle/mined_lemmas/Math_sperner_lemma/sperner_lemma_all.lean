import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` lines to come first in a module, so the
required header block is placed immediately after the single `import Mathlib` line.
-/

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-! ### Codimension-one subsets -/

/-- Subsets of `S` of cardinality `S.card - 1` are exactly the sets `S.erase x` for `x ∈ S`;
hence counting them amounts to counting the vertices `x ∈ S` with the corresponding property. -/

theorem sperner_lemma_all {V : Type*} [DecidableEq V] [Fintype V]
    (n : ℕ) (color : V → ℕ) (T : ℕ → Finset (Finset V))
    (hcard : ∀ k ≤ n, ∀ S ∈ T k, S.card = k + 1)
    (hcolor : ∀ k ≤ n, ∀ S ∈ T k, S.image color ⊆ Finset.range (k + 1))
    (hbase : ∃ v, T 0 = {{v}} ∧ color v = 0)
    (hdoor : ∀ k, k + 1 ≤ n → ∀ G : Finset V, G.card = k + 1 →
      G.image color = Finset.range (k + 1) →
      ((T (k + 1)).filter (fun S => G ⊆ S)).card % 2 = if G ∈ T k then 1 else 0) :
    ∀ k ≤ n, ((T k).filter (fun S => S.image color = Finset.range (k + 1))).card % 2 = 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    obtain ⟨v, hTv, hcv⟩ := hbase
    rw [hTv]
    have hfe : ({{v}} : Finset (Finset V)).filter
        (fun S => S.image color = Finset.range 1) = {{v}} := by
      rw [Finset.filter_eq_self]
      intro S hS
      rw [Finset.mem_singleton] at hS
      subst hS
      ext y
      simp [hcv]
    rw [hfe, Finset.card_singleton]
  | succ k ih =>
    intro hkn
    have hk : k ≤ n := by omega
    -- `D` is the set of all rainbow `k`-faces ("doors")
    set D : Finset (Finset V) :=
      (Finset.univ : Finset (Finset V)).filter
        (fun G => G.card = k + 1 ∧ G.image color = Finset.range (k + 1)) with hD
    -- double counting of incidences between doors and `(k+1)`-cells
    have key : ∑ S ∈ T (k + 1), (D.filter (fun G => G ⊆ S)).card
        = ∑ G ∈ D, ((T (k + 1)).filter (fun S => G ⊆ S)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    -- each cell has an odd number of doors iff it is rainbow
    have step1 : ∀ S ∈ T (k + 1), (D.filter (fun G => G ⊆ S)).card % 2
        = if S.image color = Finset.range (k + 2) then 1 else 0 := by
      intro S hS
      have hDS : D.filter (fun G => G ⊆ S)
          = S.powerset.filter (fun G => G.card = k + 1 ∧
              G.image color = Finset.range (k + 1)) := by
        ext G
        simp only [hD, Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, true_and]
        tauto
      rw [hDS, card_filter_powerset_erase S (k + 1) (hcard (k + 1) hkn S hS),
        door_count color k S (hcard (k + 1) hkn S hS) (hcolor (k + 1) hkn S hS)]
    -- each door lies in an odd number of cells iff it is a `k`-cell of the `k`-th face
    have step2 : ∀ G ∈ D, ((T (k + 1)).filter (fun S => G ⊆ S)).card % 2
        = if G ∈ T k then 1 else 0 := by
      intro G hG
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hG
      exact hdoor k hkn G hG.1 hG.2
    have hDT : D.filter (fun G => G ∈ T k)
        = (T k).filter (fun S => S.image color = Finset.range (k + 1)) := by
      ext G
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hcard k hk G h1, h2⟩, h1⟩
    have hleft : (∑ S ∈ T (k + 1), (D.filter (fun G => G ⊆ S)).card) % 2
        = ((T (k + 1)).filter (fun S => S.image color = Finset.range (k + 2))).card % 2 := by
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl step1, ← Finset.card_filter]
    have hright : (∑ G ∈ D, ((T (k + 1)).filter (fun S => G ⊆ S)).card) % 2
        = ((T k).filter (fun S => S.image color = Finset.range (k + 1))).card % 2 := by
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl step2, ← Finset.card_filter, hDT]
    rw [← hleft, key, hright]
    exact ih hk

/--
**Sperner's Lemma**: every Sperner colouring of a triangulated `n`-simplex has an odd
number of rainbow cells.  See `Math.sperner_lemma_all` for the meaning of the hypotheses.
-/
