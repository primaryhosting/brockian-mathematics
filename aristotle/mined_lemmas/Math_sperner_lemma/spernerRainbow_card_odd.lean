import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Auxiliary counting lemmas -/

/-- Parity translated into `ZMod 2`. -/

theorem spernerRainbow_card_odd (k : ℕ) :
    ∀ J : Finset (Fin (n + 1)), J.card = k + 1 → Odd (spernerRainbow carrier T c J).card := by
  classical
  induction k with
  | zero =>
    intro J hJ
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hJ
    have hcount := hpm {i} ∅ hT0 (by simp) (by simp)
    rw [Finset.filter_true_of_mem (fun σ _ => Finset.empty_subset σ)] at hcount
    rw [if_neg (by simp)] at hcount
    have hrb : spernerRainbow carrier T c {i} = spernerCells carrier T {i} := by
      apply Finset.filter_true_of_mem
      intro σ hσ
      obtain ⟨-, hcard, hcar⟩ := Finset.mem_filter.mp hσ
      simp only [Finset.card_singleton] at hcard
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      have : c v = i := by
        have := hcar v (Finset.mem_singleton_self v) (hc v)
        simpa using this
      simp [this]
    rw [hrb, hcount]
    exact odd_one
  | succ k ih =>
    intro J hJ
    have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀⟩ := hJne
    set Cells := spernerCells carrier T J with hCells
    set Doors := spernerDoors carrier T c J i₀ with hDoors
    -- double counting of incident (cell, door) pairs
    have hdc : ∑ σ ∈ Cells, (Doors.filter (fun τ => τ ⊆ σ)).card
        = ∑ τ ∈ Doors, (Cells.filter (fun σ => τ ⊆ σ)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have hcast := congrArg (fun m : ℕ => (m : ZMod 2)) hdc
    simp only [Nat.cast_sum] at hcast
    -- left-hand side counts rainbow cells of `J`
    have hL : ∑ σ ∈ Cells, ((Doors.filter (fun τ => τ ⊆ σ)).card : ZMod 2)
        = ((spernerRainbow carrier T c J).card : ZMod 2) := by
      rw [Finset.sum_congr rfl (fun σ hσ =>
        spernerDoors_in_cell_card carrier T c hdown hc hi₀ hσ)]
      rw [spernerRainbow, Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun σ _ => by split <;> simp)
    -- right-hand side counts rainbow cells of `J \ {i₀}`
    have hsub : spernerRainbow carrier T c (J.erase i₀) ⊆ Doors := by
      intro τ hτ
      obtain ⟨hmc, himg⟩ := Finset.mem_filter.mp hτ
      obtain ⟨hτT, hcard, hcar⟩ := Finset.mem_filter.mp hmc
      refine Finset.mem_filter.mpr ⟨hτT, ?_, ?_, himg⟩
      · rw [hcard, Finset.card_erase_of_mem hi₀]
        have := Finset.card_pos.mpr ⟨i₀, hi₀⟩
        omega
      · intro v hv
        exact (hcar v hv).trans (Finset.erase_subset i₀ J)
    have hR : ∑ τ ∈ Doors, ((Cells.filter (fun σ => τ ⊆ σ)).card : ZMod 2)
        = ((spernerRainbow carrier T c (J.erase i₀)).card : ZMod 2) := by
      rw [Finset.sum_congr rfl (fun τ hτ =>
        spernerCells_over_door_card carrier T c hpm hc hi₀ hτ)]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr hsub]
      simp
    rw [odd_iff_cast_zmod_two]
    rw [← hL, hcast, hR, ← odd_iff_cast_zmod_two]
    exact ih (J.erase i₀) (by rw [Finset.card_erase_of_mem hi₀]; omega)

include hdown hT0 hpm hc in
/-- **Sperner's lemma.** Let `T` be a triangulation of the `n`-simplex, described
combinatorially: `T` is a finite simplicial complex on a vertex set `V` (closed under
passing to subfaces, and containing the empty face), each vertex `v` carries a nonempty
*carrier* `carrier v ⊆ Fin (n+1)` — the minimal face of the big simplex containing it —
and `T` satisfies the pseudomanifold condition `hpm`: inside each face `F J` of the big
simplex, every codimension-one face `τ` of the induced triangulation is contained in
exactly two full-dimensional cells of `F J` if it is interior to `F J` (that is, the
carriers of its vertices jointly cover `J`), and in exactly one otherwise.

Then for every *Sperner colouring* `c` — a colouring of the vertices with `c v ∈ carrier v`
— the number of rainbow cells, i.e. full-dimensional cells of the triangulation receiving
all `n + 1` colours, is odd. -/
