import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS
namespace IS

/-!
## The reachability sets of a finite digraph

Throughout, the digraph has vertex set `{0, 1, ..., N-1} ⊆ ℕ` and edge relation `adj`.
`R N adj s i` is the set of vertices reachable from `s` using at most `i` edges.
-/

/-- The edge relation of the digraph on vertex set `{0,...,N-1}`. -/

theorem reach_inner (hs : s < N) {t i c v k : ℕ}
    (hc : c = (R N adj s (i - 1)).card)
    (hcheck : ∀ w ∈ R N adj s (i - 1), w ≠ v ∧ adj w v = false) :
    ∀ n lb d, ((R N adj s (i - 1)).filter (fun x => lb ≤ x)).card = n → d + n = c →
      ∃ lb', Relation.ReflTransGen (Step N adj s t)
        (.inner i c v k d lb) (.inner i c v k c lb') := by
  intro n
  induction n with
  | zero => intro lb d _ hdn; exact ⟨lb, by rw [show d = c by omega]⟩
  | succ n ih =>
      intro lb d hfilter hdn
      have hne : ((R N adj s (i - 1)).filter (fun x => lb ≤ x)).Nonempty := by
        rw [← Finset.card_pos, hfilter]; omega
      set u := ((R N adj s (i - 1)).filter (fun x => lb ≤ x)).min' hne with hu_def
      have humem := Finset.min'_mem _ hne
      rw [← hu_def] at humem
      simp only [Finset.mem_filter] at humem
      obtain ⟨huR, hlbu⟩ := humem
      have huN : u < N := by simpa using R_subset_range hs (i - 1) huR
      have hstep1 : Step N adj s t (.inner i c v k d lb) (.pathB i c v k d u s 0) :=
        Step.startB (by omega) hlbu huN
      obtain ⟨l', hl', hreach⟩ := reach_pathB (t := t) (i := i) (c := c) (v := v) (k := k)
        (d := d) (u := u)
        (i - 1) (by omega) u huR
      obtain ⟨hne_uv, hadj_uv⟩ := hcheck u huR
      have hstep2 : Step N adj s t (.pathB i c v k d u u l') (.inner i c v k (d + 1) (u + 1)) :=
        Step.doneB rfl hne_uv hadj_uv
      have hsplit : ((R N adj s (i - 1)).filter (fun x => lb ≤ x)) =
          insert u ((R N adj s (i - 1)).filter (fun x => u + 1 ≤ x)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hx, hlx⟩
          have hxu : u ≤ x := Finset.min'_le _ x (by simp only [Finset.mem_filter]; exact ⟨hx, hlx⟩)
          rcases Nat.eq_or_lt_of_le hxu with h | h
          · exact Or.inl h.symm
          · exact Or.inr ⟨hx, by omega⟩
        · rintro (rfl | ⟨hx, hlx⟩)
          · exact ⟨huR, hlbu⟩
          · exact ⟨hx, by omega⟩
      have hcard : ((R N adj s (i - 1)).filter (fun x => u + 1 ≤ x)).card = n := by
        have hnot : u ∉ ((R N adj s (i - 1)).filter (fun x => u + 1 ≤ x)) := by
          simp only [Finset.mem_filter]
          omega
        rw [hsplit, Finset.card_insert_of_notMem hnot] at hfilter
        omega
      obtain ⟨lb', hrest⟩ := ih (u + 1) (d + 1) hcard (by omega)
      exact ⟨lb', ((Relation.ReflTransGen.single hstep1).trans hreach).tail hstep2 |>.trans hrest⟩

/-- The outer loop of round `i` scans all vertices, counting those in `R i`. -/
