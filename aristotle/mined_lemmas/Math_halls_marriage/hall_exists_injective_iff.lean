import Mathlib
/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A self-contained development of Hall's marriage theorem.

* `Math.hall_exists_injective_iff` : the combinatorial ("system of distinct representatives")
  form, proved from scratch by induction (it does *not* use Mathlib's Hall theorem).
* `Math.halls_marriage` : a bipartite graph has a perfect matching iff Hall's condition holds.
-/

namespace Math

open Finset

section Core

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in

theorem hall_exists_injective_iff [Fintype ι] (t : ι → Finset α) :
    (∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ t i) ↔
      ∀ s : Finset ι, s.card ≤ (s.biUnion t).card := by
  constructor
  · rintro ⟨f, hf, hmem⟩ s
    calc s.card = (s.image f).card := (Finset.card_image_of_injective s hf).symm
      _ ≤ (s.biUnion t).card := by
          refine Finset.card_le_card fun y hy => ?_
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
          exact Finset.mem_biUnion.mpr ⟨i, hi, hmem i⟩
  · intro hall
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨fun i => (IsEmpty.false i).elim, fun a => (IsEmpty.false a).elim,
        fun i => (IsEmpty.false i).elim⟩
    · have hαne : Nonempty α := by
        obtain ⟨i⟩ := hι
        have h1 := hall {i}
        rw [Finset.card_singleton, Finset.singleton_biUnion] at h1
        obtain ⟨x, _⟩ := Finset.card_pos.mp (show 0 < (t i).card by omega)
        exact ⟨x⟩
      obtain ⟨f, hinj, hmem⟩ :=
        hall_aux (Fintype.card ι) t Finset.univ (by simp) (fun u _ => hall u)
      exact ⟨f, fun a b hab => hinj (by simp) (by simp) hab, fun i => hmem i (Finset.mem_univ i)⟩

end Core

section Graph

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B : Set V}

omit [DecidableEq V] in
/-- A graph admitting a perfect matching satisfies Hall's condition. -/
