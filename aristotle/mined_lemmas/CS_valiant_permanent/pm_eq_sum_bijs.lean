import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace CS

/-! ## A recursive description of the permanent

`pm M l C` is the weighted count of bijections from the rows listed in `l` onto the
column set `C`, where the weight of a bijection is the product of the corresponding
matrix entries.  It is a convenient recursive handle on the permanent. -/

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommSemiring R]

/-- Weighted count of the bijections from the rows in the list `l` onto the columns in `C`. -/

theorem pm_eq_sum_bijs (M : ι → ι → R) :
    ∀ (l : List ι), l.Nodup → ∀ (C : Finset ι), C.card = l.length →
      pm M l C = ∑ f ∈ bijs l C, (l.map (fun r => M r (f r))).prod := by
  intro l
  induction l with
  | nil =>
      intro _ C hcard
      have hC : C = ∅ := Finset.card_eq_zero.mp (by simpa using hcard)
      subst hC
      have : bijs ([] : List ι) (∅ : Finset ι) = {id} := by
        ext f
        simp only [mem_bijs, Finset.mem_singleton, not_false_eq_true,
          forall_const, List.mem_nil_iff, IsEmpty.forall_iff, implies_true, and_true]
        constructor
        · intro h; funext x; exact h x
        · rintro rfl x; rfl
      rw [this]
      simp
  | cons r rs ih =>
      intro hnd C hcard
      have hr : r ∉ rs := (List.nodup_cons.mp hnd).1
      have hnd' : rs.Nodup := (List.nodup_cons.mp hnd).2
      have hne : ∀ x, x ∈ rs → x ≠ r := by
        intro x hx h
        subst h
        exact hr hx
      rw [pm_cons]
      have step : ∀ c ∈ C, M r c * pm M rs (C.erase c)
          = ∑ g ∈ bijs rs (C.erase c), M r c * (rs.map (fun x => M x (g x))).prod := by
        intro c hc
        have hcard' : (C.erase c).card = rs.length := by
          rw [Finset.card_erase_of_mem hc, hcard]
          simp
        rw [ih hnd' (C.erase c) hcard', Finset.mul_sum]
      rw [Finset.sum_congr rfl step, Finset.sum_sigma']
      refine Finset.sum_nbij' (i := fun p => Function.update p.2 r p.1)
        (j := fun f => (⟨f r, Function.update f r r⟩ : (_ : ι) × (ι → ι))) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨c, g⟩ hp
        simp only [Finset.mem_sigma, mem_bijs] at hp ⊢
        obtain ⟨hc, hfix, hinj, hmaps⟩ := hp
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          have hxr : x ≠ r := fun h => hx (by simp [h])
          rw [Function.update_of_ne hxr]
          exact hfix x (fun h => hx (List.mem_cons_of_mem _ h))
        · intro x hx y hy hxy
          rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
          · rfl
          · exfalso
            rw [Function.update_self, Function.update_of_ne (hne y hy')] at hxy
            exact (Finset.mem_erase.mp (hmaps y hy')).1 hxy.symm
          · exfalso
            rw [Function.update_self, Function.update_of_ne (hne x hx')] at hxy
            exact (Finset.mem_erase.mp (hmaps x hx')).1 hxy
          · rw [Function.update_of_ne (hne x hx'),
              Function.update_of_ne (hne y hy')] at hxy
            exact hinj x hx' y hy' hxy
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · rwa [Function.update_self]
          · rw [Function.update_of_ne (hne x hx')]
            exact Finset.mem_of_mem_erase (hmaps x hx')
      · intro f hf
        simp only [Finset.mem_sigma, mem_bijs] at hf ⊢
        obtain ⟨hfix, hinj, hmaps⟩ := hf
        refine ⟨hmaps r List.mem_cons_self, ?_, ?_, ?_⟩
        · intro x hx
          by_cases hxr : x = r
          · subst hxr; rw [Function.update_self]
          · rw [Function.update_of_ne hxr]
            exact hfix x (by simp [List.mem_cons, hxr, hx])
        · intro x hx y hy hxy
          rw [Function.update_of_ne (hne x hx),
            Function.update_of_ne (hne y hy)] at hxy
          exact hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy
        · intro x hx
          rw [Function.update_of_ne (hne x hx)]
          refine Finset.mem_erase.mpr ⟨?_, hmaps x (List.mem_cons_of_mem _ hx)⟩
          intro hcon
          exact hr (hinj x (List.mem_cons_of_mem _ hx) r List.mem_cons_self hcon ▸ hx)
      · rintro ⟨c, g⟩ hp
        simp only [Finset.mem_sigma, mem_bijs] at hp
        obtain ⟨hc, hfix, hinj, hmaps⟩ := hp
        have hgr : g r = r := hfix r hr
        simp only [Function.update_self, Sigma.mk.injEq, heq_eq_eq, true_and]
        rw [Function.update_idem]
        funext x
        by_cases hx : x = r
        · subst hx; simp [hgr]
        · simp [Function.update_of_ne hx]
      · intro f hf
        simp only [mem_bijs] at hf
        simp only [Function.update_idem, Function.update_eq_self]
      · rintro ⟨c, g⟩ hp
        simp only [Finset.mem_sigma, mem_bijs] at hp
        obtain ⟨hc, hfix, hinj, hmaps⟩ := hp
        simp only [List.map_cons, List.prod_cons, Function.update_self]
        congr 1
        refine congrArg List.prod (List.map_congr_left ?_)
        intro x hx
        rw [Function.update_of_ne (hne x hx)]

