import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem dioph_fin {α : Type} {S : Set (α → ℕ)} (d : Dioph S) :
    ∃ (n : ℕ) (p : Poly (α ⊕ Fin n)), ∀ v, v ∈ S ↔ ∃ t : Fin n → ℕ, p (Sum.elim v t) = 0 := by
  classical
  obtain ⟨β, p, hp⟩ := d
  obtain ⟨s, hs⟩ := isPoly_support p.isPoly
  set s' : Finset β := s.preimage Sum.inr (Sum.inr_injective.injOn) with hs'
  set n : ℕ := s'.card with hn
  set e : {x // x ∈ s'} ≃ Fin n := s'.equivFin with he
  set idx : β → Fin (n + 1) := fun b => if h : b ∈ s' then (e ⟨b, h⟩).castSucc else Fin.last n
    with hidx
  refine ⟨n + 1, p.map (Sum.map id idx), fun v => (hp v).trans ?_⟩
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun j => if h : (j : ℕ) < n then t (e.symm ⟨(j : ℕ), h⟩) else 0, ?_⟩
    rw [Poly.map_apply]
    refine (hs _ _ ?_).trans ht
    rintro (a | b) hb
    · rfl
    · have hb' : b ∈ s' := by rw [hs']; simpa using hb
      have hib : idx b = (e ⟨b, hb'⟩).castSucc := by rw [hidx]; simp [hb']
      simp only [Function.comp_apply, Sum.map_inr, hib, Sum.elim_inr, Fin.val_castSucc]
      rw [dif_pos (e ⟨b, hb'⟩).isLt]
      congr 1
      have hcast : (⟨((e ⟨b, hb'⟩ : Fin n) : ℕ), (e ⟨b, hb'⟩).isLt⟩ : Fin n) = e ⟨b, hb'⟩ := rfl
      rw [hcast, Equiv.symm_apply_apply]
  · rintro ⟨u, hu⟩
    refine ⟨fun b => u (idx b), ?_⟩
    rw [Poly.map_apply] at hu
    refine Eq.trans ?_ hu
    congr 1
    funext x
    rcases x with a | b <;> rfl

end CS

import RequestProject.Davis

/-!
# The MRDP theorem

Building on Matiyasevich's theorem (`Dioph.pow_dioph`, in Mathlib) and on Davis' bounded
universal quantifier (`CS.forall_lt_dioph`), we show here that every partial recursive
function has a Diophantine graph, and hence that every recursively enumerable predicate is
Diophantine.
-/

open Dioph Nat Sum Vector3

namespace CS

/-! ### Gödel's β function -/

/-- Gödel's β function, used to code finite sequences by a pair of numbers. -/
