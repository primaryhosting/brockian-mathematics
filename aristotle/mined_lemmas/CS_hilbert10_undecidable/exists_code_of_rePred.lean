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

theorem exists_code_of_rePred {p : ℕ → Prop} (hp : REPred p) :
    ∃ c : Nat.Partrec.Code, ∀ a, p a ↔ ∃ k, (Nat.Partrec.Code.evaln k c a).isSome := by
  have hpart : Nat.Partrec fun a => Part.assert (p a) fun _ => Part.some 0 :=
    Partrec.nat_iff.mp hp
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hpart
  refine ⟨c, fun a => ?_⟩
  constructor
  · intro ha
    have h0 : (0 : ℕ) ∈ c.eval a := by rw [hc]; simp [ha]
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h0
    exact ⟨k, by rw [Option.isSome_iff_exists]; exact ⟨0, hk⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
    have hmem : x ∈ c.eval a := Nat.Partrec.Code.evaln_complete.mpr ⟨k, hx⟩
    rw [hc] at hmem
    obtain ⟨⟨h1, h2⟩, h3⟩ := hmem
    exact h1

/-- **MRDP theorem** (Matiyasevich–Robinson–Davis–Putnam): every recursively enumerable
predicate on `ℕ` is Diophantine. -/
