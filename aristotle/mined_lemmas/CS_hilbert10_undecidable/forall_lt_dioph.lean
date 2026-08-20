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

theorem forall_lt_dioph {S : Set (Option α → ℕ)} {f : (α → ℕ) → ℕ}
    (d : Dioph S) (df : DiophFn f) :
    Dioph {v : α → ℕ | ∀ x < f v, Option.elim' x v ∈ S} := by
  classical
  obtain ⟨n, p, hp⟩ := dioph_fin d
  obtain ⟨q, hq0, hqp, hqm⟩ := exists_majorant p
  set sg : Option α ⊕ Fin n → α ⊕ davisIdx n :=
    Sum.elim (Option.elim' (Sum.inr none) Sum.inl) (fun _ => Sum.inr (some none)) with hsg
  set tu : Option α ⊕ Fin n → α ⊕ davisIdx n :=
    Sum.elim (Option.elim' (Sum.inr (some (some none))) Sum.inl)
      (fun i => Sum.inr (some (some (some i)))) with htu
  -- the basic Diophantine functions of the extended variable vector
  have dY : DiophFn (fun w : α ⊕ davisIdx n → ℕ => w (Sum.inr none)) :=
    Dioph.proj_dioph _
  have dU : DiophFn (fun w : α ⊕ davisIdx n → ℕ => w (Sum.inr (some none))) :=
    Dioph.proj_dioph _
  have dK : DiophFn (fun w : α ⊕ davisIdx n → ℕ => w (Sum.inr (some (some none)))) :=
    Dioph.proj_dioph _
  have dA : ∀ i : Fin n,
      DiophFn (fun w : α ⊕ davisIdx n → ℕ => w (Sum.inr (some (some (some i))))) :=
    fun i => Dioph.proj_dioph _
  have dF : DiophFn (fun w : α ⊕ davisIdx n → ℕ => f (fun a => w (Sum.inl a))) :=
    Dioph.reindex_diophFn Sum.inl df
  -- the bound `B`, the modulus base `b` and the product of moduli are Diophantine
  have hqmap : ∀ w : α ⊕ davisIdx n → ℕ,
      (q.map sg) w = q (Sum.elim (Option.elim' (w (Sum.inr none)) (fun a => w (Sum.inl a)))
        (fun _ => w (Sum.inr (some none)))) := by
    intro w
    rw [Poly.map_apply]
    congr 1
    funext x
    rcases x with (c | i)
    · rcases c with _ | c <;> rfl
    · rfl
  have dB : DiophFn (fun w : α ⊕ davisIdx n → ℕ =>
      davisB q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none)))) := by
    have h1 : DiophFn (fun w : α ⊕ davisIdx n → ℕ => ((q.map sg) w).natAbs) :=
      Dioph.abs_poly_dioph _
    have heq : (fun w : α ⊕ davisIdx n → ℕ =>
        davisB q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none))))
        = fun w => ((q.map sg) w).natAbs + w (Sum.inr none)
            + w (Sum.inr (some none)) + 1 := by
      funext w
      rw [davisB, hqmap w]
    rw [heq]
    exact Dioph.add_dioph (Dioph.add_dioph (Dioph.add_dioph h1 dY) dU) (Dioph.const_dioph 1)
  have db : DiophFn (fun w : α ⊕ davisIdx n → ℕ =>
      davisb q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none)))) :=
    factorial_dioph dB
  have dP : DiophFn (fun w : α ⊕ davisIdx n → ℕ =>
      davisP q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none)))) :=
    progProd_dioph dY db (fun w => davisb_pos _ _ _ _)
  -- the three divisibility conditions are Diophantine
  have dC1 : Dioph {w : α ⊕ davisIdx n → ℕ |
      davisP q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none))) ∣
        davisb q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none)))
          * w (Sum.inr (some (some none)))
        + davisb q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none)))
        + 1} :=
    Dioph.dvd_dioph dP (Dioph.add_dioph (Dioph.add_dioph (Dioph.mul_dioph db dK) db)
      (Dioph.const_dioph 1))
  have dC2 : Dioph {w : α ⊕ davisIdx n → ℕ | ∀ i : Fin n,
      davisP q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none))) ∣
        (w (Sum.inr (some (some (some i))))).descFactorial (w (Sum.inr (some none)) + 1)} := by
    refine dioph_forall_fin n _ (fun i => ?_)
    have hd : DiophFn (fun w : α ⊕ davisIdx n → ℕ =>
        (w (Sum.inr (some (some (some i))))).descFactorial (w (Sum.inr (some none)) + 1)) := by
      have heq : (fun w : α ⊕ davisIdx n → ℕ =>
          (w (Sum.inr (some (some (some i))))).descFactorial (w (Sum.inr (some none)) + 1))
          = fun w => (w (Sum.inr (some none)) + 1)! *
              (w (Sum.inr (some (some (some i))))).choose (w (Sum.inr (some none)) + 1) := by
        funext w
        exact Nat.descFactorial_eq_factorial_mul_choose _ _
      rw [heq]
      exact Dioph.mul_dioph (factorial_dioph (Dioph.add_dioph dU (Dioph.const_dioph 1)))
        (choose_dioph (dA i) (Dioph.add_dioph dU (Dioph.const_dioph 1)))
    exact Dioph.dvd_dioph dP hd
  have hpmap : ∀ w : α ⊕ davisIdx n → ℕ,
      (p.map tu) w
        = p (Sum.elim (Option.elim' (w (Sum.inr (some (some none)))) (fun a => w (Sum.inl a)))
          (fun i => w (Sum.inr (some (some (some i)))))) := by
    intro w
    rw [Poly.map_apply]
    congr 1
    funext x
    rcases x with (c | i)
    · rcases c with _ | c <;> simp [htu]
    · simp [htu]
  have dC3 : Dioph {w : α ⊕ davisIdx n → ℕ |
      davisP q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none))) ∣
        (p (Sum.elim (Option.elim' (w (Sum.inr (some (some none)))) (fun a => w (Sum.inl a)))
          (fun i => w (Sum.inr (some (some (some i))))))).natAbs} := by
    have h1 : DiophFn (fun w : α ⊕ davisIdx n → ℕ => ((p.map tu) w).natAbs) :=
      Dioph.abs_poly_dioph _
    have heq : (fun w : α ⊕ davisIdx n → ℕ => ((p.map tu) w).natAbs)
        = fun w =>
            (p (Sum.elim (Option.elim' (w (Sum.inr (some (some none))))
              (fun a => w (Sum.inl a))) (fun i => w (Sum.inr (some (some (some i))))))).natAbs := by
      funext w; rw [hpmap w]
    rw [heq] at h1
    exact Dioph.dvd_dioph dP h1
  have dCond : Dioph {w : α ⊕ davisIdx n → ℕ |
      davisCond p q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none)))
        (w (Sum.inr (some (some none)))) (fun i => w (Sum.inr (some (some (some i)))))} :=
    Dioph.ext ((dC1.inter dC2).inter dC3) (fun w => by
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, davisCond]
      tauto)
  have dC0 : Dioph {w : α ⊕ davisIdx n → ℕ |
      w (Sum.inr none) = f (fun a => w (Sum.inl a))} := Dioph.eq_dioph dY dF
  -- assemble
  refine Dioph.ext (Dioph.ex_dioph (dC0.inter dCond)) fun v => ?_
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨x, hC0, hCond⟩
    have hy : x none = f v := hC0
    intro k hk
    refine (hp _).2 (davis_of_cond p q hq0 hqp hqm v (x none) _ _ _ hCond k ?_)
    rw [hy]; exact hk
  · intro h
    have h' : ∀ k < f v, ∃ t : Fin n → ℕ, p (Sum.elim (Option.elim' k v) t) = 0 :=
      fun k hk => (hp _).1 (h k hk)
    obtain ⟨u, K, a, hCond⟩ := cond_of_davis p q v (f v) h'
    exact ⟨Option.elim' (f v) (Option.elim' u (Option.elim' K a)), rfl, hCond⟩

end CS

import RequestProject.MRDP

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Sum Nat MvPolynomial

namespace CS

/-! ### An undecidable recursively enumerable predicate on `ℕ` -/

/-- The halting problem transported to `ℕ` along the standard enumeration of codes. -/
