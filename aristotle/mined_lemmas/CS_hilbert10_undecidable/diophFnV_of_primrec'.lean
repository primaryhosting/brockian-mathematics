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

theorem diophFnV_of_primrec' {n : ℕ} {f : List.Vector ℕ n → ℕ} (hf : Nat.Primrec' f) :
    DiophFnV f := by
  induction hf with
  | zero => exact Dioph.const_dioph 0
  | succ =>
      have h : DiophFn (fun v : Vector3 ℕ 1 => v Fin2.fz + 1) :=
        Dioph.add_dioph (Dioph.proj_dioph _) (Dioph.const_dioph 1)
      refine cast (congrArg DiophFn ?_) h
      funext v
      simp
  | get i =>
      have h : DiophFn (fun v : Vector3 ℕ _ => v (Fin2.ofFin i)) := Dioph.proj_dioph _
      refine cast (congrArg DiophFn ?_) h
      funext v
      simp
  | @comp m n f g _ _ hf hg =>
      have hall : VectorAllP DiophFn
          (fun (i : Fin2 n) (a : Vector3 ℕ m) => g (Fin2.toFin i) (toLV a)) :=
        (vectorAllP_iff_forall _ _).2 (fun i => hg (Fin2.toFin i))
      have h := Dioph.diophFn_comp hf
        (fun (i : Fin2 n) (a : Vector3 ℕ m) => g (Fin2.toFin i) (toLV a)) hall
      refine cast (congrArg DiophFn ?_) h
      funext a
      exact congrArg f (toLV_ofFn (fun j : Fin n => g j (toLV a)))
  | @prec n f g _ _ hf hg =>
      have h := precFn_dioph hf hg
      refine cast (congrArg DiophFn ?_) h
      funext v
      rw [precFn_eq]
      show _ = Nat.rec (motive := fun _ => ℕ) (f (toLV v).tail)
        (fun y IH => g (y ::ᵥ IH ::ᵥ (toLV v).tail)) ((toLV v).head)
      simp

/-! ### The MRDP theorem -/

/-- A recursively enumerable predicate is the domain of the evaluation of a code, hence is
described by the step-bounded evaluation function `evaln`. -/
