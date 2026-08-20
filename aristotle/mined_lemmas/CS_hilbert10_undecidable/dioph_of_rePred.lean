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

theorem dioph_of_rePred (p : ℕ → Prop) (hp : REPred p) :
    Dioph {v : Fin2 1 → ℕ | p (v Fin2.fz)} := by
  obtain ⟨c, hc⟩ := exists_code_of_rePred hp
  set F : List.Vector ℕ 2 → ℕ :=
    fun v => ((Nat.Partrec.Code.evaln v.head c v.tail.head).map Nat.succ).getD 0 with hF
  have hprim : Primrec F := by
    have h1 : Primrec (fun v : List.Vector ℕ 2 => Nat.Partrec.Code.evaln v.head c v.tail.head) :=
      Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair (Primrec.pair Primrec.vector_head
        (Primrec.const c)) (Primrec.vector_head.comp Primrec.vector_tail))
    exact Primrec.option_getD.comp (Primrec.option_map h1 (Primrec.succ.comp Primrec.snd))
      (Primrec.const 0)
  have hFd : DiophFn (fun v : Vector3 ℕ 2 => F (toLV v)) :=
    diophFnV_of_primrec' (Nat.Primrec'.of_prim hprim)
  have hS : Dioph {v : Vector3 ℕ 2 | 0 < F (toLV v)} := Dioph.lt_dioph (Dioph.const_dioph 0) hFd
  refine Dioph.ext (Dioph.vec_ex1_dioph 1 hS) fun v => ?_
  simp only [Set.mem_setOf_eq]
  rw [hc (v Fin2.fz)]
  refine exists_congr fun k => ?_
  have hval : F (toLV (Vector3.cons k v)) =
      ((Nat.Partrec.Code.evaln k c (v Fin2.fz)).map Nat.succ).getD 0 := by
    rw [hF]
    simp
  rw [hval]
  rcases h : Nat.Partrec.Code.evaln k c (v Fin2.fz) with _ | x <;> simp

end CS

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

