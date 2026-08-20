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

theorem precFn_dioph {n : ℕ} {F : Vector3 ℕ n → ℕ} {G : Vector3 ℕ (n + 2) → ℕ}
    (dF : DiophFn F) (dG : DiophFn G) :
    DiophFn (fun v : Vector3 ℕ (n + 1) => precFn F G (fun i => v (Fin2.fs i)) (v Fin2.fz)) := by
  set S : Set (Option (Fin2 (n + 4)) → ℕ) :=
    {t | beta (t (some (Fin2.fs Fin2.fz))) (t (some Fin2.fz)) (t none + 1) =
      G (Vector3.cons (t none) (Vector3.cons
        (beta (t (some (Fin2.fs Fin2.fz))) (t (some Fin2.fz)) (t none))
        (fun i => t (some (Fin2.fs (Fin2.fs (Fin2.fs (Fin2.fs i))))))))} with hS
  have dS : Dioph S := by
    refine Dioph.eq_dioph (beta_dioph (Dioph.proj_dioph _) (Dioph.proj_dioph _)
      (Dioph.add_dioph (Dioph.proj_dioph none) (Dioph.const_dioph 1))) ?_
    exact diophFn_comp_cons2 dG (Dioph.proj_dioph none)
      (beta_dioph (Dioph.proj_dioph _) (Dioph.proj_dioph _) (Dioph.proj_dioph none))
      (fun i => Dioph.proj_dioph _)
  have dmid : Dioph {u : Fin2 (n + 4) → ℕ | ∀ x < u (Fin2.fs (Fin2.fs (Fin2.fs Fin2.fz))),
      Option.elim' x u ∈ S} := forall_lt_dioph dS (Dioph.proj_dioph _)
  have dfirst : Dioph {u : Fin2 (n + 4) → ℕ |
      beta (u (Fin2.fs Fin2.fz)) (u Fin2.fz) 0
        = F (fun i => u (Fin2.fs (Fin2.fs (Fin2.fs (Fin2.fs i)))))} :=
    Dioph.eq_dioph (beta_dioph (Dioph.proj_dioph _) (Dioph.proj_dioph _) (Dioph.const_dioph 0))
      (Dioph.reindex_diophFn (fun i => Fin2.fs (Fin2.fs (Fin2.fs (Fin2.fs i)))) dF)
  have dlast : Dioph {u : Fin2 (n + 4) → ℕ |
      beta (u (Fin2.fs Fin2.fz)) (u Fin2.fz) (u (Fin2.fs (Fin2.fs (Fin2.fs Fin2.fz))))
        = u (Fin2.fs (Fin2.fs Fin2.fz))} :=
    Dioph.eq_dioph (beta_dioph (Dioph.proj_dioph _) (Dioph.proj_dioph _) (Dioph.proj_dioph _))
      (Dioph.proj_dioph _)
  have dS2 : Dioph ({u : Vector3 ℕ (n + 4) |
      beta (u (Fin2.fs Fin2.fz)) (u Fin2.fz) 0
        = F (fun i => u (Fin2.fs (Fin2.fs (Fin2.fs (Fin2.fs i)))))} ∩
    ({u : Vector3 ℕ (n + 4) | ∀ x < u (Fin2.fs (Fin2.fs (Fin2.fs Fin2.fz))),
      Option.elim' x u ∈ S} ∩
    {u : Vector3 ℕ (n + 4) |
      beta (u (Fin2.fs Fin2.fz)) (u Fin2.fz) (u (Fin2.fs (Fin2.fs (Fin2.fs Fin2.fz))))
        = u (Fin2.fs (Fin2.fs Fin2.fz))})) := dfirst.inter (dmid.inter dlast)
  rw [Dioph.diophFn_vec]
  refine Dioph.ext (Dioph.vec_ex1_dioph _ (Dioph.vec_ex1_dioph _ dS2)) fun v => ?_
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hS, Vector3.cons_fz, Vector3.cons_fs,
    Option.elim']
  rw [precFn_iff]
  rfl

/-! ### From `List.Vector` to `Vector3` -/

/-- Convert an inductively indexed vector to a `List.Vector`. -/
