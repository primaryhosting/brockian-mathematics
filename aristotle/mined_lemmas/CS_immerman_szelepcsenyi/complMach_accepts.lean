import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS


lemma complMach_accepts (M : Mach n) (x : Fin n → Bool) :
    (complMach M).Accepts x ↔ ¬ M.Accepts x := by
  let e : M.V ≃ Fin (Fintype.card M.V) := Fintype.equivFin M.V
  show (cmach (fun u v => M.edge (e.symm u) (e.symm v)) (e M.start) (e M.acc)).Accepts x ↔ _
  rw [cmach_correct]
  have h : Relation.ReflTransGen (Rl (fun u v => M.edge (e.symm u) (e.symm v)) x)
      (e M.start) (e M.acc) ↔ M.Accepts x :=
    (reflTransGen_equiv e (M.Step x) M.start M.acc).symm
  rw [h]

/-- **Complementation of nondeterministic machines.** For every machine `M` there is a
machine `M'`, with polynomially many configurations in the number of configurations of
`M`, accepting exactly the inputs rejected by `M`. -/
