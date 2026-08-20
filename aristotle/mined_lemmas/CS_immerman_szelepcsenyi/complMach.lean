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


noncomputable def complMach (M : Mach n) : Mach n :=
  let e : M.V ≃ Fin (Fintype.card M.V) := Fintype.equivFin M.V
  cmach (fun u v => M.edge (e.symm u) (e.symm v)) (e M.start) (e M.acc)

