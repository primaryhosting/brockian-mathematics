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


def enc : St m →
    Fin 6 × Fin (m+2) × Fin (m+2) × Fin (m+2) × Fin (m+2) × Fin (m+2) × Fin (m+2) ×
      Fin (m+2) × Fin (m+2) × Fin (m+2)
  | .lvl i c => (0, i, c, 0, 0, 0, 0, 0, 0, 0)
  | .outer i c j c' => (1, i, c, j, c', 0, 0, 0, 0, 0)
  | .walkY i c j c' w k => (2, i, c, j, c', vtx w, k, 0, 0, 0)
  | .no i c j c' v jj d => (3, i, c, j, c', vtx v, jj, d, 0, 0)
  | .walkN i c j c' v jj d w k => (4, i, c, j, c', vtx v, jj, d, vtx w, k)
  | .acc => (5, 0, 0, 0, 0, 0, 0, 0, 0, 0)

