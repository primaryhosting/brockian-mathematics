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


noncomputable def cmach (r : Fin m → Fin m → Lit n) (s t : Fin m) : Mach n where
  V := St m
  fV := inferInstance
  start := .lvl 0 1
  acc := .acc
  edge := E r s t

