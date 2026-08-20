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


noncomputable def firstBitMach (n : ℕ) : Mach n where
  V := Bool
  fV := inferInstance
  start := false
  acc := true
  edge := fun u v =>
    if u = false ∧ v = true then
      (if h : 0 < n then Lit.test ⟨0, h⟩ true else Lit.never)
    else Lit.never

