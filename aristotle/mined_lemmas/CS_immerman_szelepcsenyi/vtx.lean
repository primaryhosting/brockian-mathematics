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


def vtx (v : Fin m) : Fin (m + 2) := ⟨v.val, by omega⟩

/-- An encoding of the configurations into a product of index types, used only to bound
the number of configurations. -/
