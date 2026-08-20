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


theorem NL_firstBit : NL (fun n x => ∃ h : 0 < n, x ⟨0, h⟩ = true) := by
  refine ⟨1, fun n => ⟨firstBitMach n, ?_, fun x => (firstBitMach_accepts n x).symm⟩⟩
  have : Fintype.card (firstBitMach n).V = 2 := rfl
  simp only [this, pow_one]
  omega

end CS

import RequestProject.ISModel

/-!
# Level sets of reachability

For a guarded graph `r` on `Fin m` and an input `x`, `RS r s x i` is the set of vertices
reachable from `s` in at most `i` steps (we allow "waiting", so the level sets are
increasing by construction).

The main result is that the level sets stabilise at level `m + 1`, so that
`RS r s x (m+1)` is exactly the set of vertices reachable from `s`.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS

variable {n m : ℕ}

/-- The one step relation of a guarded graph on the input `x`. -/
