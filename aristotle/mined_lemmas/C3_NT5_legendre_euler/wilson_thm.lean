import Mathlib
namespace C3.NT5

/-- Euler's criterion: the Legendre symbol `(a/p)`, viewed in `ZMod p`, equals
`a ^ ((p-1)/2)` for an odd prime `p`. -/

theorem wilson_thm (p : ℕ) (hp : p.Prime) : ((p-1).factorial : ZMod p) = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact ZMod.wilsons_lemma p

end C3.NT5

