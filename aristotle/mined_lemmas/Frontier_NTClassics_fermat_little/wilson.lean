import Mathlib
namespace Frontier.NTClassics


theorem wilson (p : ℕ) (hp : p.Prime) : ((p-1).factorial : ZMod p) = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact ZMod.wilsons_lemma p

