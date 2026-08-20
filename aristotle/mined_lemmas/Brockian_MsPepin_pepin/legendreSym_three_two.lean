import Mathlib
namespace Brockian.MsPepin

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `1` mod `4`. -/

private lemma legendreSym_three_two : legendreSym 3 (2 : ℤ) = -1 := by decide

/-- `3` is a quadratic nonresidue modulo a prime Fermat number `F n`, `n ≥ 1`. -/
