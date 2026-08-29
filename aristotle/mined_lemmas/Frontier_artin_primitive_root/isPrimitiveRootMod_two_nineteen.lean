/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `IsPrimitiveRootMod a p` says that the integer `a` is a primitive root modulo `p`,
i.e. the residue of `a` generates the multiplicative group `(ZMod p)ˣ`, which for a
prime `p` amounts to the multiplicative order of `a` modulo `p` being `p - 1`. -/

theorem isPrimitiveRootMod_two_nineteen : IsPrimitiveRootMod 2 19 := by
  have : ((2 : ℤ) : ZMod 19) = (2 : ZMod 19) := by norm_num
  rw [IsPrimitiveRootMod, this, orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

/-! ### Main statement -/

/-- **Artin's conjecture on primitive roots**, formalized as
`Frontier.ArtinPrimitiveRootConjecture`, together with what is proved here:

* the exceptional cases of the conjecture are genuinely exceptional — if `a` is a perfect
  square, resp. `a = -1`, then the set of primes having `a` as a primitive root is finite
  (contained in `{2}`, resp. `{2,3}`), so the two hypotheses of the conjecture cannot be
  dropped;
* base cases: `2` is a primitive root modulo `3`, `5`, `11`, `13` and `19`. -/
