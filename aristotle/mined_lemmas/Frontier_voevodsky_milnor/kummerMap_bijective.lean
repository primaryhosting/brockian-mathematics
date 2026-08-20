import Mathlib

/-!
# Mod-2 Milnor K-theory of a field

For a field `F` we define
`k_n(F) = K^M_n(F)/2`, the `n`-th mod-2 Milnor K-group, as the quotient of the `n`-fold
tensor power over `𝔽₂` of the square class group `F^×/(F^×)²` by the Steinberg relations
`{a, 1-a} = 0`.
-/

open scoped TensorProduct

namespace MilnorK

variable (F : Type) [Field F]

/-- The subgroup of squares of `Fˣ`. -/

theorem kummerMap_bijective : Function.Bijective (kummerMap F) :=
  ⟨kummerMap_injective F, kummerMap_surjective F⟩

end Kummer

import Mathlib
import RequestProject.ContCohomology
import RequestProject.MilnorK
import RequestProject.Kummer

/-!
# Voevodsky Milnor
Category: Frontier — Fields Medal Work
Target: Frontier.voevodsky_milnor
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to be preceded by the `import` lines, since Lean 4 requires
`import` commands to come first in a file.)

## What is formalized here

For a field `F` with `char F ≠ 2` we have defined

* `MilnorK.MilnorK2 F n`, the mod-2 Milnor K-group `k_n(F) = K^M_n(F)/2`, as the quotient of the
  `n`-fold tensor power over `𝔽₂` of the square class group `F^×/(F^×)²` by the Steinberg
  relations (see `RequestProject/MilnorK.lean`);
* `ContCoh.H G n`, the continuous cochain cohomology `Hⁿ(G, ℤ/2)` of a topological group `G`
  with trivial coefficients `ℤ/2` (see `RequestProject/ContCohomology.lean`), applied to the
  absolute Galois group `G_F = Gal(F^sep/F)` with its Krull topology;
* the norm residue maps in degrees `0` and `1`, the latter being the Kummer map
  `a ↦ (σ ↦ σ(√a)/√a)`.

`Frontier.milnorConjecture F` states the Milnor conjecture (Voevodsky's theorem):
mod-2 Galois cohomology is isomorphic to mod-2 Milnor K-theory in every degree.

The theorem `Frontier.voevodsky_milnor` proves the base cases: the norm residue maps in
degrees `0` and `1` are bijective. Degree `1` is Kummer theory, and it is proved here in full
(injectivity and surjectivity) for every field of characteristic `≠ 2`.
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open MilnorK ContCoh Kummer

namespace Frontier

variable (F : Type) [Field F] [NeZero (2 : F)]

/-- The Milnor conjecture (Voevodsky's theorem): in every degree the mod-2 Milnor K-group
`k_n(F) = K^M_n(F)/2` is isomorphic to the mod-2 Galois cohomology `Hⁿ(G_F, ℤ/2)`. -/
