/-
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 does not permit a module docstring `/-! ... -/` before the `import` block, so the
-- required header appears verbatim above as a plain comment and again below as the module
-- docstring.)

import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-!
## The `n`-gon vertex action of the dihedral group

We realise `DihedralGroup n` as the symmetry group of the regular `n`-gon by letting it act on
the vertex set `ZMod n`.  With Mathlib's multiplication convention

```
r i * r j = r (i + j),  r i * sr j = sr (j - i),  sr i * r j = sr (i + j),  sr i * sr j = r (j - i)
```

the corresponding left action is

```
r i • x = x - i,        sr i • x = i - x.
```

For `n = 5` this is the usual action of the symmetry group of the regular pentagon on its five
vertices; everything below is proved for arbitrary `n`, which is the promised extension.
-/

/-- The action of an element of `DihedralGroup n` on a vertex of the regular `n`-gon. -/

theorem card_vertexOrbits (n : ℕ) [NeZero n] :
    Nat.card (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n)) = 1 := by
  have hne : Nonempty (ZMod n) := ⟨0⟩
  have huniq : Unique (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n)) :=
    ((MulAction.pretransitive_iff_unique_quotient_of_nonempty (DihedralGroup n) (ZMod n)).mp
      inferInstance).some
  letI := huniq
  exact Nat.card_unique

/-!
## The permutation character and the multiplicity of the trivial character
-/

/-- The permutation character of the `n`-gon vertex action: `g` is sent to the number of
vertices that it fixes. -/
