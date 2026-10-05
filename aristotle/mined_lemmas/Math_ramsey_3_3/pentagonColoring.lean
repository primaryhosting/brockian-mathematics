import Mathlib

/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- Boolean core of the pigeonhole/case analysis for `R(3,3) ≤ 6`: for any assignment of two
colours to the fifteen edges of `K₆` (edge `pq` for `p < q` is the variable listed in
lexicographic order), one of the twenty triangles is monochromatic. -/

noncomputable def pentagonColoring : Sym2 (Fin 5) → Bool :=
  Sym2.lift ⟨fun i j => ((i.val + 1) % 5 == j.val) || ((j.val + 1) % 5 == i.val), by decide⟩

/-- **R(3,3) = 6.**  Every 2-colouring of the edges of `K₆` contains a monochromatic triangle,
while there is a 2-colouring of the edges of `K₅` with no monochromatic triangle. -/
