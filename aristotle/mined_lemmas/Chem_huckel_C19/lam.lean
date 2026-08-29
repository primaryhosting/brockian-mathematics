import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex Finset

namespace Chem

/-- `Fin 19` carries the commutative ring structure of `ZMod 19`
(the two types, and their additive group structures, are definitionally equal). -/
noncomputable local instance : CommRing (Fin 19) := (inferInstance : CommRing (ZMod 19))

/-- A primitive 19-th root of unity. -/

noncomputable def lam (k : Fin 19) : ℂ := ((2 * Real.cos (2 * Real.pi * k.val / 19) : ℝ) : ℂ)

