/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix ComplexOrder

namespace Phys

/-! ## Entropy of a finitely supported probability vector -/

/-- Shannon entropy of a real vector, `∑ -p i * log (p i)`. -/

noncomputable def mpsProd (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ) (o n : ℕ)
    (s : Fin n → Fin d) : Matrix (Fin D) (Fin D) ℂ :=
  (List.ofFn fun i : Fin n => A (o + (i : ℕ)) (s i)).prod

/-- The amplitude of a matrix product state with bond dimension `D`, local dimension `d`,
tensors `A` and boundary vectors `vL`, `vR`. -/
