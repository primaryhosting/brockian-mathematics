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

theorem mpsProd_append (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ) (o k m : ℕ)
    (u : Fin k → Fin d) (v : Fin m → Fin d) :
    mpsProd A o (k + m) (Fin.append u v) = mpsProd A o k u * mpsProd A (o + k) m v := by
  unfold mpsProd
  rw [List.ofFn_add, List.prod_append]
  congr 1
  · refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    have h1 : Fin.castLE (Nat.le_add_right k m) i = Fin.castAdd m i := rfl
    simp [h1, Fin.append_left]
  · refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp [Fin.append_right, Nat.add_assoc]

/-- Auxiliary permutation of a triple sum. -/
