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

private theorem sum_comm_first_last {α : Type*} [Fintype α] (f : α → α → α → ℂ) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ z, ∑ y, ∑ x, f x y z := by
  calc ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ z, ∑ y, f x y z :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, f x y z := Finset.sum_comm
    _ = ∑ z, ∑ y, ∑ x, f x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Contracting a product of two matrices with boundary vectors splits over the bond index. -/
