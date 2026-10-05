/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
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

namespace CS

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- `phi n` is the partial function computed by the program with index `n`
(the standard enumeration of partial recursive functions, obtained from the
Gödel numbering of `Nat.Partrec.Code`). -/

theorem index_of_empty_not_computable :
    ¬ ComputablePred (fun n : ℕ => n ∈ {n : ℕ | phi n = fun _ => Part.none}) := by
  refine rice_extended _ (fun m n h => by simp [Set.mem_setOf_eq, h]) ?_ ?_
  · obtain ⟨n, hn⟩ := exists_index (f := fun _ => Part.none) Nat.Partrec.none
    exact ⟨n, by simpa using hn⟩
  · obtain ⟨n, hn⟩ := exists_index (Nat.Partrec.of_primrec Nat.Primrec.id)
    refine ⟨n, ?_⟩
    intro hmem
    have h0 : phi n 0 = Part.none := by
      rw [(hmem : phi n = fun _ => Part.none)]
    rw [hn] at h0
    simp [Part.eq_none_iff'] at h0

end CS

#print axioms CS.rice_extended
#print axioms CS.halting_not_computable
#print axioms CS.index_of_empty_not_computable

