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

theorem exists_index {f : ℕ →. ℕ} (hf : Nat.Partrec f) : ∃ n, phi n = f := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 hf
  exact ⟨Encodable.encode c, by rw [phi_encode, hc]⟩

/-- **Rice's theorem** (index-set form). Let `A` be a set of program indices which is
*semantic* (extensional): membership of an index in `A` depends only on the partial
function that index computes. If `A` is *nontrivial*, i.e. it is neither empty nor all of
`ℕ`, then `A` is not recursive (decidable). -/
