/-
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: verified (axiom-clean)
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- **Regular languages are closed under complement.**

If a language `L` over an alphabet `T` is regular, i.e. it is accepted by some
(finite-state) DFA, then its complement `Lᶜ` is regular as well: one simply
swaps accepting and non-accepting states of a DFA recognizing `L`. -/
theorem dfa_complement_regular {T : Type u} {L : Language T} (hL : L.IsRegular) :
    (Lᶜ : Language T).IsRegular := by
  obtain ⟨σ, inst, M, rfl⟩ := hL
  refine ⟨σ, inst, ⟨M.step, M.start, M.acceptᶜ⟩, ?_⟩
  ext x
  rw [Set.mem_compl_iff, DFA.mem_accepts, DFA.mem_accepts]
  simp [DFA.eval, DFA.evalFrom]

end CS

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

