/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module documentation, so the header above is
-- written as a plain comment; it is repeated as the module docstring below.)
import RequestProject.Savitch.Final

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The machine model is the standard off-line random-access model of space bounded computation
(see `RequestProject/Savitch/Model.lean`): the memory of a machine is a bit string, one step
rewrites the memory using the memory content and a single input bit, read at a position which
is determined by the memory, and the space used on an input is the maximal length of a memory
string occurring in the computation.

`NSPACE f` and `DSPACE g` are the classes of languages accepted by nondeterministic,
respectively deterministic, machines running in space `O (f n)`, respectively `O (g n)`.

The proof is Savitch's: for a nondeterministic machine `M` running in space `S` on the input
`x`, deciding whether `M` accepts amounts to deciding reachability in the configuration graph
of `M` on `x`, whose vertices are the words of length at most `S`.  Reachability by a path of
length at most `2 ^ k` is decided by the midpoint recursion `savR`, whose recursion depth is
`k`; taking `k = S + 1` suffices because there are only `2 ^ (S + 1) - 1` configurations.  The
simulator runs this recursion with an explicit stack of at most `S + 2` frames, each holding
three words of length at most `S`, so it uses `O (S ^ 2)` bits.  Since the simulator does not
know `S`, it runs the whole procedure for stages `s = 0, 1, 2, …`, and at each stage also
checks whether some reachable configuration has a successor of length more than `s`; the first
stage at which this check fails gives the correct answer, and this happens at the latest at
stage `S`.
-/

namespace CS

namespace Savitch

/-- A deterministic machine viewed as a nondeterministic machine. -/

theorem firstBit_mem_DSPACE :
    {x : Word | x[0]? = some true} ∈ DSPACE (fun _ => 1) := by
  refine ⟨Savitch.firstBitD, 1, ?_, ?_⟩
  · intro x t
    cases t with
    | zero => simp [DMachine.run]
    | succ t =>
        rw [Savitch.firstBitD_run_succ]
        by_cases h : x[0]? = some true <;> simp [h]
  · ext x
    simp only [DMachine.lang, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, ht⟩
      cases t with
      | zero => simp [DMachine.run, Savitch.firstBitD] at ht
      | succ t =>
          rw [Savitch.firstBitD_run_succ] at ht
          by_contra h
          simp [h, Savitch.firstBitD] at ht
    · intro h
      exact ⟨1, by rw [Savitch.firstBitD_run_succ]; simp [h, Savitch.firstBitD]⟩

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

/-
# Bounded reachability and the Savitch recursion

`PathN E s n a b` says that there is a path of length exactly `n` from `a` to `b` for the edge
relation `E`, all of whose vertices, except possibly the last one, are words of length at most
`s`.

`savR E s k a b` is the midpoint recursion of Savitch's algorithm; it decides whether `b` can be
reached from `a` by a path of length at most `2 ^ k` inside the set of words of length `≤ s`.
-/
import RequestProject.Savitch.Words

namespace CS
namespace Savitch

variable {E : Word → Word → Bool} {s : ℕ}

/-- A path of length `n` from `a` to `b`, staying (except possibly for its last vertex)
inside the words of length at most `s`. -/
