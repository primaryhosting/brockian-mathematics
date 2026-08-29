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

import Mathlib

/-!
# A relativized model of computation

We formalise oracle computation by a small imperative register language over bit
strings.  Registers hold finite bit strings (`List Bool`), and a program may query
an oracle (an arbitrary set of bit strings, presented as `Str → Bool`).

The cost model is: each elementary instruction costs one unit, except copying and
querying, which cost one unit plus the length of the string that is moved / written
on the query tape.  This is the usual convention for oracle Turing machines: writing
the query string on the oracle tape takes as many steps as the string is long.
-/

set_option autoImplicit false

namespace BGS

/-- Bit strings. -/
abbrev Str := List Bool

/-- An oracle is an arbitrary set of bit strings. -/
abbrev Oracle := Str → Bool

/-- A language is a set of bit strings. -/
abbrev Lang := Set Str

/-- A register store: countably many registers, each holding a bit string. -/
abbrev St := ℕ → Str

/-- Update one register. -/

lemma run_congr (O O' : Oracle) (cf : Cfg) (t : ℕ)
    (h : ∀ q ∈ queriesUpto O cf t, O q = O' q) :
    (step O)^[t] cf = (step O')^[t] cf ∧ gasUsed O cf t = gasUsed O' cf t ∧
      queriesUpto O cf t = queriesUpto O' cf t := by
  induction t with
  | zero => simp [gasUsed, queriesUpto]
  | succ t ih =>
      have hsub : ∀ q ∈ queriesUpto O cf t, O q = O' q := by
        intro q hq
        exact h q (by rw [queriesUpto_succ]; exact List.mem_append_left _ hq)
      obtain ⟨h1, h2, h3⟩ := ih hsub
      have hstepeq : step O ((step O)^[t] cf) = step O' ((step O')^[t] cf) := by
        rw [← h1]
        refine step_congr O O' _ (fun q hq => h q ?_)
        exact queriesUpto_mem (Nat.lt_succ_self t) hq
      refine ⟨?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstepeq]
      · rw [gasUsed_succ, gasUsed_succ, h1, h2]
      · rw [queriesUpto_succ, queriesUpto_succ, h1, h3]

end BGS

