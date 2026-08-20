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

import RequestProject.BGS.PartA
import RequestProject.BGS.PartB

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Statement: There are oracles A,B with P^A=NP^A and P^B≠NP^B (relativization barrier).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header block above is placed after the `import` lines because Lean 4 requires
`import` commands to come first in a file.)

The model of relativized computation is developed in `RequestProject.BGS.Model`:

* an *oracle* is a set of binary strings, `Oracle := Str → Bool`;
* an *oracle machine* `OM` is a pair of computable functions `ask`, `out`: `ask z l`
  returns the next query on input `z` (a pair of an input and a certificate) given the
  list `l` of oracle answers received so far, and `out z l` returns the verdict;
* `Bounded M k` says that all queries of `M` have length at most `(|x|+2)^k`, where `x`
  is the proper input, and a machine is run for `(|x|+2)^k` steps;
* `Po A L` (`L ∈ P^A`) and `NPo A L` (`L ∈ NP^A`) are the usual definitions, and
  `PClass A`, `NPClass A` are the corresponding classes of languages.

`RequestProject.BGS.PartA` builds an oracle `A` (by recursion on the length of strings)
which encodes acceptance of the `NP^A` computations, so that `P^A = NP^A`.

`RequestProject.BGS.PartB` builds an oracle `B` by diagonalization, so that the unary
language `LB = {1^n : B contains a string of length n}` lies in `NP^B` but not in `P^B`.
-/

namespace CS

/-- **Baker–Gill–Solovay theorem** (the relativization barrier): there is an oracle `A`
with `P^A = NP^A` and an oracle `B` with `P^B ≠ NP^B`. -/

theorem natFun_inj {α σ} [Primcodable α] [Primcodable σ] {f g : α → σ}
    (h : natFun f = natFun g) : f = g := by
  funext a
  have := congrFun h (Encodable.encode a)
  simpa [natFun, Encodable.encodek] using this

instance countable_computable {α σ} [Primcodable α] [Primcodable σ] :
    Countable {f : α → σ // Computable f} := by
  classical
  refine Function.Injective.countable
    (f := fun f : {f : α → σ // Computable f} =>
      (Nat.Partrec.Code.exists_code.mp (natFun_partrec f.1 f.2)).choose) ?_
  intro f g hfg
  have e1 := (Nat.Partrec.Code.exists_code.mp (natFun_partrec f.1 f.2)).choose_spec
  have e2 := (Nat.Partrec.Code.exists_code.mp (natFun_partrec g.1 g.2)).choose_spec
  simp only at hfg
  rw [hfg] at e1
  exact Subtype.ext (natFun_inj (e1.symm.trans e2))

instance : Countable OM := by
  refine Function.Injective.countable
    (f := fun M : OM =>
      ((⟨fun p => M.ask p.1 p.2, M.ask_computable⟩ :
          {f : (Str × Str) × List Bool → Str // Computable f}),
       (⟨fun p => M.out p.1 p.2, M.out_computable⟩ :
          {f : (Str × Str) × List Bool → Bool // Computable f}))) ?_
  rintro ⟨a₁, o₁, ha₁, ho₁⟩ ⟨a₂, o₂, ha₂, ho₂⟩ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have ha : a₁ = a₂ := by funext z l; exact congrFun h1 (z, l)
  have ho : o₁ = o₂ := by funext z l; exact congrFun h2 (z, l)
  subst ha; subst ho; rfl

/-- A trivial machine, used to witness nonemptiness of `OM`. -/
