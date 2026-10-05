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
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

We set up two-party communication protocols as protocol trees, and prove the
`Ω(n)` lower bound for the randomized communication complexity of set
disjointness on `n`-element ground sets: any public-coin randomized protocol
which never wrongly claims that two intersecting sets are disjoint, and which
detects disjointness with probability at least `1/2`, must communicate at least
`n - 1` bits (`CS.disjointness_lb`).

The proof combines the classical fooling set `{(S, Sᶜ) : S ⊆ Fin n}` of size
`2 ^ n` for disjointness with an averaging argument over the public random
string.  We also record the matching upper bound `n + 1`
(`CS.disjointness_ub`), which shows in particular that the hypotheses of the
lower bound are satisfiable, and the deterministic lower bound `n`
(`CS.disjointness_deterministic_lb`).

The randomized bound proved here is for protocols with one-sided error (they
never certify disjointness wrongly); the two-sided bounded-error case is
Razborov's theorem and is not covered by this argument.
-/

open Finset

namespace CS

open scoped Classical

/-- A deterministic two-party communication protocol tree.  `alice g L R` means
"Alice sends the bit `g x` and the players continue with `L` (if the bit is
`true`) or `R` (if it is `false`)"; `bob` is the same with Bob speaking. -/
inductive Prot (X Y : Type*) : Type _
  | leaf : Bool → Prot X Y
  | alice : (X → Bool) → Prot X Y → Prot X Y → Prot X Y
  | bob : (Y → Bool) → Prot X Y → Prot X Y → Prot X Y

namespace Prot

variable {X Y : Type*}

/-- The output of the protocol on the input pair `(x, y)`. -/

def getBit {n : ℕ} (m : ℕ) (x : Fin n → Bool) : Bool :=
  if h : m < n then x ⟨m, h⟩ else false

/-- The naive protocol: Alice reveals her bits `m-1, …, 0` one at a time, and
Bob finally answers.  The parameter `h` records the answer Bob would give on
the basis of the bits revealed so far. -/
