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
A model of polynomial-time oracle computation, used to state and prove the
Baker-Gill-Solovay theorem.

*Strings* are finite lists of booleans.  An *oracle* is a map from strings to
booleans.

A *machine* is a code `c` for a partial recursive function (`Nat.Partrec.Code`).
A machine is run on a pair of strings `(x, w)` (the input and a certificate; for
deterministic computation `w = []`).  The machine interacts with the oracle in
rounds: in a configuration where the list of oracle answers received so far is
`as`, the machine computes `c.eval (encode ((x, w), as))`, whose value is
interpreted as
* `0`  : halt and reject,
* `1`  : halt and accept,
* `n+2`: query the string coded by `n`, and continue with the answer appended to `as`.

The *cost* of a run is the number of rounds plus the total length of all queried
strings (writing a query string of length `ℓ` costs `ℓ` steps, and halting costs
one step).  This is the cost measure with respect to which polynomial time
bounds are imposed; the oracle-independent internal computation of the partial
recursive step function is required to converge, but is not itself charged.
Since the same convention is used for both `P` and `NP`, the two classes below
are the relativized classes of the standard query-cost model, and the machine
type ranges over *all* partial recursive step functions.
-/
import Mathlib

namespace CS

open Encodable Nat.Partrec

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings, presented as its characteristic function. -/
abbrev Oracle := Str → Bool

/-- A language is a set of strings. -/
abbrev Lang := Set Str

/-- `HaltsQ c O x as b n Q` : the machine `c` with oracle `O`, running on input
pair `x` with oracle answers `as` received so far, halts with output `b`,
at cost `n`, having made the queries `Q` (in order). -/
inductive HaltsQ (c : Code) (O : Oracle) (x : Str × Str) :
    List Bool → Bool → ℕ → List Str → Prop
  | halt {as : List Bool} {b : Bool} :
      (cond b 1 0 : ℕ) ∈ c.eval (encode (x, as)) → HaltsQ c O x as b 1 []
  | query {as : List Bool} {q : Str} {b : Bool} {n : ℕ} {Q : List Str} :
      (encode q + 2) ∈ c.eval (encode (x, as)) →
      HaltsQ c O x (as ++ [O q]) b n Q →
      HaltsQ c O x as b (n + q.length + 1) (q :: Q)

namespace HaltsQ

/-- Every queried string is shorter than the cost of the run. -/

theorem length_lt {c : Code} {O : Oracle} {x : Str × Str} {as : List Bool} {b : Bool}
    {n : ℕ} {Q : List Str} (h : HaltsQ c O x as b n Q) :
    ∀ q ∈ Q, q.length < n := by
  induction h with
  | halt _ => simp
  | query _ _ ih =>
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · omega
      · have := ih q hq; omega

/-- The number of queries is smaller than the cost of the run. -/
