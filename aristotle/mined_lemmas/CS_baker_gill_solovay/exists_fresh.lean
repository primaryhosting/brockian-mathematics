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

theorem exists_fresh (n : ℕ) (Q : List (List Bool)) (h : Q.length < 2 ^ n) :
    ∃ y : List Bool, y.length = n ∧ y ∉ Q := by
  by_contra hc
  push_neg at hc
  set T : Finset (List Bool) :=
    (Finset.univ : Finset (Fin n → Bool)).image (fun f => List.ofFn f) with hT
  have hcard : T.card = 2 ^ n := by
    rw [hT, Finset.card_image_of_injective _ List.ofFn_injective]
    simp
  have hsub : T ⊆ Q.toFinset := by
    intro y hy
    rw [hT] at hy
    simp only [Finset.mem_image] at hy
    obtain ⟨f, -, rfl⟩ := hy
    simp only [List.mem_toFinset]
    exact hc _ (by simp)
  have := Finset.card_le_card hsub
  have h2 := Q.toFinset_card_le
  omega

/-- An arithmetic bound used to fit the cost of a single oracle call into a polynomial. -/
