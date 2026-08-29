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

theorem poly_lt_exp (k m : ℕ) : ∃ n ≥ m, (n + 2) ^ k < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (r := (2:ℝ)) (by norm_num)
  have h2 : ∀ᶠ n : ℕ in atTop, (n:ℝ) ^ k / 2 ^ n < 1 / 4 :=
    h.eventually (gt_mem_nhds (show (0:ℝ) < 1 / 4 by norm_num))
  obtain ⟨N, hN⟩ := h2.exists_forall_of_atTop
  set n := max N (m + 2) with hn
  have hnN : N ≤ n := le_max_left _ _
  have hnm : m + 2 ≤ n := le_max_right _ _
  have hlt := hN n hnN
  have hpos : (0:ℝ) < 2 ^ n := by positivity
  have h3 : (n:ℝ) ^ k * 4 < 2 ^ n := by
    rw [div_lt_iff₀ hpos] at hlt; nlinarith [hlt]
  refine ⟨n - 2, by omega, ?_⟩
  have hn2 : n - 2 + 2 = n := by omega
  rw [hn2]
  have e : (2:ℝ) ^ (n - 2 + 2) = 2 ^ (n - 2) * 4 := by rw [pow_add]; norm_num
  rw [hn2] at e
  have h4 : (n:ℝ) ^ k < 2 ^ (n - 2) := by
    rw [e] at h3
    nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) (n - 2)]
  exact_mod_cast (by exact_mod_cast h4 : ((n ^ k : ℕ) : ℝ) < ((2 ^ (n - 2) : ℕ) : ℝ))

/-- If a list contains fewer than `2 ^ n` strings, some string of length `n` is missing
from it. -/
