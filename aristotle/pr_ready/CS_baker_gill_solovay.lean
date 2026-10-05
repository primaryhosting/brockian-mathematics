/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Statement: There are oracles A,B with P^A=NP^A and P^B≠NP^B (relativization barrier).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
theorem card_lt {c : Code} {O : Oracle} {x : Str × Str} {as : List Bool} {b : Bool}
    {n : ℕ} {Q : List Str} (h : HaltsQ c O x as b n Q) : Q.length < n := by
  induction h with
  | halt _ => simp
  | query _ _ ih => simp only [List.length_cons]; omega

/-- Runs are deterministic. -/
theorem unique {c : Code} {O : Oracle} {x : Str × Str} {as : List Bool} {b b' : Bool}
    {n n' : ℕ} {Q Q' : List Str} (h : HaltsQ c O x as b n Q) (h' : HaltsQ c O x as b' n' Q') :
    b = b' ∧ n = n' ∧ Q = Q' := by
  induction h generalizing b' n' Q' with
  | @halt as b hb =>
      cases h' with
      | halt hb' =>
          have := Part.mem_unique hb hb'
          cases b <;> cases b' <;> simp_all
      | query hq _ =>
          have := Part.mem_unique hb hq
          cases b <;> simp only [cond_true, cond_false] at this <;> omega
  | @query as q b n Q hq _ ih =>
      cases h' with
      | halt hb' =>
          have := Part.mem_unique hq hb'
          cases b' <;> simp only [cond_true, cond_false] at this <;> omega
      | @query as' q' b' n' Q' hq' h2' =>
          have hqq : encode q + 2 = encode q' + 2 := Part.mem_unique hq hq'
          have hq2 : q = q' := by
            have : encode q = encode q' := by omega
            exact Encodable.encode_injective this
          subst hq2
          obtain ⟨h1, h2, h3⟩ := ih h2'
          exact ⟨h1, by omega, by rw [h3]⟩

/-- Only the oracle answers on the queried strings matter. -/
theorem oracle_congr {c : Code} {O O' : Oracle} {x : Str × Str} {as : List Bool} {b : Bool}
    {n : ℕ} {Q : List Str} (h : HaltsQ c O x as b n Q) (hOO : ∀ q ∈ Q, O q = O' q) :
    HaltsQ c O' x as b n Q := by
  induction h with
  | halt hb => exact HaltsQ.halt hb
  | @query as q b n Q hq _ ih =>
      have hq0 : O q = O' q := hOO q (by simp)
      refine HaltsQ.query hq ?_
      rw [← hq0]
      exact ih fun q' hq' => hOO q' (by simp [hq'])

/-- Transferring a run along a code that simulates another code. -/
theorem congr_code {c c' : Code} {O : Oracle} {x x' : Str × Str} {as : List Bool} {b : Bool}
    {n : ℕ} {Q : List Str}
    (hsim : ∀ as : List Bool, c'.eval (encode (x', as)) = c.eval (encode (x, as)))
    (h : HaltsQ c O x as b n Q) : HaltsQ c' O x' as b n Q := by
  induction h with
  | @halt as b hb => exact HaltsQ.halt (by rw [hsim as]; exact hb)
  | @query as q b n Q hq _ ih => exact HaltsQ.query (by rw [hsim as]; exact hq) ih

end HaltsQ

/-- `L` is decided by a deterministic polynomial-time oracle machine with oracle `O`. -/
def InP (O : Oracle) (L : Lang) : Prop :=
  ∃ (c : Code) (k : ℕ), ∀ x : Str, ∃ (b : Bool) (n : ℕ) (Q : List Str),
      HaltsQ c O (x, []) [] b n Q ∧ n ≤ (x.length + 2) ^ k ∧ (b = true ↔ x ∈ L)

/-- `L` has a polynomial-time oracle verifier with oracle `O`. -/
def InNP (O : Oracle) (L : Lang) : Prop :=
  ∃ (c : Code) (k : ℕ), ∀ x : Str,
      (x ∈ L ↔ ∃ w : Str, w.length ≤ (x.length + 2) ^ k ∧
        ∃ (n : ℕ) (Q : List Str), HaltsQ c O (x, w) [] true n Q ∧ n ≤ (x.length + 2) ^ k)

/-- The relativized class `P^O`. -/
def PClass (O : Oracle) : Set Lang := {L | InP O L}

/-- The relativized class `NP^O`. -/
def NPClass (O : Oracle) : Set Lang := {L | InNP O L}

/-- Every partial recursive step function is realized by a machine. -/
theorem exists_code_of_partrec {α : Type} [Primcodable α] {f : α →. ℕ} (hf : Partrec f) :
    ∃ c : Code, ∀ p, c.eval (encode p) = f p := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 hf
  refine ⟨c, fun p => ?_⟩
  rw [hc]
  simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
  exact Part.map_id' (fun x => rfl) _

/-- `P^O ⊆ NP^O` for every oracle. -/
theorem InP.toInNP {O : Oracle} {L : Lang} (h : InP O L) : InNP O L := by
  obtain ⟨c, k, hc⟩ := h
  -- the verifier ignores its certificate and runs `c` on the input
  obtain ⟨c', hc'⟩ := exists_code_of_partrec (α := (Str × Str) × List Bool)
    (f := fun p => c.eval (encode (((p.1.1, ([] : Str)) : Str × Str), p.2)))
    (Code.eval_part.comp (Computable.const c)
      (Primrec.encode.comp
        (Primrec₂.pair.comp
          (Primrec₂.pair.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))
            (Primrec.const ([] : Str)))
          (Primrec.snd.comp Primrec.id))).to_comp)
  have hsim : ∀ (x : Str) (w : Str) (as : List Bool),
      c'.eval (encode (((x, w) : Str × Str), as))
        = c.eval (encode (((x, ([] : Str)) : Str × Str), as)) :=
    fun x w as => hc' (((x, w) : Str × Str), as)
  refine ⟨c', k, fun x => ?_⟩
  obtain ⟨b, n, Q, hrun, hn, hb⟩ := hc x
  constructor
  · intro hx
    have hbt : b = true := hb.2 hx
    subst hbt
    exact ⟨[], by positivity, n, Q, hrun.congr_code (hsim x []), hn⟩
  · rintro ⟨w, -, m, Q', hrun', hm⟩
    have hrun2 : HaltsQ c' O (x, w) [] b n Q := hrun.congr_code (hsim x w)
    obtain ⟨h1, -, -⟩ := hrun2.unique hrun'
    exact hb.1 h1

end CS

/-
Elementary counting and growth lemmas used in the Baker-Gill-Solovay proof.
-/

namespace CS

open Filter

/-- A polynomial is eventually dominated by `2 ^ n`: for every `k` and `m` there is
`n ≥ m` with `(n + 2) ^ k < 2 ^ n`. -/
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
theorem arith_bound (e n k : ℕ) : 2 * e + 2 * n + 4 + (n + 2) ^ k ≤ (n + 2) ^ (k + e + 4) := by
  have h1 : (2:ℕ) ^ e ≥ e + 1 := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have h2 : (n + 2) ^ e ≥ 2 ^ e := Nat.pow_le_pow_left (by omega) e
  have h3 : (n + 2) ^ 4 ≥ 2 * n + 5 := by nlinarith [sq_nonneg n]
  have hP : (n + 2) ^ (e + 4) ≥ 2 * e + 2 * n + 5 := by
    calc (n + 2) ^ (e + 4) = (n + 2) ^ e * (n + 2) ^ 4 := by rw [pow_add]
    _ ≥ (e + 1) * (2 * n + 5) := Nat.mul_le_mul (le_trans h1 h2) h3
    _ ≥ 2 * e + 2 * n + 5 := by nlinarith
  have ha : (n + 2) ^ k ≥ 1 := Nat.one_le_pow _ _ (by omega)
  calc 2 * e + 2 * n + 4 + (n + 2) ^ k ≤ (n + 2) ^ k * (2 * e + 2 * n + 5) := by nlinarith
  _ ≤ (n + 2) ^ k * (n + 2) ^ (e + 4) := Nat.mul_le_mul_left _ hP
  _ = (n + 2) ^ (k + e + 4) := by rw [← pow_add, ← Nat.add_assoc]

end CS

