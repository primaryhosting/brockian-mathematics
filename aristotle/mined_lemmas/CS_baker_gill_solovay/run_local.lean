/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.BGSModel

/-!
## Basic properties of the machine model

* costs and query lists only grow;
* the cost of a run does not depend on the cost already accumulated (`run_shift`);
* every recorded query has length at most the cost, and there are at most `cost`
  many queries (`run_QInv`);
* locality: a run only depends on the oracle at the strings it queries
  (`run_local`).
-/

namespace CS.BGS

variable {O O' : Oracle} {st : State} {i : ℕ} {s : Str} {a b c e : Expr}

/-! ### Unfolding lemmas -/


lemma run_local {O O' : Oracle} (p : Prog) (st : State)
    (h : ∀ q ∈ (run O p st).qs, O' q = O q) : run O' p st = run O p st := by
  induction p generalizing st with
  | skip => simp
  | assign i e =>
      have := evalE_local (O := O) (O' := O') e st (fun q hq => h q (by simpa using hq))
      simp only [run_assign, this]
  | seq p q ihp ihq =>
      have ha : run O' p st = run O p st := by
        refine ihp st (fun q hq => h q ?_)
        exact run_qs_mono O q (run O p st) hq
      simp only [run_seq, ha]
      exact ihq (run O p st) (fun q hq => h q hq)
  | ite c t f iht ihf =>
      have hc : evalE O' c st = evalE O c st := by
        refine evalE_local c st (fun q hq => h q ?_)
        rw [run_ite]
        split
        · exact run_qs_mono O f _ hq
        · exact run_qs_mono O t _ hq
      rw [run_ite, run_ite, hc]
      rw [run_ite] at h
      split
      · exact ihf _ (fun q hq => h q (by simp_all))
      · exact iht _ (fun q hq => h q (by simp_all))
  | loop c body ih =>
      have hmono : ∀ (m : ℕ) (s' : State), s'.qs ⊆ ((run O body)^[m] s').qs :=
        fun m s' => iter_qs_mono O body (run_qs_mono O body) m s'
      have key : ∀ (n : ℕ) (s : State), (∀ q ∈ ((run O body)^[n] s).qs, O' q = O q) →
          (run O' body)^[n] s = (run O body)^[n] s := by
        intro n
        induction n with
        | zero => intro s _; simp
        | succ n ihn =>
            intro s hs
            rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
            have h1 : run O' body s = run O body s := by
              refine ih s (fun q hq => hs q ?_)
              rw [Function.iterate_succ_apply]
              exact hmono n (run O body s) hq
            rw [h1]
            refine ihn _ (fun q hq => hs q ?_)
            rw [Function.iterate_succ_apply]
            exact hq
      have hc : evalE O' c st = evalE O c st := by
        refine evalE_local c st (fun q hq => h q ?_)
        rw [run_loop]
        exact hmono _ _ hq
      rw [run_loop, run_loop, hc]
      refine key _ _ (fun q hq => h q ?_)
      rw [run_loop]
      exact hq

end CS.BGS

/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## A model of polynomial-time oracle computation

We fix a concrete, self-contained machine model: a small imperative language over
bit strings with variables, concatenation, the "smash" function
`x # y = 0^(|x|·|y|)`, string equality, bounded iteration (`loop`), conditionals,
and an oracle query primitive.  Every operation is charged a cost which is at
least the length of the value it produces, so that the cost of a run bounds both
the number of oracle queries and the length of every query.  This is a faithful
cost model for polynomial time (it is a "for"-loop language with the standard
Cobham primitives).

`P^O` and `NP^O` are then defined in the usual way.
-/

namespace CS.BGS

/-- Bit strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings, presented as its characteristic function. -/
abbrev Oracle := Str → Bool

/-- Expressions of the machine language. -/
inductive Expr : Type
  | var (i : ℕ) : Expr
  | lit (s : Str) : Expr
  | cat (a b : Expr) : Expr
  /-- `smash a b` is the all-zero string of length `|a| * |b|`. -/
  | smash (a b : Expr) : Expr
  | tail (a : Expr) : Expr
  /-- `eqE a b` is `[true]` if the two values are equal, `[]` otherwise. -/
  | eqE (a b : Expr) : Expr
  /-- `query a` is `[true]` if the value of `a` is in the oracle, `[]` otherwise. -/
  | query (a : Expr) : Expr
  deriving DecidableEq

/-- Programs of the machine language. -/
inductive Prog : Type
  | skip : Prog
  | assign (i : ℕ) (e : Expr) : Prog
  | seq (a b : Prog) : Prog
  | ite (c : Expr) (t f : Prog) : Prog
  /-- `loop c body` runs `body` exactly `|c|` times (`c` is evaluated once, first). -/
  | loop (c : Expr) (body : Prog) : Prog
  deriving DecidableEq

/-- A machine state: the values of the variables, the cost incurred so far, and the
list of oracle queries made so far. -/
structure State where
  vars : ℕ → Str
  cost : ℕ
  qs : List Str

/-- Update a variable assignment. -/
