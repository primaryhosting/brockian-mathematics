/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` to precede any module docstring, so the header above is a
plain block comment; the same text is repeated as the module docstring below.)
-/

import Mathlib

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## What is formalised here

The statement "there are problems with no fastest algorithm" is formalised as follows.

* `CS.BlumMeasure` is a Blum complexity measure on a programming system: an effective
  numbering of the partial computable functions (`sem_partrec`, `sem_complete`) together with a
  cost function satisfying Blum's two axioms, namely that the cost of a run is defined exactly
  when the run converges (`cost_dom`) and that the graph of the cost function is computable
  (`cost_decidable`).
* `CS.blum` is such a measure. Its semantics is the standard one: a program is a pair `(c, k)`
  of a code `c` in the standard system `Nat.Partrec.Code` and a *compression level* `k`, and it
  computes the function computed by `c`. Its cost is the number of steps of `c` (the least fuel
  making `Nat.Partrec.Code.evaln` converge) recorded on the scale of the `k`-th branch of the
  Ackermann function; at level `0` this is exactly the step count (`CS.scaledCost_level_zero`),
  and along any program the cost still tends to infinity (`CS.scaledCost_unbounded`).
* `CS.hardProblem` is a `0-1` valued computable problem which is arbitrarily hard for the
  standard step count: every algorithm for it exceeds any prescribed primitive recursive time
  bound on infinitely many inputs (`CS.hardProblem_hard_of_primrec`).
* `CS.blum_speedup` combines these: there is a Blum complexity measure and a (hard) decision
  problem such that every algorithm for the problem is beaten, by any prescribed primitive
  recursive factor and on almost every input, by another algorithm for the same problem.

## Scope

Blum's original speedup theorem is stronger in two respects: it holds for *every* Blum
complexity measure (in particular for the standard step count) and for every total computable
speedup factor, at the price of a much more delicate construction of the problem. What is proved
here is the existential statement, for an explicitly constructed Blum measure and primitive
recursive speedup factors; in that measure `CS.blum_no_fastest` shows that in fact no problem
has a fastest algorithm.
-/

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ## Blum complexity measures -/

/-- A *Blum complexity measure* on a programming system whose semantics is given by
`sem : Prog → ℕ →. ℕ`.

* `sem_partrec` says that the programming system is effective (there is a universal machine);
* `sem_complete` says that every partial computable function is computed by some program
  (so the system really is a programming system for the partial computable functions);
* `cost_dom` is Blum's first axiom: the cost of a run is defined exactly when the run converges;
* `cost_decidable` is Blum's second axiom: the graph of the cost function is computable. -/
structure BlumMeasure (Prog : Type) [Primcodable Prog] where
  /-- semantics: the partial function computed by a program -/
  sem : Prog → ℕ →. ℕ
  /-- the cost (running time) of a program on an input -/
  cost : Prog → ℕ →. ℕ
  sem_partrec : Partrec₂ sem
  sem_complete : ∀ f : ℕ →. ℕ, Partrec f → ∃ p, sem p = f
  cost_dom : ∀ p n, (cost p n).Dom ↔ (sem p n).Dom
  cost_decidable : ∃ D : Prog × ℕ × ℕ → Bool, Computable D ∧
      ∀ p n m, (D (p, n, m) = true ↔ m ∈ cost p n)

variable {Prog : Type} [Primcodable Prog]

/-- Program `q` beats program `p` by the factor `r`: on almost every input, applying `r` to the
cost of `q` still does not exceed the cost of `p`. -/

theorem computable_costDecide : Computable costDecide := by
  have hc : Computable fun x : (Code × ℕ) × ℕ × ℕ => x.1.1 := Computable.fst.comp Computable.fst
  have hn : Computable fun x : (Code × ℕ) × ℕ × ℕ => x.2.1 := Computable.fst.comp Computable.snd
  have hk : Computable fun x : (Code × ℕ) × ℕ × ℕ => x.1.2 := Computable.snd.comp Computable.fst
  have hm : Computable fun x : (Code × ℕ) × ℕ × ℕ => x.2.2 := Computable.snd.comp Computable.snd
  have hA : Computable fun x : (Code × ℕ) × ℕ × ℕ => ack x.1.2 x.2.2 - 1 :=
    Primrec.nat_sub.to_comp.comp (computable₂_ack.comp hk hm) (Computable.const 1)
  have hB : Computable fun x : (Code × ℕ) × ℕ × ℕ => ack x.1.2 (x.2.2 + 1) - 1 :=
    Primrec.nat_sub.to_comp.comp
      (computable₂_ack.comp hk (Computable.succ.comp hm)) (Computable.const 1)
  have hpA : Computable fun x : (Code × ℕ) × ℕ × ℕ => ((x.1.1, x.2.1), ack x.1.2 x.2.2 - 1) :=
    (hc.pair hn).pair hA
  have hpB : Computable fun x : (Code × ℕ) × ℕ × ℕ =>
      ((x.1.1, x.2.1), ack x.1.2 (x.2.2 + 1) - 1) := (hc.pair hn).pair hB
  have h1 := primrec_halts.to_comp.comp hpB
  have h2 := primrec_halts.to_comp.comp hpA
  have h3 : Computable fun x : (Code × ℕ) × ℕ × ℕ => (x.2.2 == 0) :=
    ((Primrec.nat_casesOn (Primrec.snd.comp Primrec.snd) (Primrec.const true)
      ((Primrec.const false).to₂)).of_eq (by intro x; cases h : x.2.2 <;> simp)).to_comp
  have h4 := (Primrec.dom_bool (!·)).to_comp.comp h2
  have h5 := (Primrec.dom_bool₂ (· || ·)).to_comp.comp h3 h4
  exact (Primrec.dom_bool₂ (· && ·)).to_comp.comp h1 h5

