/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The two-colour Ramsey number `R(4,4)` equals `18`.

Mathlib (at the pinned revision) contains no theory of Ramsey numbers, so the whole
argument is developed here:

* the classical upper bound `R(p+1,q+1) ≤ R(p,q+1) + R(p+1,q)` (`Math.arrow_step`),
* `R(3,3) ≤ 6` and, via the parity/degree argument, `R(3,4) ≤ 9`
  (`Math.arrow_three_three`, `Math.arrow_three_four`), giving `R(4,4) ≤ 18`,
* the Paley graph on 17 vertices, which has neither a 4-clique nor a 4-element
  independent set, giving `R(4,4) > 17`.
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

/-! ## A relation-theoretic formulation of Ramsey's theorem for two colours -/

variable {V : Type*}

/-- A finite set `t` is homogeneous for the relation `r` if all distinct pairs of elements
of `t` are related by `r`. -/

lemma paley_no_mono (t : Finset (Fin 17)) (ht : t.card = 4) :
    ¬ Homog (fun a b => qrAdj a b = true) t ∧ ¬ Homog (fun a b => ¬ (qrAdj a b = true)) t := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := card_eq_four ht
  have ma : a ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have mb : b ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have mc : c ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have md : d ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  constructor
  · intro hh
    exact paley_no_red_four a b c d hab hac had hbc hbd hcd
      ⟨hh a ma b mb hab, hh a ma c mc hac, hh a ma d md had, hh b mb c mc hbc,
       hh b mb d md hbd, hh c mc d md hcd⟩
  · intro hh
    refine paley_no_blue_four a b c d hab hac had hbc hbd hcd
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Bool.not_eq_true] at hh
    · exact hh a ma b mb hab
    · exact hh a ma c mc hac
    · exact hh a ma d md had
    · exact hh b mb c mc hbc
    · exact hh b mb d md hbd
    · exact hh c mc d md hcd

/-! ## The main theorem -/

/-- The Ramsey number `R(4,4)` equals `18`: `18` is the least `N` such that every
graph on `N` vertices contains a clique of size 4 or an independent set of size 4
(i.e. a 4-clique of the complement). -/
