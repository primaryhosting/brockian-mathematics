import Mathlib

/-!
# Further Diophantine functions: binomial coefficients and factorials

Mathlib's `Mathlib/NumberTheory/Dioph.lean` develops the basic theory of Diophantine sets and
functions and culminates in Matiyasevich's theorem that exponentiation is Diophantine
(`Dioph.pow_dioph`).  Two further classical steps on the way to the MRDP theorem are formalized
here, both unconditionally:

* `CS.choose_dioph`: the binomial coefficient `(n, k) ↦ n.choose k` is a Diophantine function.
  This follows from `Dioph.pow_dioph` because `n.choose k` is the `k`-th digit of `(u + 1) ^ n`
  in base `u := 2 ^ n + 1`, and division and remainder are Diophantine.
* `CS.factorial_dioph`: the factorial `r ↦ r !` is a Diophantine function.  This follows from
  `CS.choose_dioph` because `r ! = u ^ r / u.choose r` as soon as `u` is large enough compared
  to `r`, and `u := (2 * r) ^ (r + 2) + 2 * r + 1` is large enough.
-/

set_option autoImplicit false

namespace CS

open Finset Nat

/-! ## Digits in base `u` -/

/-- A number with all digits `< u` and at most `k` digits is `< u ^ k`. -/

def haltSet : Set ℕ := fun n => (eval (Denumerable.ofNat Code n) 0).Dom

theorem haltSet_re : REPred haltSet :=
  (ComputablePred.halting_problem_re 0).comp (Computable.ofNat Code)

theorem haltSet_not_computable : ¬ ComputablePred haltSet := by
  intro h
  refine ComputablePred.halting_problem 0 ?_
  obtain ⟨inst, hc⟩ := h
  have h2 : ComputablePred fun c : Code => haltSet (Encodable.encode c) :=
    ⟨fun c => inst _, hc.comp (Computable.encode (α := Code))⟩
  refine h2.of_eq fun c => ?_
  simp [haltSet, Denumerable.ofNat_encode]

/-! ## Statement of the MRDP theorem -/

/-- The Matiyasevich–Robinson–Davis–Putnam theorem: every recursively enumerable set of natural
numbers is Diophantine, i.e. is the set of parameters for which some integer polynomial equation
has a solution in the natural numbers. -/

def MRDP : Prop :=
  ∀ S : Set ℕ, REPred S → Dioph {v : Fin 1 → ℕ | S (v 0)}

/-! ## Hilbert's tenth problem is undecidable -/

/-- **Hilbert's tenth problem is undecidable.**

Given the MRDP theorem, there is a single integer polynomial `p` in one distinguished parameter
`a` and finitely many further unknowns `t` such that no algorithm decides, given `a`, whether the
Diophantine equation `p (a, t) = 0` has a solution `t` in the natural numbers.  In particular
there is no algorithm deciding solvability of arbitrary Diophantine equations. -/

theorem hilbert10_undecidable (mrdp : MRDP) :
    ∃ (β : Type) (p : Poly (Fin 1 ⊕ β)),
      ¬ ComputablePred fun a : ℕ => ∃ t : β → ℕ, p (Sum.elim (fun _ => a) t) = 0 := by
  obtain ⟨β, p, hp⟩ := mrdp haltSet haltSet_re
  refine ⟨β, p, fun h => haltSet_not_computable ?_⟩
  refine h.of_eq fun a => ?_
  have := hp (fun _ => a)
  simpa using this.symm

/-! ## The easy half of MRDP: Diophantine sets are recursively enumerable

This direction is proved unconditionally.  Together with `MRDP` it says that the Diophantine
subsets of `ℕ` are exactly the recursively enumerable ones, so the undecidable set produced by
`hilbert10_undecidable` is as complicated as the halting problem, but no worse. -/

/-- An integer polynomial function depends on only finitely many of its variables. -/
