/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is self-contained (no imports): it builds, from scratch,

* propositional formulas in conjunctive normal form (CNF) and satisfiability,
* Boolean circuits (as formulas over a fixed set of input variables),
* the Tseitin transformation from circuits to CNF, with its correctness proof
  and a linear size bound,
* the notion of an `NP` verifier (a polynomial-size circuit family together
  with a polynomially bounded witness length),

and proves the Cook–Levin theorem in the following form.

`Frontier.cook_levin`: every language `L` admitting a polynomial-size circuit
verifier reduces to `SAT` by an (explicitly constructed, hence computable)
map `f` such that `x ∈ L ↔ f x` is satisfiable, and the size of `f x` is
bounded by a polynomial in the length of `x`.

`Frontier.sat_in_np`: conversely, `SAT` itself lies in `NP`: a CNF `c` is
satisfiable iff there is a witness (a Boolean word of length the number of
variables of `c`) accepted by a circuit of size linear in `c`, which is
constructed from `c` by the explicit map `cnfCircuit`.

## Scope

Membership in `NP` is formalised here through *verifier circuits* rather than
through Turing machines: a language is in `NP` when there are a circuit family
`V` of polynomially bounded size and a witness-length function `m` such that
`V n` accepts exactly the pairs (input of length `n`, witness of length `m n`)
that certify membership. The step which is proved is therefore the
circuit-satisfiability core of Cook–Levin (the Tseitin translation of an
arbitrary verifier circuit into an equisatisfiable CNF of linear size, together
with the hard-wiring of the input), and not the simulation of a
polynomial-time Turing machine by a polynomial-size circuit family. All
constructions here are explicit computable functions, and the size bounds are
proved, not assumed.
-/

namespace Frontier

/-! ## Polynomial bounds -/

/-- A function `Nat → Nat` is polynomially bounded. The shifted base `n+1`
avoids degenerate behaviour at `n = 0`. -/

theorem tseitin_sound (c : Circuit) : ∀ (k : Nat) (σ : Nat ⊕ Nat → Bool),
    cnfEval σ (tseitin c k).cls = true →
    litEval σ (tseitin c k).out = c.eval (fun i => σ (Sum.inl i)) := by
  induction c with
  | var i => intro k σ _; simp [tseitin, Circuit.eval]
  | tru =>
      intro k σ h
      simp only [tseitin, cnfEval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
        Bool.or_false, litEval_mk_true, Bool.and_true] at h
      simp [tseitin, Circuit.eval, h]
  | fls =>
      intro k σ h
      simp only [tseitin, cnfEval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
        Bool.or_false, litEval_mk_false, Bool.and_true, Bool.not_eq_eq_eq_not,
        Bool.not_true] at h
      simp [tseitin, Circuit.eval, h]
  | neg a ih =>
      intro k σ h
      simp only [tseitin] at h ⊢
      rw [litEval_negLit, ih k σ h]
      rfl
  | conj a b iha ihb =>
      intro k σ h
      simp only [tseitin, cnfEval, List.all_cons, List.all_append, List.any_cons, List.any_nil,
        Bool.or_false, Bool.and_eq_true, litEval_negLit, litEval_mk_true] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have ea := iha k σ h4
      have eb := ihb (tseitin a k).next σ h5
      simp only [tseitin, Circuit.eval, litEval_mk_true, ← ea, ← eb]
      revert h1 h2 h3
      generalize σ (Sum.inr (tseitin b (tseitin a k).next).next) = G
      generalize litEval σ (tseitin a k).out = A
      generalize litEval σ (tseitin b (tseitin a k).next).out = B
      revert A B G
      decide
  | disj a b iha ihb =>
      intro k σ h
      simp only [tseitin, cnfEval, List.all_cons, List.all_append, List.any_cons, List.any_nil,
        Bool.or_false, Bool.and_eq_true, litEval_negLit, litEval_mk_true] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have ea := iha k σ h4
      have eb := ihb (tseitin a k).next σ h5
      simp only [tseitin, Circuit.eval, litEval_mk_true, ← ea, ← eb]
      revert h1 h2 h3
      generalize σ (Sum.inr (tseitin b (tseitin a k).next).next) = G
      generalize litEval σ (tseitin a k).out = A
      generalize litEval σ (tseitin b (tseitin a k).next).out = B
      revert A B G
      decide

/-- Update an assignment at a single gate variable. -/
