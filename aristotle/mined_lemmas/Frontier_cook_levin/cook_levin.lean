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

theorem cook_levin
    (L : List Bool → Prop) (V : Nat → Circuit) (m : Nat → Nat)
    (hvars : ∀ n, (V n).VarsBelow (n + m n))
    (hsize : IsPolyBound (fun n => (V n).size))
    (hV : ∀ x : List Bool, L x ↔ ∃ w : List Bool, w.length = m x.length ∧
        (V x.length).eval (fun i => (x ++ w).getD i false) = true) :
    ∃ (f : List Bool → CNF Nat) (g : Nat → Nat),
      (∀ x, L x ↔ Sat (f x)) ∧ IsPolyBound g ∧ ∀ x, cnfSize (f x) ≤ g x.length := by
  refine ⟨reduction V, fun n => 10 * (V n).size + 2 * n + 2, fun x => ?_, ?_,
    fun x => reduction_size V x⟩
  · rw [hV x, reduction_correct V m hvars x]
  · exact isPolyBound_add (isPolyBound_add (isPolyBound_mul_const 10 hsize)
      (isPolyBound_mul_const 2 isPolyBound_linear)) (isPolyBound_const 2)

/-! ## SAT belongs to NP -/

/-- The circuit computing the value of a literal. -/
