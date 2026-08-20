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

theorem reduction_size (V : Nat → Circuit) (x : List Bool) :
    cnfSize (reduction V x) ≤ 10 * (V x.length).size + 2 * x.length + 2 := by
  have hts := tseitin_size (V x.length) 0
  have hlast : cnfSize [[(tseitin (V x.length) 0).out]] = 2 := by simp [cnfSize]
  simp only [reduction, cnfSize_cnfMap, cnfSize_append, cnfSize_inputClauses, hlast]
  omega

/-! ## Cook–Levin -/

/--
**Cook–Levin theorem** (NP-hardness of SAT).

Let `L` be a language of Boolean words which is verified by a family of Boolean
circuits `V` of polynomially bounded size, with polynomially bounded witness
length `m`: `x ∈ L` iff there is a witness `w` of length `m |x|` such that the
circuit `V |x|`, evaluated on the input bits of `x` followed by the bits of `w`,
outputs `true`.

Then `L` reduces to `SAT`: there is a map `f` from words to CNF formulas,
explicitly constructed (hence computable relative to `V`), such that `x ∈ L`
iff `f x` is satisfiable, and the size of `f x` is polynomially bounded in the
length of `x`.
-/
