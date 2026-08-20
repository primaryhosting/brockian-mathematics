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

theorem tseitin_vars (c : Circuit) : ∀ k : Nat,
    VarsIn (tseitin c k).cls k (tseitin c k).next := by
  induction c with
  | var i => intro k cl hcl; simp [tseitin] at hcl
  | tru =>
      intro k cl hcl l hl j hj
      simp only [tseitin, List.mem_cons, List.not_mem_nil, or_false] at hcl hl ⊢
      subst hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [Sum.inr.injEq] at hj
      omega
  | fls =>
      intro k cl hcl l hl j hj
      simp only [tseitin, List.mem_cons, List.not_mem_nil, or_false] at hcl hl ⊢
      subst hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [Sum.inr.injEq] at hj
      omega
  | neg a ih =>
      intro k cl hcl l hl j hj
      simp only [tseitin] at hcl ⊢
      exact ih k cl hcl l hl j hj
  | conj a b iha ihb =>
      intro k cl hcl l hl j hj
      have hva := iha k
      have hvb := ihb (tseitin a k).next
      have h1 := tseitin_next_ge a k
      have h2 := tseitin_next_ge b (tseitin a k).next
      have hoa := tseitin_out_var a k j
      have hob := tseitin_out_var b (tseitin a k).next j
      simp only [tseitin, List.mem_cons, List.mem_append] at hcl ⊢
      rcases hcl with rfl | rfl | rfl | hcl | hcl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · simp only [negLit, Sum.inr.injEq] at hj; omega
        · have := hoa hj; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · simp only [negLit, Sum.inr.injEq] at hj; omega
        · have := hob hj; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · simp only [Sum.inr.injEq] at hj; omega
        · have := hoa (by simpa [negLit] using hj); omega
        · have := hob (by simpa [negLit] using hj); omega
      · have := hva cl hcl l hl j hj; omega
      · have := hvb cl hcl l hl j hj; omega
  | disj a b iha ihb =>
      intro k cl hcl l hl j hj
      have hva := iha k
      have hvb := ihb (tseitin a k).next
      have h1 := tseitin_next_ge a k
      have h2 := tseitin_next_ge b (tseitin a k).next
      have hoa := tseitin_out_var a k j
      have hob := tseitin_out_var b (tseitin a k).next j
      simp only [tseitin, List.mem_cons, List.mem_append] at hcl ⊢
      rcases hcl with rfl | rfl | rfl | hcl | hcl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · simp only [negLit, Sum.inr.injEq] at hj; omega
        · have := hoa hj; omega
        · have := hob hj; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · simp only [Sum.inr.injEq] at hj; omega
        · have := hoa (by simpa [negLit] using hj); omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · simp only [Sum.inr.injEq] at hj; omega
        · have := hob (by simpa [negLit] using hj); omega
      · have := hva cl hcl l hl j hj; omega
      · have := hvb cl hcl l hl j hj; omega

