/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A predicate on `Nat` is `Unbounded` when it holds arbitrarily far out; for subsets of `Nat`
this is exactly the same as being infinite. -/

theorem enum_strictMono {p : Nat → Prop} (hp : Unbounded p) {i j : Nat} (hij : i < j) :
    enum hp i < enum hp j := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases h : i < j
      · exact Nat.lt_trans (ih h) (enum_lt_succ hp j)
      · have : i = j := by omega
        subst this
        exact enum_lt_succ hp i

/-- **Infinite Ramsey theorem** (pairs, two colours).  For every colouring
`c : Nat → Nat → Bool` of the pairs `{i, j} ⊆ Nat` (a pair `i < j` gets colour `c i j`) there is an
infinite set `S ⊆ Nat` — presented as an unbounded predicate on `Nat` — and a colour `b` such that
every pair from `S` has colour `b`. -/
