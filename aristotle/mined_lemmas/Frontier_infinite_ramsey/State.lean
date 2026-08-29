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

theorem State.colour_eq (s : State c) {i j : Nat} (hij : i < j) :
    c (s.a i) (s.a j) = s.bcol i := by
  have hj : (s.iter j).p (s.a j) := (s.iter j).pt_mem
  have h1 : (s.iter (i + 1)).p (s.a j) := s.iter_p_imp hij hj
  exact h1.1.2

