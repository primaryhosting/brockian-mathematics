/-
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Local operations performed by Alice on her half of a bipartite (possibly entangled)
system cannot change Bob's reduced state, hence cannot transmit any information.

The bipartite system is modelled by matrices indexed by `A × B` over `ℂ`
(`A` = Alice's factor, `B` = Bob's factor).  Alice's local operation is an
arbitrary quantum channel given in Kraus form by operators `K i` acting on her
factor only, i.e. `K i ⊗ I`, subject to trace preservation `∑ i, (K i)ᴴ * K i = 1`.
Bob's reduced state is the partial trace over Alice's factor.
-/

namespace Frontier

open scoped Matrix
open Finset

variable {A B ι : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype ι]

/-- Partial trace over the first (Alice) factor of a bipartite operator:
Bob's reduced state. -/

private theorem sum_comm4 {f : A → ι → A → A → ℂ} :
    (∑ a, ∑ i, ∑ e, ∑ c, f a i e c) = ∑ c, ∑ e, ∑ i, ∑ a, f a i e c := by
  rw [show (∑ a, ∑ i, ∑ e, ∑ c, f a i e c) = ∑ x : A × ι × A × A, f x.1 x.2.1 x.2.2.1 x.2.2.2 by
        simp [Fintype.sum_prod_type],
      show (∑ c, ∑ e, ∑ i, ∑ a, f a i e c) = ∑ y : A × A × ι × A, f y.2.2.2 y.2.2.1 y.2.1 y.1 by
        simp [Fintype.sum_prod_type]]
  exact Fintype.sum_equiv
    { toFun := fun x : A × ι × A × A => (x.2.2.2, x.2.2.1, x.2.1, x.1),
      invFun := fun y : A × A × ι × A => (y.2.2.2, y.2.2.1, y.2.1, y.1),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun _ => rfl)

/-- **No-communication theorem** (finite-dimensional, Kraus form).

Alice applies an arbitrary quantum operation to her half of a bipartite state `ρ`,
described by Kraus operators `K i` acting on her factor only (tensored with the
identity on Bob's factor) and satisfying the trace-preservation condition
`∑ i, (K i)ᴴ * K i = 1`.  Then Bob's reduced state, the partial trace over
Alice's factor, is completely unchanged: no information can be transmitted. -/
