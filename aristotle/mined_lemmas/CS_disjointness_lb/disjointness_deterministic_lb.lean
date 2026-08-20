import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

We formalize deterministic two-party communication protocols as protocol trees
(`CS.Protocol`), with `CS.Protocol.run` the output and `CS.Protocol.cost` the worst-case number
of exchanged bits, and prove the fooling-set bound `CS.Protocol.card_fooling_le`: a protocol of
cost `c` admits no fooling set of size larger than `2 ^ c`.

Applying it to the fooling set `{(x, xᶜ) : x ⊆ [n]}` for set disjointness gives

* `CS.disjointness_deterministic_lb`: every deterministic protocol computing set disjointness on
  subsets of an `n`-element universe costs at least `n` bits;
* `CS.disjointness_lb_of_success` and `CS.disjointness_lb`: every *public-coin randomized*
  protocol with perfect soundness (it never answers "disjoint" on an intersecting pair) that
  answers "disjoint" with probability at least `1/2` (more generally `δ`) on each disjoint pair
  costs at least `n - 1` bits (more generally `δ * 2 ^ n ≤ 2 ^ c`).  Hence set disjointness has
  `Ω(n)` randomized communication complexity in the one-sided-error model.
* `CS.disjointness_ub`: a matching deterministic protocol of cost `n + 1`, so the bounds are
  tight up to an additive constant and the hypotheses above are satisfiable.

The randomized lower bound proved here is for the one-sided-error (perfectly sound) model; the
two-sided bounded-error case (Kalyanasundaram–Schnitger, Razborov) is not formalized here.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CS

universe u v

/-- A deterministic two-party communication protocol with Boolean output.
`alice f t e` means Alice sends the bit `f x` and the parties continue with `t` or `e`;
`bob g t e` is the same with Bob speaking. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf (b : Bool) : Protocol X Y
  | alice (f : X → Bool) (t e : Protocol X Y) : Protocol X Y
  | bob (g : Y → Bool) (t e : Protocol X Y) : Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The output of the protocol on the input pair `(x, y)`. -/

theorem disjointness_deterministic_lb {n : ℕ} (P : Protocol (Finset (Fin n)) (Finset (Fin n)))
    (hP : ∀ x y, P.run x y = Disj n x y) : n ≤ P.cost := by
  classical
  have hT : (Finset.univ.image (fun x : Finset (Fin n) => (x, xᶜ))).card ≤ 2 ^ P.cost := by
    refine Protocol.card_fooling_le P _ ?_ ?_
    · intro p hp
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
      obtain ⟨x, rfl⟩ := hp
      simp [hP, Disj, disjoint_compl_right]
    · intro p hp q hq hne
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp hq
      obtain ⟨x, rfl⟩ := hp
      obtain ⟨z, rfl⟩ := hq
      have hxz : x ≠ z := by
        intro h; exact hne (by rw [h])
      rcases cross_not_disjoint hxz with h | h
      · exact Or.inl (by simp [hP, Disj, h])
      · exact Or.inr (by simp [hP, Disj, h])
  have hcard : (Finset.univ.image (fun x : Finset (Fin n) => (x, xᶜ))).card = 2 ^ n := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg Prod.fst hab)]
    simp [Fintype.card_finset]
  rw [hcard] at hT
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hT

/-- The trivial protocol in which Alice reveals membership in `x` of each element of the list
`L` (accumulating the revealed elements of `x` in `a`), after which Bob announces the answer. -/
