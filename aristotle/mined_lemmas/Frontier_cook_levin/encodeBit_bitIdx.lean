import Mathlib
import RequestProject.Hardness

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Cook–Levin theorem

`SAT` is NP-complete:

* `SAT ∈ NP`, and
* every language in `NP` reduces to `SAT`.

Here languages are sets of bit strings; a language is in `NP` when it is decided by a
family of polynomial size Boolean circuits reading the input word together with a
witness word of polynomial length (`Frontier.InNP`).  `SAT` is the set of bit strings
whose associated CNF formula is satisfiable (`Frontier.SATlang`), the association being
the occurrence-matrix encoding of `Frontier.decodeCNF`.

The reductions produced here are *projections*: each output bit is a constant, or a bit
of the input word, or the negation of a bit of the input word, and the number of output
bits is polynomial in the length of the input word (`Frontier.IsProjectionReduction`).
In particular they are computable by polynomial size circuits.

The circuit families witnessing membership in `NP` are not required to be uniformly
generated, so `Frontier.InNP` is the non-uniform version of `NP`; correspondingly the
reductions produced by the hardness proof are non-uniform (but they are projections,
which is a much more restrictive class than polynomial time computable maps).
-/

namespace Frontier

/-- `L₁` reduces to `L₂` by a projection reduction. -/

theorem encodeBit_bitIdx (k : ℕ) (f : CNF ℕ) {i j : ℕ} (b : Bool) (hj : j < k) :
    encodeBit k f (bitIdx k i j b) = (f[i]?).elim true (fun c => decide ((j, b) ∈ c)) := by
  have hk : 0 < 2 * k := by omega
  obtain ⟨e, he, he1, hbe⟩ :
      ∃ e : ℕ, (if b then 0 else 1) = e ∧ e ≤ 1 ∧ decide ((2 * j + e) % 2 = 0) = b := by
    cases b
    · exact ⟨1, rfl, le_refl 1, by simp⟩
    · exact ⟨0, rfl, Nat.zero_le 1, by simp⟩
  have hsmall : 2 * j + e < 2 * k := by omega
  have hform : bitIdx k i j b = 2 * k * i + (2 * j + e) := by
    simp only [bitIdx, he]; ring
  have hdiv : bitIdx k i j b / (2 * k) = i := by
    rw [hform, Nat.mul_add_div hk, Nat.div_eq_of_lt hsmall]
    simp
  have hmod : bitIdx k i j b % (2 * k) = 2 * j + e := by
    rw [hform, Nat.mul_add_mod, Nat.mod_eq_of_lt hsmall]
  have hj2 : (2 * j + e) / 2 = j := by omega
  rw [encodeBit, hdiv, hmod, hj2, hbe]

/-- Two clauses with the same literals have the same value. -/
