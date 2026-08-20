import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem exists_approx (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) [Fact q.Prime]
    [CharP F q] (ht : 1 ≤ t) :
    ∃ P : (Fin n → Bool) → F, P ∈ Deg F n (((q - 1) * t) ^ C.depth) ∧
      (univ.filter (fun x => P x ≠ ind F (C.eval q x))).card * 2 ^ t ≤ C.size * 2 ^ n := by
  obtain ⟨ρ, hρ⟩ := exists_good_rand F C q t
  exact ⟨gpoly F C q t ρ C.out,
    gpoly_mem_Deg F C (Nat.Prime.two_le Fact.out) ht ρ C.out, hρ⟩

end Circuit

end CS

/-
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Poly
import RequestProject.Binom
import RequestProject.Circuit
import RequestProject.Approx
import RequestProject.Lower
import RequestProject.Sanity

/-!
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- The field over which we approximate: an algebraic closure of `𝔽_q`. -/
noncomputable abbrev Fq (q : ℕ) [Fact q.Prime] := AlgebraicClosure (ZMod q)

instance FqCharP (q : ℕ) [Fact q.Prime] : CharP (Fq q) q :=
  inferInstanceAs (CharP (AlgebraicClosure (ZMod q)) q)

