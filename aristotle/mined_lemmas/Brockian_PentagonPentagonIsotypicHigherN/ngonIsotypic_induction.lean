import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires every `import` to precede any module docstring, so the header
-- comment above sits immediately after the single `import Mathlib` line.

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The vertex space of the regular `n`-gon: complex-valued functions on the vertex
set `ZMod n`.  The dihedral group `D_n` acts on it through the rotation `ngonShift`
and the reflection `ngonRefl`. -/
abbrev NGon (n : ℕ) : Type := ZMod n → ℂ

/-- Rotation of the `n`-gon by `t` vertices, acting on functions by translation. -/

lemma ngonIsotypic_induction {j : ZMod n} {p : NGon n → Prop} (hzero : p 0)
    (hadd : ∀ a b, p a → p b → p (a + b)) (hsmul : ∀ (c : ℂ) a, p a → p (c • a))
    (hj : p ⇑(ngonChar n j)) (hj' : p ⇑(ngonChar n (-j)))
    {f : NGon n} (hf : f ∈ ngonIsotypic n j) : p f := by
  refine Submodule.span_induction (p := fun x _ => p x) ?_ hzero (fun a b _ _ => hadd a b)
    (fun c a _ => hsmul c a) hf
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact hj
  · exact hj'

