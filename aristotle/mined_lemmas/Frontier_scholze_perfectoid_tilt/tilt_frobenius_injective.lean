/-
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The tilt: inverse limit along Frobenius -/

section Tilt

variable (p : ℕ) (R : Type*) [CommRing R] [Fact p.Prime] [CharP R p]

/-- The **tilt** of a commutative ring `R` of characteristic `p`: the inverse limit
`lim_{x ↦ x^p} R`, realised as the subring of sequences `f : ℕ → R` satisfying
`f (n+1) ^ p = f n`. -/

theorem tilt_frobenius_injective : Function.Injective (frobenius (Tilt p R) p) := by
  intro f g h
  have hcoe : ∀ n, ((f : ℕ → R) n) ^ p = ((g : ℕ → R) n) ^ p := by
    intro n
    have := congrArg (fun x : Tilt p R => (x : ℕ → R) n) h
    simpa [frobenius_def, Tilt.coe_pow] using this
  apply Subtype.ext
  funext n
  calc (f : ℕ → R) n = ((f : ℕ → R) (n + 1)) ^ p := (f.2 n).symm
    _ = ((g : ℕ → R) (n + 1)) ^ p := hcoe (n + 1)
    _ = (g : ℕ → R) n := g.2 n

/-- Frobenius is surjective on the tilt. -/
