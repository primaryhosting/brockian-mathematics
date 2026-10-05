import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex Finset

namespace Chem

/-- `Fin 19` carries the commutative ring structure of `ZMod 19`
(the two types, and their additive group structures, are definitionally equal). -/
noncomputable local instance : CommRing (Fin 19) := (inferInstance : CommRing (ZMod 19))

/-- A primitive 19-th root of unity. -/

lemma ec_add_ec_neg (k : Fin 19) : ec k + ec (-k) = lam k := by
  set t : ℝ := 2 * Real.pi * k.val / 19 with ht
  have h1 : ec k = Complex.exp ((t : ℂ) * Complex.I) := ec_eq_exp k
  have h2 : ec (-k) = Complex.exp (-(t : ℂ) * Complex.I) := by
    rw [ec_neg, h1, ← Complex.exp_neg]
    ring_nf
  rw [h1, h2, ← Complex.two_cos, lam, ← ht]
  push_cast
  ring

/-- The DFT matrix. -/
