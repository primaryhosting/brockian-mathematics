import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/

lemma card_sols_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    (sols (m * n)).card = (sols m).card * (sols n).card := by
  rw [← Finset.card_product]
  refine Finset.card_bij' (i := fun r _ => (r % m, r % n))
    (j := fun p _ => (Nat.chineseRemainder h p.1 p.2 : ℕ)) ?_ ?_ ?_ ?_
  · intro r hr
    obtain ⟨hrlt, hrdvd⟩ := mem_sols.mp hr
    rw [Finset.mem_product]
    refine ⟨mem_sols.mpr ⟨Nat.mod_lt _ hm, ?_⟩, mem_sols.mpr ⟨Nat.mod_lt _ hn, ?_⟩⟩
    · exact dvd_of_modEq (Nat.mod_modEq r m) ((dvd_mul_right m n).trans hrdvd)
    · exact dvd_of_modEq (Nat.mod_modEq r n) ((dvd_mul_left n m).trans hrdvd)
  · intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, hd1⟩ := mem_sols.mp hp.1
    obtain ⟨hp2, hd2⟩ := mem_sols.mp hp.2
    have hcr := (Nat.chineseRemainder h p.1 p.2).2
    refine mem_sols.mpr ⟨Nat.chineseRemainder_lt_mul h p.1 p.2 hm.ne' hn.ne', ?_⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h (dvd_of_modEq hcr.1 hd1) (dvd_of_modEq hcr.2 hd2)
  · intro r hr
    obtain ⟨hrlt, hrdvd⟩ := mem_sols.mp hr
    have hcr := (Nat.chineseRemainder h (r % m) (r % n)).2
    have hkm : (Nat.chineseRemainder h (r % m) (r % n) : ℕ) ≡ r [MOD m] :=
      hcr.1.trans (Nat.mod_modEq r m)
    have hkn : (Nat.chineseRemainder h (r % m) (r % n) : ℕ) ≡ r [MOD n] :=
      hcr.2.trans (Nat.mod_modEq r n)
    have hmn := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨hkm, hkn⟩
    have hlt := Nat.chineseRemainder_lt_mul h (r % m) (r % n) hm.ne' hn.ne'
    rw [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hrlt] at hmn
    exact hmn
  · intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, _⟩ := mem_sols.mp hp.1
    obtain ⟨hp2, _⟩ := mem_sols.mp hp.2
    have hcr := (Nat.chineseRemainder h p.1 p.2).2
    have e1 : (Nat.chineseRemainder h p.1 p.2 : ℕ) % m = p.1 := by
      have h1 := hcr.1
      rw [Nat.ModEq, Nat.mod_eq_of_lt hp1] at h1
      exact h1
    have e2 : (Nat.chineseRemainder h p.1 p.2 : ℕ) % n = p.2 := by
      have h2 := hcr.2
      rw [Nat.ModEq, Nat.mod_eq_of_lt hp2] at h2
      exact h2
    exact Prod.ext e1 e2

/-- The number of solutions of `r (r + 2) ≡ 0 (mod d)`, as an arithmetic function. -/
