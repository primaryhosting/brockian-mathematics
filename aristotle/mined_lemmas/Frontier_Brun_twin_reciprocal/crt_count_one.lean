import Mathlib
import RequestProject.Brun.Final

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the required header comment appears immediately after the imports.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The summand is `1/n` whenever `n` and `n + 2` are both prime, and `0` otherwise; the value of
its sum is Brun's constant.  Convergence is proved from scratch by a Brun pure sieve; see the
development in `RequestProject/Brun/`. -/

lemma crt_count_one (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    #((range (a*b)).filter (fun n => a ∣ n ∧ b ∣ n + 2)) = 1 := by
  classical
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hab 0 (2*b - 2)
  have hka : a ∣ k := (Nat.modEq_zero_iff_dvd).1 hk1
  have hkb : b ∣ k + 2 := by
    have h2 : k + 2 ≡ (2*b - 2) + 2 [MOD b] := Nat.ModEq.add_right 2 hk2
    have h3 : (2*b - 2) + 2 = 2*b := by omega
    rw [h3] at h2
    exact (Nat.modEq_zero_iff_dvd).1 (h2.trans ((Nat.modEq_zero_iff_dvd).2 ⟨2, by ring⟩))
  set x := k % (a*b) with hx
  have hxlt : x < a*b := Nat.mod_lt _ (by positivity)
  have hxa : a ∣ x := by
    have h : x ≡ k [MOD a] := (Nat.mod_modEq k (a*b)).of_dvd ⟨b, rfl⟩
    exact (Nat.modEq_zero_iff_dvd).1 (h.trans ((Nat.modEq_zero_iff_dvd).2 hka))
  have hxb : b ∣ x + 2 := by
    have h : x + 2 ≡ k + 2 [MOD b] :=
      Nat.ModEq.add_right 2 ((Nat.mod_modEq k (a*b)).of_dvd ⟨a, by ring⟩)
    exact (Nat.modEq_zero_iff_dvd).1 (h.trans ((Nat.modEq_zero_iff_dvd).2 hkb))
  rw [Finset.card_eq_one]
  refine ⟨x, ?_⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨by simp [Finset.mem_filter, Finset.mem_range, hxlt, hxa, hxb], ?_⟩
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_range] at hy
  obtain ⟨hylt, hya, hyb⟩ := hy
  have key : ∀ u v : ℕ, v < a*b → a ∣ u → b ∣ u + 2 → a ∣ v → b ∣ v + 2 → u ≤ v → u = v := by
    intro u v hv hua hub hva hvb huv
    have h1 : a ∣ v - u := Nat.dvd_sub hva hua
    have h2 : b ∣ v - u := by
      have := Nat.dvd_sub hvb hub
      simpa [Nat.add_sub_add_right] using this
    have h3 : a*b ∣ v - u := Nat.Coprime.mul_dvd_of_dvd_of_dvd hab h1 h2
    have h5 : v - u = 0 := by
      rcases Nat.eq_zero_or_pos (v - u) with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd h h3) (by omega)
    omega
  rcases le_total y x with h | h
  · exact (key y x hxlt hya hyb hxa hxb h)
  · exact (key x y hylt hxa hxb hya hyb h).symm

/-- Counting `n < N` in a fixed pair of coprime congruence classes. -/
