import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

theorem parity_lower_bound (N ℓ d : ℕ) (hℓ : 0 < ℓ)
    (hbig : 64 * ((2 * ℓ) ^ d + 1) ^ 2 ≤ 3 * N + 1)
    (c : Circuit (2 * N)) (hd : c.DepthLe d) (hcomp : c.Computes (parity (2 * N)))
    (hsize : 4 * c.size ≤ 2 ^ ℓ) : False := by
  classical
  set D := (2 * ℓ) ^ d with hDdef
  obtain ⟨q, hqd, B, hB, hqv⟩ := circuit_approx c d ℓ hℓ hd
  set A : Finset (Cube (2 * N)) := Finset.univ \ B with hA
  have hBsub : B ⊆ Finset.univ := Finset.subset_univ B
  have hAcard : A.card = 2 ^ (2 * N) - B.card := by
    rw [hA, Finset.card_univ_diff, card_cube]
  have hBle : B.card ≤ 2 ^ (2 * N) := by
    have := Finset.card_le_card hBsub
    rwa [Finset.card_univ, card_cube] at this
  -- the low degree function agreeing with parity on `A`
  set R : Cube (2 * N) → ZMod 3 := (fun _ => 1) + q with hR
  have hRd : R ∈ Deg (2 * N) D := Submodule.add_mem _ (const_mem_Deg _ _) hqd
  have hRA : ∀ x ∈ A, R x = mon (Finset.univ : Finset (Fin (2 * N))) x := by
    intro x hx
    have hxB : x ∉ B := (Finset.mem_sdiff.mp hx).2
    have hval := hqv x hxB
    rw [c.computes_value hcomp x] at hval
    simp only [hR, Pi.add_apply, hval]
    rw [mon_univ_eq_sgn_parity, sgn_eq_one_add_bit]
  have hsmol := card_le_of_approximates_parity (N := N) (D := D) rfl A R hRd hRA
  -- the exceptional set is small
  have h1 : 4 * B.card ≤ 2 ^ (2 * N) := by
    have hpos : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc 2 ^ ℓ * (4 * B.card) = 4 * (2 ^ ℓ * B.card) := by ring
      _ ≤ 4 * (c.size * 2 ^ (2 * N)) := Nat.mul_le_mul_left _ hB
      _ = (4 * c.size) * 2 ^ (2 * N) := by ring
      _ ≤ 2 ^ ℓ * 2 ^ (2 * N) := Nat.mul_le_mul_right _ hsize
  -- the central binomial coefficient is small
  have h2 : 8 * ((D + 1) * (2 * N).choose N) ≤ 2 ^ (2 * N) := by
    have hcb : ((2 * N).choose N) ^ 2 * (3 * N + 1) ≤ 16 ^ N := centralBinom_sq_mul_le N
    have hsq : (8 * ((D + 1) * (2 * N).choose N)) ^ 2 ≤ (2 ^ (2 * N)) ^ 2 := by
      have e1 : (8 * ((D + 1) * (2 * N).choose N)) ^ 2
          = (64 * (D + 1) ^ 2) * ((2 * N).choose N) ^ 2 := by ring
      have e2 : (16 : ℕ) ^ N = (2 ^ (2 * N)) ^ 2 := by
        rw [← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
        ring_nf
      calc (8 * ((D + 1) * (2 * N).choose N)) ^ 2
          = (64 * (D + 1) ^ 2) * ((2 * N).choose N) ^ 2 := e1
        _ ≤ (3 * N + 1) * ((2 * N).choose N) ^ 2 := Nat.mul_le_mul_right _ hbig
        _ = ((2 * N).choose N) ^ 2 * (3 * N + 1) := by ring
        _ ≤ 16 ^ N := hcb
        _ = (2 ^ (2 * N)) ^ 2 := e2
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hsq
  have h3 := sum_range_choose_le N D
  have h4 : 0 < 2 ^ (2 * N) := Nat.two_pow_pos _
  omega

/-- If `ℓ ^ k` is eventually dominated by `2 ^ ℓ`. -/
