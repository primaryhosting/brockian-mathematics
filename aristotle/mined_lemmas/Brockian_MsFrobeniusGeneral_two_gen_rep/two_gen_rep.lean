import Mathlib
namespace Brockian.MsFrobeniusGeneral

/-- Two-generator case: if `p` and `q` are coprime and `p > 0`, every `n ≥ p * q`
    is a nonnegative combination of `p` and `q`. -/

lemma two_gen_rep (p q n : ℕ) (hp : 0 < p) (hcop : Nat.Coprime p q) (hn : p * q ≤ n) :
    ∃ x y : ℕ, p * x + q * y = n := by
  by_cases hq : 0 < q
  · -- Both p and q are positive
    -- Use extended GCD to find a particular solution in integers
    have hgcd : (p : ℤ) * Int.gcdA p q + (q : ℤ) * Int.gcdB p q = 1 := by
      have hg : Int.gcd (p : ℤ) q = 1 := by simp [Int.gcd_natCast_natCast] at *; exact hcop
      linarith [Int.gcd_eq_gcd_ab p q]
    -- Get particular solution: p * (n * gcdA) + q * (n * gcdB) = n
    let x₀ := n * Int.gcdA p q
    let y₀ := n * Int.gcdB p q
    have hparticular : (p : ℤ) * x₀ + (q : ℤ) * y₀ = n := by
      calc (p : ℤ) * x₀ + (q : ℤ) * y₀ = (p : ℤ) * (n * Int.gcdA p q) + (q : ℤ) * (n * Int.gcdB p q) := rfl
        _ = n * ((p : ℤ) * Int.gcdA p q + (q : ℤ) * Int.gcdB p q) := by ring
        _ = n * 1 := by rw [hgcd]
        _ = n := by ring
    -- General solution: (x₀ + t*q, y₀ - t*p) for any integer t
    -- We need to find t such that x₀ + t*q ≥ 0 and y₀ - t*p ≥ 0
    -- Choose t = -⌊x₀/q⌋ to make x = x₀ + t*q = x₀ % q ∈ [0, q-1]
    let t := -(x₀ / q)
    let x' := x₀ + t * q
    let y' := y₀ - t * p
    have hx' : x' = x₀ % q := by
      show x₀ + (-(x₀ / q)) * q = x₀ % q
      linarith [Int.mul_ediv_add_emod x₀ q]
    -- x' ≥ 0 since x' = x₀ % q and q > 0
    have hx'_nonneg : 0 ≤ x' := by
      rw [hx']
      exact Int.emod_nonneg _ (by positivity)
    -- x' < q
    have hx'_lt_q : x' < q := by
      rw [hx']
      exact Int.emod_lt_of_pos _ (by positivity)
    -- Show p * x' + q * y' = n
    have hsum : (p : ℤ) * x' + (q : ℤ) * y' = n := by
      -- x' = x₀ + t*q, y' = y₀ - t*p
      -- p*x' + q*y' = p*(x₀ + t*q) + q*(y₀ - t*p) = p*x₀ + q*y₀ + p*t*q - q*t*p = p*x₀ + q*y₀ = n
      show (p : ℤ) * x' + (q : ℤ) * y' = n
      simp only [x', y']
      ring_nf
      rw [hparticular]
    -- Show y' ≥ 0: we have p*x' + q*y' = n, x' < q, so p*x' < p*q ≤ n, thus q*y' = n - p*x' > 0
    have hy'_nonneg : 0 ≤ y' := by
      have h1 : (p : ℤ) * x' < p * q := by nlinarith
      have h2 : (p : ℤ) * x' < n := by linarith
      have h3 : (q : ℤ) * y' = n - (p : ℤ) * x' := by linarith
      have h4 : (q : ℤ) * y' > 0 := by linarith
      nlinarith
    -- Convert to natural numbers
    use Int.toNat x', Int.toNat y'
    have hx'_eq : x' = Int.toNat x' := (Int.toNat_of_nonneg hx'_nonneg).symm
    have hy'_eq : y' = Int.toNat y' := (Int.toNat_of_nonneg hy'_nonneg).symm
    have hsum' : (p : ℤ) * (Int.toNat x') + (q : ℤ) * (Int.toNat y') = (n : ℤ) := by
      rw [← hx'_eq, ← hy'_eq]; exact hsum
    exact_mod_cast hsum'
  · -- q = 0, but then gcd(p, 0) = p ≠ 1 unless p = 1
    push_neg at hq
    interval_cases q
    simp at hcop
    -- q = 0 and gcd(p, 0) = 1 means p = 1
    subst hcop; exact ⟨n, 0, by simp⟩

/-- If `c` is coprime to `g > 0`, one can solve `c * z ≡ m [MOD g]` with `z < g`.
    (For `g = 1` take `z = 0`; otherwise take `z = (m * d) % g` where `d` is an inverse of `c`
    modulo `g`, obtained from `Nat.exists_mul_mod_eq_one_of_coprime`.) -/
