import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math2

open NumberField

section NumberFields

variable (L : Type*) [Field L] [NumberField L]

/-- The group of `ℤ`-algebra automorphisms of the ring of integers of a number field is
finite. -/

lemma isArithFrobAt_apply_zetaInt {p : ℕ} (hpn : ¬ p ∣ n) {Q : Ideal (𝓞 L)}
    (hQ : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) {f : 𝓞 L ≃ₐ[ℤ] 𝓞 L}
    (hf : IsArithFrobAt ℤ f Q) : f (zetaInt n L) = zetaInt n L ^ p := by
  have hpow : (zetaInt n L) ^ n = 1 := (zetaInt_isPrimitiveRoot n L).pow_eq_one
  have hmem : ((n : ℕ) : 𝓞 L) ∉ Q := by
    intro hmem
    have hn : ((n : ℤ)) ∈ Ideal.under ℤ Q := by
      simpa [Ideal.under, Ideal.mem_comap] using hmem
    rw [hQ, Ideal.mem_span_singleton] at hn
    exact hpn (by exact_mod_cast hn)
  have hfz := hf.apply_of_pow_eq_one hpow hmem
  have hcard : Nat.card (ℤ ⧸ Ideal.under ℤ Q) = p := by
    rw [hQ, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  rw [hcard] at hfz
  simpa using hfz

variable (n L)

include n in
/-- **Chebotarev density theorem** (qualitative form, for cyclotomic extensions of `ℚ`).

Let `n ≥ 1`, let `L = ℚ(ζₙ)` be an `n`-th cyclotomic field and let `G = 𝓞L ≃ₐ[ℤ] 𝓞L` be its
Galois group, acting on the ring of integers `𝓞L`.  Then for every `σ ∈ G` there are infinitely
many rational primes `p` whose Frobenius conjugacy class is the conjugacy class of `σ`: there is
a prime `Q` of `𝓞L` above `p` at which `σ` itself is an arithmetic Frobenius element, and at
*every* prime `Q` of `𝓞L` above `p` some conjugate of `σ` is an arithmetic Frobenius element. -/
