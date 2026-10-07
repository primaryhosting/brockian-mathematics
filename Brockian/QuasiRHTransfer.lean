import Mathlib

/-!
# The Brockian zeta function and the θ-transfer of zero-free half-planes

`ζ_B(s) = (1 − 5^{−s}) ζ(s)` — the Riemann zeta function with its Euler factor at 5
removed; equivalently (`zetaB_eq_LFunctionTrivChar`) Mathlib's L-function of the
principal Dirichlet character mod 5.

This module is **Mathlib-only**.  Its job is to be the single trust boundary through which
an external zero-free half-plane for `ζ` enters the Brockian corpus: the external theorem
is a *hypothesis* of `zetaB_ne_zero_of_zeroFree` (the `θ`-parametrised transfer), never an
`axiom`, following the `formal/Zeta23Scaffold` discipline.  The instantiation at
`θ = 7/8` from openai/math family 003 lives outside the kernel-checked corpus in
`formal/QuasiRH003/Import003.lean`, because it imports that project's `OAI` library.

Instantiations of `θ`:
* `θ = 1`   — `zetaB_ne_zero_of_one_lt_re`, proved here from Mathlib's
  `riemannZeta_ne_zero_of_one_le_re`;
* `θ = 7/8` — openai/math 003 (`formal/QuasiRH003/`), pending kernel check;
* `θ = 1/2` — the Riemann Hypothesis.

The converse transfer `riemannZeta_ne_zero_of_zetaB_zeroFree` records the honest position
of the programme: any zero-free half-plane proved for `ζ_B` is the same half-plane for `ζ`.
Removing the Euler factor at 5 does not make the problem easier.

Audit of the external input: `writeups/openai-math-003-quasi-rh-audit.md`.
-/

open Complex

noncomputable section

namespace Brockian.QuasiRHTransfer

/-- The Brockian zeta function `ζ_B(s) = (1 − 5^{−s}) ζ(s)`. -/
def zetaB (s : ℂ) : ℂ := (1 - (5 : ℂ) ^ (-s)) * riemannZeta s

/-! ### The Euler factor at 5 -/

/-- `‖5^{−s}‖ = 5^{−Re s}`. -/
theorem norm_five_cpow_neg (s : ℂ) : ‖(5 : ℂ) ^ (-s)‖ = (5 : ℝ) ^ (-s.re) := by
  have h := Complex.norm_natCast_cpow_of_pos (n := 5) (by norm_num) (-s)
  simpa [Complex.neg_re] using h

/-- For `Re s > 0`, `‖5^{−s}‖ < 1`. -/
theorem norm_five_cpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) : ‖(5 : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_five_cpow_neg]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- The Euler factor `1 − 5^{−s}` does not vanish for `Re s > 0`.  This is the whole
content of the transfer: on the critical strip, multiplying by it neither creates nor
destroys zeros. -/
theorem eulerFactor_five_ne_zero {s : ℂ} (hs : 0 < s.re) : (1 : ℂ) - (5 : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (5 : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hlt := norm_five_cpow_neg_lt_one hs
  rw [h1, norm_one] at hlt
  exact lt_irrefl _ hlt

/-! ### Zeros of `ζ_B` are zeros of `ζ`, and conversely, on `Re s > 0` -/

/-- On `Re s > 0` the zero sets of `ζ_B` and `ζ` coincide. -/
theorem zetaB_eq_zero_iff {s : ℂ} (hs : 0 < s.re) : zetaB s = 0 ↔ riemannZeta s = 0 := by
  unfold zetaB
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h5 | hζ
    · exact absurd h5 (eulerFactor_five_ne_zero hs)
    · exact hζ
  · intro h
    rw [h, mul_zero]

/-! ### Identification with Mathlib's L-function of the principal character mod 5 -/

/-- Away from `s = 1`, `ζ_B` is Mathlib's `DirichletCharacter.LFunctionTrivChar 5`, the
analytically continued L-function of the principal character mod 5.  Through this bridge
an external *Dirichlet* zero-free theorem applies to `ζ_B` directly, independently of the
corresponding `ζ` theorem. -/
theorem zetaB_eq_LFunctionTrivChar {s : ℂ} (hs : s ≠ 1) :
    zetaB s = DirichletCharacter.LFunctionTrivChar 5 s := by
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs, Nat.prime_five.primeFactors,
    Finset.prod_singleton]
  simp [zetaB]

/-! ### The `θ`-parametrised transfer -/

/-- Transfer `ζ → ζ_B`: a zero-free half-plane `Re s > θ` for `ζ`, with `0 ≤ θ`, is one for
`ζ_B`.  The external input enters only as the hypothesis `hζ`. -/
theorem zetaB_ne_zero_of_zeroFree (θ : ℝ) (hθ : 0 ≤ θ)
    (hζ : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0)
    {s : ℂ} (hs : θ < s.re) : zetaB s ≠ 0 := by
  unfold zetaB
  exact mul_ne_zero (eulerFactor_five_ne_zero (lt_of_le_of_lt hθ hs)) (hζ s hs)

/-- Transfer `ζ_B → ζ`: any zero-free half-plane proved for `ζ_B` is the same half-plane
for `ζ`.  Removing the Euler factor at 5 does not weaken the problem. -/
theorem riemannZeta_ne_zero_of_zetaB_zeroFree (θ : ℝ)
    (hB : ∀ s : ℂ, θ < s.re → zetaB s ≠ 0)
    {s : ℂ} (hs : θ < s.re) : riemannZeta s ≠ 0 := by
  intro h
  apply hB s hs
  unfold zetaB
  rw [h, mul_zero]

/-- Instantiation at `θ = 1` from Mathlib alone: `ζ_B(s) ≠ 0` for `Re s > 1`. -/
theorem zetaB_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : zetaB s ≠ 0 :=
  zetaB_ne_zero_of_zeroFree 1 zero_le_one
    (fun _ hs' => riemannZeta_ne_zero_of_one_le_re hs'.le) hs

/-! ### Reflection of zeros

Only the easy direction of the functional equation is needed to turn a half-plane
`Re s > θ` into a strip `1 − θ ≤ Re ρ ≤ θ`: if `ζ(ρ) = 0` with `0 < Re ρ < 1` then
`ζ(1 − ρ) = 0`.  The nonvanishing of the Gamma/cosine prefactor is not required for this
direction. -/

/-- If `ζ(ρ) = 0` and `0 < Re ρ < 1`, then `ζ(1 − ρ) = 0`. -/
theorem riemannZeta_one_sub_eq_zero_of_eq_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hρ : riemannZeta ρ = 0) : riemannZeta (1 - ρ) = 0 := by
  have hne : ∀ n : ℕ, ρ ≠ -n := by
    intro n hn
    have hre : ρ.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hne1 : ρ ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have hfe := riemannZeta_one_sub hne hne1
  rw [hρ, mul_zero] at hfe
  exact hfe

/-- The `θ`-parametrised strip: a zero-free half-plane `Re s > θ` for `ζ` with `θ < 1`
confines every zero of `ζ_B` in the critical strip to `1 − θ ≤ Re ρ ≤ θ`. -/
theorem zetaB_zero_strip_of_zeroFree (θ : ℝ)
    (hζ : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hρ : zetaB ρ = 0) :
    1 - θ ≤ ρ.re ∧ ρ.re ≤ θ := by
  have hζρ := (zetaB_eq_zero_iff h0).mp hρ
  have hfe := riemannZeta_one_sub_eq_zero_of_eq_zero h0 h1 hζρ
  constructor
  · by_contra hlt
    push_neg at hlt
    have hre : θ < (1 - ρ).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact hζ _ hre hfe
  · by_contra hlt
    push_neg at hlt
    exact hζ ρ hlt hζρ

end Brockian.QuasiRHTransfer

end
