# Public mathematical claims

16 September 2026. These are the statements supported by the stated definitions
and analytic inputs. Compilation status is reported separately in REVIEW.md.

## Approved description

The Brockian program studies finite residue symmetries, cyclic Fourier analysis,
observer-dependent holonomy, and arithmetic scattering. Its zeta function is
ζ_B(s)=(1−5^(−s))ζ(s), the Dirichlet L-function of the principal character
modulo 5. In the open strip 0<Re(s)<1, the extra factor is nonzero, so RH for
ζ_B in that strip is equivalent to the ordinary Riemann Hypothesis.

With the standard width-one normalization at the two cusps of Y₀(5), the
Eisenstein scattering matrix has two Fricke channels. A nontrivial zeta zero
ρ gives a scattering resonance at s=ρ/2, through the common denominator
ζ(2s). This is a continuous-spectrum scattering description. The cusp-swap
symmetry used here is C₂. The golden ratio occurs in five-cycle Fourier
algebra and in Q(√5)=Q(ζ₅)⁺. No D₅ action on Y₀(5) or proof of RH is claimed.

## Exact normalization behind the description

Write x=5^(−s) and
φ₀(s)=√π Γ(s−1/2)ζ(2s−1)/(Γ(s)ζ(2s)). Then

\[
\Phi_5=\frac{\phi_0}{1-x^2}
\begin{pmatrix}4x^2&x(1-5x^2)\\x(1-5x^2)&4x^2\end{pmatrix},
\quad
\phi_+=\phi_0\frac{x(1+5x)}{1+x},\quad
\phi_-=\phi_0\frac{x(5x-1)}{1-x}.
\]

Thus det Φ₅ = φ₀² x²(25x²−1)/(1−x²). Both channels carry the nontrivial
ζ-zero poles; they do not assign all such zeros to one parity. For a strip
zero ρ of multiplicity m, each channel has pole order m and the determinant
has order 2m at ρ/2. Here the local factors are regular and nonzero and
ζ(ρ−1) does not cancel the denominator. These analytic facts are distinct
from the rational matrix identities formalized in Lean.

The local denominator poles at x=(−1)^k occur in the Fricke-even factor when
k is odd and in the odd factor when k is even. Before asserting an actual
meromorphic pole, include φ₀ and check cancellation; s=0 requires care.
The extra zeros of ζ_B on Re(s)=0 are excluded from the RH_B statement.

The analytic input is the meromorphic Eisenstein constant term, with the
cusp normalization above. See [Young, *Explicit calculations with Eisenstein
series*](https://arxiv.org/pdf/1710.03624), and [Kaneko–Koyama, Remark 1.1,
equation (1.2)](https://arxiv.org/pdf/1909.09174) for the prime-level change
of basis. In `channels_of_constant_term` it remains the named hypothesis
`hEisensteinConstantTerm`; algebraic compilation does not certify that input.

## Claims requiring correction if reused

| Earlier shorthand | Accurate scope |
|---|---|
| "Eigenvalues are the zeta zeros" | The identification used here concerns scattering poles at half the zero parameter |
| "Fricke symmetry supplies D₅ on Y₀(5)" | The two-cusp swap supplies C₂; a different group action would need an explicit construction |
| "Golden ratio is a unit length" | It is an algebraic unit and a finite-cycle spectral quantity; a metric length needs its own definition |
| "The observer recovers gcd or h, with nothing between" | The combined observer (gcd(h,8), h mod 4) is strictly between gcd alone and labelled h |
| "Exact pilots are formal theorems" | Finite examples and uncompiled skeletons are separate evidence levels |
| "A positive cutoff trace proves Weil positivity" | The required global primitive sign and limiting identity need independent theorems |
| "All second-order operators fail the counting test" | The Weyl law must be stated for a specified operator, domain and spectral parameter |

## Badge policy

Use a kernel-checked description only after exact source compilation and an
axiom audit. Keep named analytic/geometric hypotheses visible. The repository's
PROVED register additionally requires its existing independent attestation
gate. A proposed FORMAL_THEOREM label must not be used to bypass that gate.
An exact `decide` witness is finite computation under the repository policy;
it does not promote a general unproved statement.
