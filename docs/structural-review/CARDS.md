# Structural cards: claim-by-claim evidence

These cards describe the review branch, not an inspected copy of packet v5.
The reported 69 tests and 13 pilots are not build receipts. The final receipt
index and remaining promotion gates are in REVIEW.md. Each card has separate
mathematical, kernel, and external-attestation statuses.

## E18 — Fricke channels explain the prime-level scattering factor

**Question:** what does level 5 contribute after the common level-one factor?

**Object:** a symmetric 2×2 matrix over a characteristic-zero field, scalar a,
level p, and coordinate x. Analytically a=φ₀(s), x=p^(−s).

**Claim:** r₊=x(1+px)/(1+x), r₋=x(px−1)/(1−x);
Φ=a r₊P₊+a r₋P₋; det Φ=a²x²(p²x²−1)/(1−x²). The regular-domain factors
satisfy r(x)r(1/(px))=1. The elementary local denominator at (−1)^k selects
the even channel iff k is odd. Nonzero numerators are checked separately.

**Lean:** `FrickeChannelAlgebra.lean`, including denominator conditions,
projector algebra, determinant and the transfer theorem
`channels_of_constant_term`.

**Dependency boundary:** the Eisenstein identification is a named hypothesis;
no analytic continuation, gamma-factor cancellation or scattering theorem is
silently imported as an axiom. The Lean parity statement uses k∈N; extension
to negative lattice indices and the analytic pole statement are separate.

**Explanation earned:** cusp symmetry is C₂ and both channels carry ζ(2s).
This arithmetic factorization survives if RH is false. Promotion is per
compiled algebraic statement; the analytic application stays conditional.

## E19 — The invariant depends on the observer

**Question:** what information about seam holonomy survives a specified observation?

**Object:** q,m≥1, the seam permutation on Z/q×Z/m, and labelled quotient
observers π on the depth group.

**Written theorem:** for g=gcd(m,h), every orbit has length q(m/g), so
det(I−zP_h)=(1−z^(q(m/g)))^g. The determinant detects g; the residue marginal
detects no h. A quotient observer detects π(h). Proof: HOLONOMY_PROOF.md.

**Lean:** `HolonomyObservers.lean` proves general observer equivalence,
kernel classification, coarsening, iterated loop translations, and loop return
order m/g. The explicit finite witness at m=8 is proved by kernel-checked
finite computation. `HolonomySeam.lean` connects these loop translations to
the actual one-step map and proves the general return-time equivalence:
P_h^n(x)=x iff q(m/g) divides n.
The compound observer (gcd(h,8),h mod 4) strictly refines gcd and is weaker
than labelled h. Quotient h mod 4 alone is not a refinement of gcd globally.

**Open formalization:** `SeamDeterminantStatement` is a Prop container, not
a theorem. The remaining bridge after the seam return-time theorem is the
uniform cycle decomposition and the cycle-block determinant proof in Lean. Checking
three parameter pairs does not fill this gap.

**Explanation earned:** the former "nothing in between" assertion is withdrawn.
The observer theorem can be promoted independently of the determinant target.

## E20 / E01 — One finite Fourier lemma supports two applications

**Question:** which structure is shared by the finite D₅ projectors and cycle Hamiltonians?

**Object:** functions on Z/N, N>0, standard additive characters, shifts and
reflection. The Hückel operator is αI+β(T+T⁻¹).

**Claims:** character orthogonality; complete rank-one Fourier projectors;
P_kP_l=δ_kl P_k on every function; ΣP_k=I; RTR=T⁻¹; Fourier eigenvalues
α+β(χ(k)+χ(−k)). N=5 and N=13 are specializations, not separate numerical proofs.

**Lean:** `CyclicFourierStructure.lean` is the generic interface.
`D5FourierBridge.lean` identifies its modes and projectors with the existing
five-vertex representation. `CyclePolynomialCertificates.lean` proves exact
factor identities for fifth and thirteenth roots. `CycleOperatorPolynomials.lean`
uses Fourier completeness to transfer those identities to the operator and
its complex coordinate matrix.

**Polynomial explanation:** for t=x+x⁻¹,

\[
(t-2)(t^2+t-1)=\frac{(x-1)(x^5-1)}{x^3},
\quad
(t-2)\Psi(t)=\frac{(x-1)(x^{13}-1)}{x^7},
\]

where Ψ(t)=t⁶+t⁵−5t⁴−4t³+6t²+3t−1. These certificates give annihilators.
For N=5, the five complex modes group over R as 1+2+2; the two nonconstant
eigenvalues are (−1±√5)/2. The quadratic factor of the integer adjacency
matrix is proved to be the all-ones matrix, with rank exactly one: a
one-column factorization gives the upper bound and a nonzero 1×1 minor gives
the lower bound. Irreducibility/minimality of Ψ and the real irreducible
decomposition still require their own formal statements.

**Scope:** the operator identities are proved over C and transferred to
integer adjacency matrices through the injective coefficient map Z→C. The
five-cycle quadratic-factor identity is also checked directly in the kernel.
This supplies separate repository proofs of the integer identities; it does
not reproduce the unavailable v5 test suite. No modular-surface D₅ action follows.

## E21 — The finite-field template locates the sign theorem

**Question:** which geometric fact makes a Weil bound follow without forcing zeros?

**Object:** primitive numerical divisor classes on C×C. The Frobenius graph
projects to D_i=Γ_i−H−q^iV. The sign comes from Hodge index for H+V.

**Written result:** FINITE_FIELD_TEMPLATE.md derives all intersections, the
Gram matrix, the bound for every extension degree, and the root-modulus
conclusion with rationality and functional equation stated separately. It
includes explicit curves over F_5 and audits the reported v5 data conditionally
on those point counts. The diagonal convention is N_0=2−2g.

**Lean:** `HodgeGramAlgebra.lean` proves the real algebra following the supplied
Gram sign. It does not produce the geometric sign. Its application is labelled
conditional on `hHodgeGramSign`.

**Arithmetic gate:** Connes–Consani's construction is evaluated against six
roles. The needed primitive pairing and index/sign theorem are not exhibited
in the reviewed manuscript. Status: SIGN_GATE_UNMET.

**Priority interpretation:** E21 can be the lab's highest-priority card because
it makes the decisive hypothesis visible. A catalog score expresses chosen
weights; it is not mathematical evidence that this route is closer to RH.
