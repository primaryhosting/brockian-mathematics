# The Pentagon as a Finite Selberg Machine — a plan

## One picture

Everything we have built is a single object seen through five lenses:

```
      cohomology            transfer operator          dynamical zeta
   H¹(C₅ ; A) = A     ⟷    T_c on ZMod 5 × A     ⟷    det(I − zT_c)
        │                        │                          │
        └──── gauge class ───────┴──── trace formula ───────┘
                     │                       │
              character variety        closed-orbit sum
              Hom(π₁,H)/H              Σ_orbits χ(holonomy)
```

The cocycle *is* a connection; its holonomy *is* the monodromy; the transfer determinant *is*
a Ruelle/Lefschetz zeta function; its trace *is* a Selberg-style sum over closed orbits; and the
gauge-invariant of the holonomy *is* a point of a character variety. We proved the C₅ column of
this diagram (classification, trace identity, D₅ covariance, the cycle-structure behind the zeta).

## What the no-go actually taught us — a precise diagnosis

The Phase-4 experiment did not say "phase-depth is empty." It said something sharp:

> On a single cycle with an **abelian** fiber, the holonomy is `H = ∑ c` — a **linear functional**
> of the data. Linear functionals of residue data are, by construction, low-order statistics.
> So the abelian single-cycle holonomy *cannot* exceed ≤3-point correlation information. It saw the
> Lemke Oliver–Soundararajan bias (a real, beyond-Fourier signal) and nothing past it.

Two structural facts are doing the killing: **(i) abelian** ⇒ holonomy is a sum ⇒ linear; **(ii) one
loop** ⇒ H¹(C₅;A)=A is one-dimensional ⇒ a single number. To carry genuinely new arithmetic
content the invariant must become **nonlinear** and **multi-dimensional**. Both escapes are already
latent in the corpus, and there is a choice that makes them *canonical*.

## The escape: path-ordered, multiplicative holonomy = a Frobenius symbol

Replace the abelian fiber `A` by a **nonabelian** group `H`. The holonomy is no longer a sum but a
**path-ordered product** `c(0)·c(1)·c(2)·c(3)·c(4)` — a *word*, sensitive to order, hence
intrinsically nonlinear (it encodes higher-order correlations the abelian sum washes out). Its
gauge-invariant is its **conjugacy class** in `H` (proved in miniature by `NonabelianOrderHolonomy`:
`b·a ≠ a·b`).

Now choose the cocycle from **multiplicative arithmetic data**: the Frobenius class of primes in a
Galois extension. Then the holonomy around a cycle is a product of Frobenii = an **Artin symbol** —
a conjugacy class in a Galois group. This is *not* a low-order residue statistic; it is a Galois-
theoretic object, so it escapes the no-go by construction, and its equidistribution/correlations are
governed by Chebotarev and Artin L-functions rather than by additive k-tuple heuristics.

**The unification that makes it elegant.** Pick the field so that its Galois group *is the pentagon's
own group* `D₅`. A dihedral quintic (Gal = D₅, order 10) exists; fix one in Step D. Then:

> the phase-depth `D₅` symmetry we already formalized **is** the Galois group, and the phase-depth
> holonomy **is** the Artin symbol. Geometry and arithmetic become the same object.

The transfer-operator spectrum then computes the **Artin L-function** of a `D₅`-representation, and
"where are the zeros of our finite zeta" becomes an honest finite shadow of the L-function's zeros.

## Five movements

Each is a real deliverable, ordered by dependency; difficulty and honesty stated.

**A. Close the zeta (Lean, tractable→moderate).** Prove the Lefschetz factorization
`det(I − z·P) = ∏_{ℓ ∈ cycleType σ} (1 − z^ℓ)` for a permutation matrix `P = permMatrix σ`. This is
the one lemma Mathlib lacks; supplying it upgrades our proved cycle-structure KEY into the full
`det(I − zT_c) = det(I − z⁵ρ(Hol))` — a clean dynamical-zeta identity — and is a **general,
Mathlib-worthy contribution** in its own right (the Euler product of a permutation's char-poly).

**B. The finite trace formula (Lean, tractable).** Prove `Tr(T_c^n) = Σ_{closed n-orbits} 1`, and its
character-weighted form `Tr(ρ ∘ T_c^n) = Σ_{prime cycles} (length)·χ(holonomy)`. This is the Selberg/
Ruelle trace formula in finite form — the literal bridge **holonomy ⟶ spectrum**. We already have the
period lemma and `trace = fixed-point count`; this assembles them into the trace formula.

**C. Nonabelian classification (Lean, moderate — finishes Phase 1's other half).** For fiber `H` and a
graph with `π₁ = F_r`: **gauge classes ≅ Hom(F_r, H)/conjugation**; for one loop (`r=1`), the
invariant is the **conjugacy class of the ordered product**. Prove `r=1` cleanly (the elegant
statement), then the branched pentagon (`r=2`) where the invariant becomes a genuine 2-dimensional
character-variety class — the multi-dimensional escape.

**D. The Frobenius cocycle (experiment + formalization — the creative core).** Fix a dihedral quintic
`f` with `Gal = D₅`. For primes `p` (unramified), compute the Frobenius conjugacy class
`Frob_p ∈ D₅` from the factorization type of `f mod p` (canonical, no tunable weights). Build the
`D₅`-valued cocycle; its holonomy is the Artin symbol. **Re-run the exact-k-order discrimination
harness** from Phase 4 on this *nonabelian, multiplicative* holonomy. Prediction: it escapes the
≤3-point bound, because Frobenius products are not additive residue statistics. Honest either way —
escape = a genuine arithmetic signal; no escape = a *deeper* no-go (the word-holonomy is still low-
order), which would itself be a sharp and surprising theorem. Formal companion: define `Frob_p` and
prove the holonomy = Artin symbol identity in Lean where feasible.

**E. The finite Riemann hypothesis (Lean, finite-model — Phase 6, honest).** With A+B, the zeros of the
finite zeta `det(I − zT_c)` sit at `z =` (roots of unity)/(eigenvalue moduli) — a provable finite
"RH on a circle." Connect to the Li-coefficient finite model already in the corpus and to the Artin
L-function of Step D. Presented strictly as **finite-set spectral geometry**, never as RH itself,
until an independent bridge to a global zero set exists.

## The crown (the falsifiable headline we are aiming at)

> **Claim to test:** for a dihedral quintic with `Gal = D₅`, the `D₅`-phase-depth holonomy over primes
> equals the Artin symbol, so the transfer-operator spectrum computes the `D₅`-Artin L-function, and
> its finite zero-statistics track the L-function's.

If it holds, the phase-depth machine *forces a genuine arithmetic consequence* (the top of the outcome
ladder). If Step D shows the word-holonomy is still low-order, we get the sharp no-go that says exactly
why — nonlinearity alone is not enough, and the obstruction is the next thing to name.

## Honest ladder

- **Provable now (A, B, C-r=1):** the zeta factorization, the finite trace formula, the nonabelian
  one-loop classification — clean Lean, AXLE-gated, general.
- **Research (C-r=2, D):** the branched character variety and the Frobenius-cocycle experiment — real
  uncertainty; a negative is as valuable as a positive.
- **Finite-model (E):** honest finite spectral geometry, not RH.

The decisive goal is unchanged: **one theorem that forces a new arithmetic consequence, or one no-go
that says precisely where the next construction must change.** This plan makes both outcomes reachable
and tells us, at Step D, which one we got.

## Immediate next step

Movement **A** (the Lefschetz determinant factorization) — it is tractable, it completes the zeta that
gives every other movement its language, and it is a standalone Mathlib-worthy lemma. Then **B**, then
in parallel launch the **D** experiment (which reuses the Phase-4 harness verbatim on a Frobenius
cocycle) so the decisive arithmetic question is answered while the formal spine is completed.
