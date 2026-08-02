# Why Five? — a machine-checked answer

*Every claim below resolves to a theorem in `registry/theorems.json` with a green
register. This document does not argue; it points at proofs.*

## The question

The golden ratio φ = (1+√5)/2 appears when you draw a regular pentagon: it is the
ratio of a diagonal to a side. It appears again, seemingly unrelated, in the *spectrum*
of the 5-cycle graph, in the *Galois theory* of the 5th roots of unity, and in the
*partition* generating function (Euler's pentagonal number theorem). A natural
suspicion is that these are not four coincidences but one fact wearing four costumes.

They are one fact. Here is the proof that they are.

## The four faces of five

For a cycle graph Cₙ the adjacency eigenvalues are exactly the circulant modes
2·cos(2πk/n) (`Brockian.CycleSpectrumFamily.mem_cycleSpectrum`). The pentagon's
fundamental mode is 2·cos(2π/5), and

> **2·cos(2π/5) = φ − 1.**
> `Brockian.CycleSpectrumFamily.two_cos_two_pi_div_five_eq_golden_sub_one`

That single trigonometric identity is the seam along which the costumes are stitched.
Follow it in each direction and the same number, φ − 1, forces the same integer, 5.

### The Grand Pentagon Equivalence

> For a prime p, **the following are equivalent**:
> 1. **p = 5** — the arithmetic face;
> 2. **φ − 1 ∈ spec(C_p)** — the spectral face (the golden value is a pentagon eigenvalue);
> 3. **[ℚ(2cos 2π/p) : ℚ] = 2** — the Galois face (the real cyclotomic field is *quadratic*);
> 4. **2cos(2π/p) = φ − 1** — the trigonometric face.
>
> `Brockian.PentagonGrandEquivalence.pentagon_grand_equivalence` — a 4-way `List.TFAE`,
> AXLE-verified at lean-4.32.0, axiom-clean.

The proof does not check four things four times. It routes a single strongly-connected
cycle of implications through the hub **p = 5**: p=5 forces the golden identity (face 4),
which puts φ − 1 in the spectrum (face 2, via the k=1 mode), which — by the spectral
uniqueness theorem — forces p=5 again; and p=5 makes the real cyclotomic degree
(p−1)/2 equal 2 (face 3), while degree 2 forces (p−1)/2 = 2, i.e. p ∈ {5,6}, and
primality kills 6. The degenerate prime p = 2 is dispatched cleanly: there
2cos(2π/2) = −2 is rational, so its Galois degree is 1, not 2 — every face is false
together, and the equivalence still holds.

Read plainly: **five is the unique prime whose defining rotation angle has a
golden-ratio cosine, equivalently the unique prime with a quadratic real cyclotomic
field.** That is *why* the pentagon, and nothing else prime, is golden.

### The Golden Divisibility Law

The prime statement is a shadow of a cleaner law that holds for *every* cycle:

> For every n ≥ 1, **φ − 1 ∈ spec(Cₙ) ⟺ 5 ∣ n.**
> `Brockian.GoldenDivisibility.golden_in_cycleSpectrum_iff_five_dvd` — full iff, both
> directions, AXLE-verified, axiom-clean.

The pentagon (n = 5) is the *smallest* golden cycle; the decagon, the 15-cycle, and
every fifth cycle thereafter inherit the golden mode, because a cycle of length 5j
carries the angle 2π/5 at its j-th mode. The celebrated prime result is now a
one-line corollary — `golden_unique_to_five_recovered` — obtained by noting that for a
prime, 5 ∣ p happens only at p = 5. A theorem that turns its famous special case into
a corollary has usually found the real reason, and this one has: the reason is
**divisibility by five**, not primality.

## What this is and is not

- It **is** a complete, independently machine-verified unification of the spectral,
  Galois, and trigonometric appearances of the golden ratio at the pentagon, with the
  arithmetic generalized to all cycles.
- It **is not** a claim about Euler's pentagonal number theorem. That result — proved
  unconditionally elsewhere in this core
  (`Brockian.FranklinFixedPoint.pentagonalNumberTheorem`) — concerns the *generalized
  pentagonal numbers* k(3k−1)/2, a genuinely different appearance of the pentagon. We
  keep the two stories apart on purpose: conflating them would be a fifth costume with
  no body inside it. One name, one object.

## Verification

Each theorem cited here was checked by AXLE (the independent verifier) at the pinned
environment lean-4.32.0, uses only the permitted axioms {`propext`, `Classical.choice`,
`Quot.sound`}, contains no `sorry`/`admit`/`native_decide`, and passes the
no-theater lint. The registry is derived mechanically from those attestations; nothing
here was hand-asserted. Regenerate and re-check with `python3 scripts/gen_registry.py`
and `python3 scripts/verify_firewall.py`.
