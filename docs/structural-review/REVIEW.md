# Structural review: proofs, evidence and remaining gates

16 September 2026. Review branch: `review/structural-core-2026-09-16`.
[Draft PR #13](https://github.com/primaryhosting/brockian-mathematics/pull/13).
Base: `ed95b048e7e5ecb6513326766b9efafeaba506aa`.

This review turns the explanatory statements into proof terms where completed,
and records the boundary of each result. It does not prove RH. Packet v5 was
not available among the supplied archives or retrievable files; its reported
69 tests and 13 pilots have not been reproduced here. The changes below belong
to the repository review branch, not to an edited copy of that archive.

## Deliverables

| Item | Deliverable | Boundary |
|---|---|---|
| Explanatory core | [Cards](CARDS.md), eight new Lean modules, source-bound CI receipts | The full E19 determinant theorem remains a written proof and explicit formalization target |
| Finite-field template | [Full derivation and six-role gate](FINITE_FIELD_TEMPLATE.md) | Hodge index is a named geometric input; the arithmetic counterpart is not constructed |
| Route discipline | [Route ledger](ROUTE_LEDGER.md) | Li remains parked; the precise positive-rate exclusion region replaces the overbroad no-intermediate-range slogan |
| Corpus and public claims | [Public language](PUBLIC_CLAIMS.md), [Weyl triage](WEYL_TRIAGE.md), [repair script](../../scripts/repair_import_order.sh) | No merge or registry promotion without the existing independent-attestation gate |

## Kernel evidence

The pinned compiler is Lean 4.32.0 with Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`. The checker passes
`-DautoImplicit=false`, compiles committed source without normalization, and
probes every named theorem in the nine selected structural modules (eight new
modules plus the existing QFT control). Missing axiom reports fail the check.
The permitted axiom set is only `propext`, `Classical.choice`, and `Quot.sound`.
No new axiom, `sorry`, or native-decider trust extension is introduced.

**Core check passed:** 21 modules compiled and all 82 theorem declarations in
the nine audited modules passed their axiom probes. See the
[receipt](receipts/core/receipt.json) and
[CI run 35161974557](https://github.com/primaryhosting/brockian-mathematics/actions/runs/35161974557).
The checked branch head was `663ae2b2c83da1dcf42198ca5441ed8e93b5e847`;
the PR merge commit was `713efb02adb1d5e0d085b540dbf42de6d030b94d`.
Every recorded source hash and the manifest hash match the delivered files.
The [receipt index](receipts/README.md) identifies the retained artifacts.

| Audited module | Named theorem declarations | Content |
|---|---:|---|
| FrickeChannelAlgebra | 17 | Rational channels, determinant, functional equations, projectors and parity |
| CyclicFourierStructure | 16 | Orthogonality, complete projectors, reflection and Hückel modes |
| D5FourierBridge | 5 | Identifies the generic projectors with the existing finite representation |
| CyclePolynomialCertificates | 7 | Exact scalar certificates for fifth and thirteenth roots |
| CycleOperatorPolynomials | 14 | Operator/matrix annihilation, integer transfer and the rank-one factor |
| HolonomyObservers | 12 | Observer kernels, coarsening, loop translations and intermediate witnesses |
| HolonomySeam | 7 | General seam iteration and exact return times |
| HodgeGramAlgebra | 3 | Algebra after a supplied Gram sign |
| QCQFTUnitary, existing control | 1 | Unnormalized Fourier matrix identity |

These counts concern declarations, including elementary supporting lemmas and
finite computational witnesses. They are not counts of novel research results
or newly promoted registry entries.

The four original import-order failures compile after moving their imports:
`SieveSpectrumDeletion`, `SieveSpectrumCounts`, `SieveSpectrumBlocks`, and
`OddPerfectThreePrimes`. The repair script creates a review branch and commits
only those fixes. It never changes attestations or merges.

The Weyl diagnostic closure improved from **23/27 to 27/27 compiled modules**.
The four additional repairs resolve namespaces and notation; the statements
are preserved. Evidence: [before](receipts/weyl-before/receipt.json),
[after](receipts/weyl-after/receipt.json), and
[passing diagnostic run](https://github.com/primaryhosting/brockian-mathematics/actions/runs/35159492433).
These are compilation receipts; the Weyl diagnostic did not run theorem-level
axiom probes. The early receipt's generic scope string should be read with its
empty `theorems` arrays, not as a claim that those probes were performed.

GitHub's PR workflow checks a synthetic merge commit. The receipt's
`source_commit` therefore need not equal the branch head. Each module's SHA-256
and the dependency-manifest hash identify exactly what was compiled. Later
documentation commits do not invalidate those receipts if the source hashes
remain equal.

## What still needs proof

1. **E19 determinant in Lean.** The general return-time argument and the
   observer classification do not alone instantiate
   `SeamDeterminantStatement`. Formalize the uniform cycle decomposition and
   `det(I-zC_L)=1-z^L`, then multiply the cycle blocks. The complete written
   argument, including L=1, is in [HOLONOMY_PROOF.md](HOLONOMY_PROOF.md).
2. **E20 minimality.** An annihilating polynomial is not automatically the
   minimal polynomial. The real irreducible 1+2+2 decomposition and the
   irreducibility/minimality claim for the thirteenth-root polynomial require
   their own formal statements.
3. **E18 analytic transfer.** The algebra takes the Eisenstein constant term
   as an explicit hypothesis. Meromorphic continuation and pole cancellations
   remain analytic inputs, separate from the rational channel identities.
4. **Arithmetic sign.** The Connes–Consani manuscript supplies concrete moduli
   and semilocal trace structure, but the primitive pairing, sign theorem and
   global limiting bridge needed by the template remain unfilled. Status:
   `SIGN_GATE_UNMET`.

## Promotion gate

The existing promotion workflow requires refreshed source-bound AXLE receipts
for the eight modified, previously attested modules. Those receipts have not
been fabricated or relabelled. The AXLE credential is unavailable in this
workspace, so independent re-attestation has not been performed. The new core
modules also have no external-attestation badge.

In [promotion run 35161582060](https://github.com/primaryhosting/brockian-mathematics/actions/runs/35161582060),
the control-plane suite reported **191 passed, 1 failed**. The failing test is
`test_committed_registry_is_clean`: the recorded `ConfiningSpectralShape`
attestation hash `e10ed93595a27b24` differs from the repaired flattened-source
hash `dd3c0b9642e9e841`. The later strict-attestation step was consequently
skipped. Earlier clean control-plane runs are not substituted for this result.
This failure is a real promotion blocker, even when the repaired source compiles.

The branch remains a draft for review. When independent verification is
available, attest the exact flattened sources using the repository's
`scripts/attest.py`, preserve the verifier environment and complete theorem
axiom reports, regenerate the derived registry, and rerun the existing gate.
The CI kernel receipts in this review supplement that gate; they do not
replace it.

No RH-strength solver submission, additional RH-evidence numerics, or merge
was made. The next mathematical decision remains the sign question, with the
finite-field template serving as the comparison object.
