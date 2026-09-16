# Receipt index

The files here retain compiler output and theorem axiom reports from GitHub
Actions. They are not AXLE attestations and do not promote registry entries.

| Directory | Evidence | Result |
|---|---|---|
| `core/` | [Run 35161974557](https://github.com/primaryhosting/brockian-mathematics/actions/runs/35161974557), job 105014558871, artifact 10473417311 | 21 compiled modules; 82 axiom-audited theorem declarations in nine selected modules; passed |
| `weyl-before/` | [Run 35158672068](https://github.com/primaryhosting/brockian-mathematics/actions/runs/35158672068) | 23/27 compiled; the four failure logs retained |
| `weyl-after/` | [Run 35159492433](https://github.com/primaryhosting/brockian-mathematics/actions/runs/35159492433) | 27/27 compiled; all build logs retained; no theorem axiom probes in this group |
| `promotion-gate-observation.json` | [Run 35161582060](https://github.com/primaryhosting/brockian-mathematics/actions/runs/35161582060), job 105013314852 | Observed summary: 191 tests passed, one stale-attestation test failed; this is not a verifier receipt |

The downloaded core artifact ZIP had SHA-256
`9db1a2d79b030101ba2277efef178df8ab4502e67bff0f31ce780631b5db8ade`, matching
GitHub's artifact digest. Its original `core/` contents are retained unchanged:
`receipt.json`, one build log per module, and the nine axiom-probe source/log
pairs. All 21 core and 27 repaired Weyl source hashes were compared with the
delivered source files with no mismatch.

Core compiler: Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
Mathlib revision: `81a5d257c8e410db227a6665ed08f64fea08e997`.
The checker uses `-DautoImplicit=false` and does not normalize imports before
compilation. The new algebraic, finite Fourier, observer and Gram modules
contain no `sorry`, new axiom, or `native_decide`. The only reported axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

The early Weyl receipts have a generic `verification_scope` string; their
empty `theorems` arrays accurately record that no theorem axiom probes ran for
that group. The current checker explicitly lists its axiom-probed modules.

To reproduce the bounded checks from a prepared checkout:

```bash
lake exe cache get
python3 scripts/check_structural_core.py --output /tmp/structural-receipts/core
python3 scripts/check_structural_core.py --group weyl --output /tmp/structural-receipts/weyl
```

These commands do not constitute a whole-repository `lake build` and do not
perform independent AXLE re-attestation.
