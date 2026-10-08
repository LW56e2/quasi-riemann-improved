# Quasi-Riemann boundary refinement in Lean

This repository formalizes a parameter refinement of OpenAI's family-003 argument, improving the zero-free boundary from **7/8 to 0.8749570698**:

\[
B=\frac{4374785349}{5000000000}
 =\frac78-\frac{214651}{5000000000}.
\]

The final proof covers the source's Hecke family over **ℚ(√−3)** and the resulting Dirichlet and Riemann zeta nonvanishing statements in **Re(s) > B**, with the stated principal-pole exceptions. It includes the original OpenAI baseline proof and constructs the modified arithmetic and analytic estimates. No assumed moment bound, probe estimate, or original zero-free ceiling remains in the final theorem statements.

The repository contains the Lean proof and reproducibility tools. The manuscript is not included.

## Main theorems

Import [`Transport.Nonvanishing`](lean/Transport/Nonvanishing.lean). Its declarations are in the `RH.Transport` namespace:

| Declaration | Statement |
| --- | --- |
| `improved_hecke_boundary` | The full-family zero supremum is at most `4374785349 / 5000000000`. |
| `hecke_nonvanishing` | Actual Hecke L-functions are nonzero to the right of this boundary, with the pole condition. |
| `dirichlet_nonvanishing` | Dirichlet L-functions are nonzero there, with the principal-pole exception. |
| `zeta_nonvanishing` | The Lean Riemann zeta function is nonzero there. |

For example:

```lean
import Transport.Nonvanishing

example (s : ℂ) (hs : (4374785349 / 5000000000 : ℝ) < s.re) :
    riemannZeta s ≠ 0 :=
  RH.Transport.zeta_nonvanishing s hs
```

## Build and verify

Prerequisites: Git, Python 3.10 or later, and [elan](https://github.com/leanprover/elan). The committed toolchain pins **Lean 4.34.1**; the Lake lockfile pins all dependencies, including mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.

From the repository root:

```sh
cd lean
lake env lean --version
python3 ../experiments/prepare_lean_dependencies.py
lake exe cache get
lake build +Transport.Nonvanishing
cd ..
python3 experiments/audit_lean.py
```

The first Lake command fetches the exact dependencies in the committed lockfile. The preparation script checks revisions and patch hashes, then applies two compatibility patches supplied by the OpenAI project. It is safe to rerun. Lake may subsequently report local changes in those two packages; these are the recorded patches. Use the committed lockfile for reproduction rather than running `lake update`.

The cache command retrieves mathlib's official build cache. The original arithmetic proof still has a substantial dependency closure to build. Network access, several gigabytes of free space, and sufficient build time are required. To limit build concurrency, set `LEAN_NUM_THREADS`, for example `LEAN_NUM_THREADS=4 lake build +Transport.Nonvanishing`.

The audit builds **every** transport module, checks the exact final theorem types, verifies upstream source hashes, and collects transitive axioms for every transport theorem, including private and generated declarations. It rejects new axiom declarations, `sorryAx`, and any axiom outside `propext`, `Classical.choice`, and `Quot.sound`.

The included [audit report](experiments/lean_audit.json) records a completed verification of the included source hashes:

- **133** transport modules built.
- **798** public theorems and **1,269** total theorem declarations audited.
- **2,926** unchanged OpenAI modules verified against SHA-256 and Git-blob hashes.
- All final nonvanishing statements checked, with only the three standard axioms above.

Running the audit refreshes that report and writes detailed local logs to the ignored `lean/build-logs/` directory. Downloaded dependencies and build products are also excluded from Git.

## Proof organization

| Path under `lean/Transport/` | Role |
| --- | --- |
| `OriginalBaseline.lean` | Derives the original 7/8 ceiling from the unchanged OpenAI proof. |
| `TunedEndpoint.lean`, `TunedCandidate.lean`, `TunedCertificate.lean` | Exact rational parameters, continuous endpoint certificate, and optimization obstruction. |
| `PhysicalLow/`, `PhysicalProbe/` | Reflected energy, supported arithmetic decay, Gram compensation, and the low probe estimate. |
| `PhysicalAnalytic/`, `PhysicalTail/` | Euler correction, principal contour comparison, canonical tails, continuation, and family transfer. |
| `PhysicalHigh/` | Four moment producers, slot and loss choices, and the high probe estimate. |
| `DataProbe.lean`, `CommonProbe.lean`, `Nonvanishing.lean` | One shared normalized probe, final assembly, and the exported result. |

The construction fixes the loss and energy mesh before the slots, chooses errors afterward, chooses count constants before the uniform moment degree, and chooses the height exponent last. Both estimates apply to the same physical probe.

## Exact parameter certificates

The certificate generators use only Python's standard library:

```sh
python3 experiments/optimize_transport.py
python3 experiments/generate_endpoint_lean.py
python3 experiments/optimize_transport_b.py
python3 experiments/generate_tuned_endpoint_lean.py
python3 experiments/audit_lean.py
```

The first pair regenerates the earlier endpoint module used by the tuned certificate. The second pair regenerates the current two-parameter certificate. These commands overwrite the corresponding checked-in certificate data and generated Lean files; the final audit verifies the regenerated proof. The earlier local algebra check is retained as `experiments/check_transport_local.py` for the provenance reference in `LocalBounds.lean`.

An exact two-bin obstruction puts the boundary within **10⁻¹²** of the limit of this specified two-parameter endpoint estimate, uniformly over the aspect ratio. This establishes neither optimality across other methods nor an iteration to the Riemann hypothesis. The proof is asymptotic and does not extract a practical height threshold.

## Source and license

The source is [OpenAI's `math` repository, commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). Its family-003 Lean files are preserved unchanged under [`lean/OAI/`](lean/OAI/); the [source manifest](lean/upstream-config/source-manifest.json) records their hashes. The refinement is in `lean/Transport/`, with source attribution in the relevant modules. It was implemented from OpenAI's sources and their mathematical dependencies, without adapting another refinement's Lean proof.

See [LICENSE](LICENSE) and [NOTICE](NOTICE) for the Apache-2.0 license and attribution. Mathematical and tooling dependencies retain their own licenses. No publication-priority claim is made. The work was prepared with AI assistance and has not undergone independent expert peer review.
