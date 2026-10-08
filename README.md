# Quasi-Riemann boundary refinement in Lean

This repository formalizes a parameter refinement of OpenAI's family-003 argument, improving the zero-free boundary from **7/8 to 0.8749570698**:

$$
B=\frac{4374785349}{5000000000}
 =\frac78-\frac{214651}{5000000000}.
$$

The proof covers the source's finite-order Hecke family over **ℚ(√−3)** and the resulting Dirichlet and Riemann zeta nonvanishing statements in **Re(s) > B**, away from poles. It includes the original OpenAI baseline proof and constructs the modified arithmetic and analytic estimates. No assumed moment bound, probe estimate, or original zero-free ceiling remains in the final theorem statements.

The repository contains the Lean sources and exact parameter certificates. The manuscript and exploratory experiments are not included; the experiments are not needed to check the proofs.

## Main theorems

Import [`Transport.Nonvanishing`](lean/Transport/Nonvanishing.lean). Its declarations are in the `RH.Transport` namespace:

| Declaration | Statement |
| --- | --- |
| `improved_hecke_boundary` | The full-family zero supremum is at most `4374785349 / 5000000000`. |
| `hecke_nonvanishing` | The source's Hecke L-functions are nonzero to the right of this boundary, with the pole condition. |
| `dirichlet_nonvanishing` | Dirichlet L-functions of all nonzero moduli are nonzero there, with the principal-pole exception. |
| `zeta_nonvanishing` | Lean's totalized Riemann zeta function is nonzero there. |

For the conventional meromorphic zeta function, the nonvanishing statement excludes its pole at `s = 1`. The Lean definition assigns a value there, so the formal zeta theorem does not require that exclusion. No claim is made about the line `Re(s) = B`.

For example:

```lean
import Transport.Nonvanishing

example (s : ℂ) (hs : (4374785349 / 5000000000 : ℝ) < s.re) :
    riemannZeta s ≠ 0 :=
  RH.Transport.zeta_nonvanishing s hs
```

## Build

Prerequisites: Git and [elan](https://github.com/leanprover/elan). The committed toolchain pins **Lean 4.34.1**; the Lake lockfile pins all dependencies, including mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.

From the repository root in a fresh checkout:

```sh
cd lean
lake env lean --version

git -C .lake/packages/rellich-kondrachov apply \
  "$PWD/upstream-config/patches/rellich-kondrachov-lean4341.patch"
git -C .lake/packages/PrimeNumberTheoremAnd apply \
  "$PWD/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch"

lake exe cache get
lake build
```

The first Lake command fetches the dependencies pinned by the committed lockfile. Apply the two compatibility patches **once per fresh checkout**; they are supplied by the OpenAI project, and their package revisions and patch hashes are recorded in [`applied-physical-patches.json`](lean/upstream-config/applied-physical-patches.json). Subsequent Lake warnings about local changes in these two packages are expected. Keep the committed lockfile when reproducing the proof; do not run `lake update`.

`lake exe cache get` retrieves mathlib's official build cache. `lake build` checks all **133** transport modules, including the parameter certificates. To build only the final theorem's import closure, use `lake build +Transport.Nonvanishing` instead. The original arithmetic proof still has a substantial dependency closure to build, so allow several gigabytes of disk space and sufficient build time.

## Inspect the theorem statements and axioms

After building, run this from `lean/`:

```sh
lake env lean --stdin <<'LEAN'
import Transport.Nonvanishing

#check RH.Transport.improved_hecke_boundary
#check RH.Transport.hecke_nonvanishing
#check RH.Transport.dirichlet_nonvanishing
#check RH.Transport.zeta_nonvanishing

#print axioms RH.Transport.improved_hecke_boundary
#print axioms RH.Transport.hecke_nonvanishing
#print axioms RH.Transport.dirichlet_nonvanishing
#print axioms RH.Transport.zeta_nonvanishing
LEAN
```

Each final theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The axiom lists include transitive dependencies, including the imported OpenAI baseline; they contain neither `sorryAx` nor additional axioms. These commands inspect the final statements directly and do not depend on an external audit script.

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

## Parameter certificates and scope

[`TunedEndpoint.lean`](lean/Transport/TunedEndpoint.lean) proves the continuous endpoint inequality using exact rational arithmetic and 40 Bernstein rectangles. The certificate data and proofs are committed Lean source; verifying them does not require rerunning the exploratory optimization or its generators. Some source comments record the names of those construction scripts, which are not distributed here.

An exact two-bin obstruction in [`TunedEndpoint.lean`](lean/Transport/TunedEndpoint.lean) shows that retuning the same two parameters with the specified balanced counting estimate cannot lower the chosen boundary by **10⁻¹²**. This is a necessary obstruction for that estimate, not a proof that its limiting value is attained or that other counts, moments, or geometries cannot do better. The proof is asymptotic and does not extract a practical height threshold or an iteration to the Riemann hypothesis.

## Source and license

The source is [OpenAI's `math` repository, commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). Its **2,926** family-003 Lean modules are preserved unchanged under [`lean/OAI/`](lean/OAI/); the [source manifest](lean/upstream-config/source-manifest.json) records their SHA-256 and Git-blob hashes. The refinement is in `lean/Transport/`, with source attribution in the relevant modules. It was implemented from OpenAI's sources and their mathematical dependencies, without adapting another refinement's Lean proof.

See [LICENSE](LICENSE) for the repository's Apache-2.0 license and [`lean/upstream-config/LICENSE`](lean/upstream-config/LICENSE) for the upstream license. Dependencies retain their own licenses. No publication-priority claim is made. The work was prepared with AI assistance and has not undergone independent expert peer review.
