# Gabor frames for the first Hermite function

This repository contains a Lean 4 formalization of the main result of the paper *Derivatives of Theta Functions and a Problem of Lyubarskii and Nes* by Lukas Liehr, Irina Shafkulovska and Mitchell A. Taylor ([arXiv:2609.27846](https://arxiv.org/abs/2609.27846)). The Lean project formalizes the main theorem of this paper which reads as follows.

**Theorem.** Let $h_1$ be the first Hermite function and let $\Lambda$ be a lattice in the time-frequency plane with density $D(\Lambda) = q/p$ where $p,q$ are positive integers that are coprime and satisfy $q > p + 1$. Then the Gabor system of $h_1$ along $\Lambda$ is a frame for $L^2(\mathbb{R})$.

The theorem is the implication (2) ⇒ (1) of Theorem 1.1 of the paper. The converse implication, which the paper derives from earlier results in the literature, is not formalized. Section 6 of the paper explains the Lean statement line by line.

## Formalization entry points

- `Showcase.lean`: minimal, self-contained formulation of the main formalized theorem and of the convergence of its series, with `sorry`. It imports only Mathlib
- `Showcase_WithProofs.lean`: the same statements as in `Showcase.lean`, with all `sorry` replaced by proofs
- `LeanCode/`: internal Lean library for the formalization project

## Building

The project uses Lean `v4.35.0` and the matching Mathlib release, as pinned in `lean-toolchain` and `lake-manifest.json`. All Lean files use Lean's module system.

```bash
lake exe cache get     # download the prebuilt Mathlib cache (recommended)
lake build             # builds the library and both showcase targets
```

The build reports three `sorry` warnings, all in `Showcase.lean`, where they are intended. The proof development contains no `sorry`.

## Convergence of the series

In Lean the sum `∑'` of a series which does not converge is defined to be `0`. The frame condition `IsGaborFrame` in `Showcase.lean` is stated with an iterated series over `m` and `n`. The theorem `coefficients_summable` in the same file shows that, under the hypotheses of `MainResult`, the family $|\langle f, \pi(M(m,n))h_1\rangle|^2$ is summable over $\mathbb{Z}^2$ for every $f \in L^2(\mathbb{R})$. Hence every series in `IsGaborFrame` converges, the iterated series is the sum over the whole lattice, and `MainResult` does not depend on this convention. The theorem `coefficients_summable` is not printed in the paper. The frame predicates of the library in `LeanCode/` contain this summability as a condition.

## Independent verification

The file `comparator.json` is a configuration for Lean's `lake comparator`. It checks that the declarations `h1Atom_memL2`, `MainResult` and `coefficients_summable` in `Showcase_WithProofs.lean` have exactly the statements given in `Showcase.lean`, that their proofs use no axioms other than `propext`, `Quot.sound` and `Classical.choice`, and that the proofs are accepted by Lean's kernel.

```bash
lake exe cache get
lake comparator --config comparator.json
```

This command requires Linux with `bwrap` (bubblewrap).

## Palomar

The repository is prepared for the [Palomar registry](https://palomar-registry.org/) of Lean formalizations. The file `formalization.yaml` contains the metadata that Palomar requires. The Palomar entry corresponds to the configuration `comparator.json`.

## Repository layout

```
LeanCode.lean              root module of the formalization library
LeanCode/
  Definitions.lean         Hermite Gabor atoms, L²-membership, and frame predicate
  Main.lean                imports the complete development
  MainTheorem.lean         main result for separable lattices
  Membership/              auxiliary L²-membership lemmas
  ComplexAnalysis/         division-by-divisor result
  ThetaFunctions/          theta functions and theta spaces
  TorsionJets/             primitive torsion-jet independence
  FrobeniusDeterminant/    Frobenius determinant and primitive derivative results
  ZakTransform/            Zak transform and rational frame criterion
  RationalDensity/         Gaussian Zak formulas and separable rational density theorem
  GeneralLattice/          extension to arbitrary lattices with rational density and metaplectic reduction
lakefile.toml              Lake project configuration
lake-manifest.json         pinned dependency revisions
lean-toolchain             pinned Lean version
comparator.json            configuration for lake comparator
formalization.yaml         metadata of the formalization
LICENSE                    licence of this repository
.github/workflows/         Palomar's mechanical verification, run on every push to the palomar branch
```

## Licence

This repository is released under the Apache License 2.0, see `LICENSE`.
