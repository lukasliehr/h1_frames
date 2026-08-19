# Gabor frames for the first Hermite function

This repository contains a Lean 4 formalization of the main result of the paper *Derivatives of Theta Functions and a Problem of Lyubarskii and Nes* by Lukas Liehr, Irina Shafkulovska and Mitchell A. Taylor. The Lean project formalizes the main theorem of this paper which reads as follows.

**Theorem.** Let $h_1$ be the first Hermite function and let $\Lambda$ be a lattice in the time-frequency plane with density $D(\Lambda) = q/p$ where $p,q$ are positive integers that are coprime and satisfy $q > p + 1$. Then the Gabor system of $h_1$ along $\Lambda$ is a frame for $L^2(\mathbb{R})$.

## Formalization entry points

- `Showcase.lean`: minimal, self-contained formulation of the main formalized theorem, with `sorry`
- `Showcase_WithProofs.lean`: the same statements as in `Showcase.lean`, with all `sorry` replaced by proofs
- `LeanCode/`: internal Lean library for the formalization project

## Building

```bash
lake exe cache get     # download the prebuilt Mathlib cache (recommended)
lake build             # builds the library and both showcase targets
```

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
lean-toolchain             pinned Lean version
```
