Lambda Calculus Proofs
======================

This repository contains definitions and proofs for the λ-calculus in Lean 4.

The formalization uses a nameless representation (de Bruijn indices) for
variables as defined in *Types and Programming Languages* [TAPL]. Terms are
not dependently typed.

Main Theorems
-------------

  * Church-Rosser (`LC/Semantics.lean`)
  * Progress and preservation for STLC (`LC/Types.lean`)
  * Strong normalization for STLC (`LC/Norm.lean`)

The Church-Rosser proof uses the simultaneous contraction method described in
*Parallel Reductions in λ-Calculus* [Takahashi1995].

The structure of the strong normalization proof follows the logical relations
approach used in *Software Foundations Vol. 2* [SF2].

Some mathlib tactics (e.g. `linarith`) and definitions are used where
necessary.

Requirements
------------

  * Lake 5.0.0
  * Lean 4.24.0
  * [mathlib](https://github.com/leanprover-community/mathlib4)

To build:

	lake build

References
----------

* [SF2] Software Foundations Vol. 2: Programming Language Foundations, by
  Benjamin C. Pierce et al. 2023. Version 6.3.
  [URL](http://softwarefoundations.cis.upenn.edu/plf-6.3/)

* [TAPL] Types and Programming Languages, by Benjamin C. Pierce.
  MIT Press, 2002.

* [Takahashi1995] Takahashi, Masako. "Parallel Reductions in λ-Calculus."
  *Information and Computation* 118(1): 120-127, 1995.
  [DOI](https://doi.org/10.1006/inco.1995.1057)

See `references.bib` for complete reference information.
