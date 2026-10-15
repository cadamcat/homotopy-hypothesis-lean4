# homotopy-hypothesis-lean4

A Lean 4 proof of Grothendieck's homotopy hypothesis for coherators, in the form stated by Maltsiniotis and Ara.

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [AUTHORS.md](AUTHORS.md).
- Developed with AI assistance (Claude Code, Codex and other coding agents); all proofs are verified by the Lean 4 kernel.

## The statement

`HomotopyHypothesis.Statement`, in [Challenge.lean](HomotopyHypothesis/Challenge.lean), which imports only Mathlib. For every coherator `C` (Ara's definition), a topological realization `C → Top` exists. For every realization, the fundamental ∞-groupoid functor `Π_∞ : Top → ∞-Gpd_C` sends weak homotopy equivalences to weak equivalences of `C`-models and exhibits `Ho(∞-Gpd_C)` as the localization of `Top` at the weak homotopy equivalences. The file's header lists every definition the statement uses.

## Main theorem

`HomotopyHypothesis.Blueprint.main : HomotopyHypothesis.Statement`, in [Blueprint/Main.lean](HomotopyHypothesis/Blueprint/Main.lean). Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Build and verify

Requirements: Git and [elan](https://github.com/leanprover/elan). From the repository root:

```sh
lake exe cache get
./scripts/verify.sh
```

`verify.sh` builds the library and prints the axioms of the main theorem ([Verification/Axioms.lean](Verification/Axioms.lean)). `lake exe cache get` downloads prebuilt Mathlib files; without it the first build compiles Mathlib.

The kernel replay, the Comparator check against the statement and their negative controls are recorded in [docs/verification.md](docs/verification.md).

## Mathematical sources

- D. Ara, *On the homotopy theory of Grothendieck ∞-groupoids*, [arXiv:1206.2941](https://arxiv.org/abs/1206.2941): the form of the conjecture that `Statement` formalizes.
- S. Henry, *Algebraic models of homotopy types and the homotopy hypothesis*, [arXiv:1609.04622](https://arxiv.org/abs/1609.04622): the proof followed here, through cylinder categories and the comparison with spaces.
- OpenAI, [openai/math](https://github.com/openai/math): the Lean theory of globular theories and coherators, including the elementary expansion theorem, vendored under [OAI/](OAI). The vocabulary part of `Challenge.lean` is copied from its Comparator challenge. Details in [THIRD_PARTY.md](THIRD_PARTY.md).
