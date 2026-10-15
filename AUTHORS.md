# Authors and attribution

Yao Xu ([@cadamcat](https://github.com/cadamcat)) is the author and maintainer of this formalization project.

The theorem formalized here is Grothendieck's homotopy hypothesis for coherators, in the form stated by Maltsiniotis and Ara. A proof was given by OpenAI in [*The Grothendieck homotopy hypothesis via elementary expansions*](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Grothendieck-homotopy-hypothesis-via-elementary-expansions-September-24-2026/paper.pdf) (2026), building on S. Henry's *Algebraic models of homotopy types and the homotopy hypothesis*. This repository formalizes the theorem; it does not claim a new mathematical solution. The formal proof follows Henry's comparison through cylinder categories, uses the elementary expansion theorem from OpenAI's Lean library, and proves the topological input directly in topological spaces.

The author planned, directed and reviewed the work, using AI coding assistants; all proofs and their dependencies are checked by the Lean kernel.

The project uses Mathlib and OpenAI's `openai/math` library, whose modules under `OAI/` are included unchanged. Their authors and licenses are credited in [THIRD_PARTY.md](THIRD_PARTY.md).
