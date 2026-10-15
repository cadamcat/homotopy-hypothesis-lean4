# Third-party sources

- **Mathlib** ([leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4)), Apache-2.0. A build dependency, pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612` in `lake-manifest.json`; no Mathlib source is copied here.
- **OpenAI's mathematics library** ([openai/math](https://github.com/openai/math), directory `lean`), Apache-2.0 ([OAI/LICENSE](OAI/LICENSE)). The modules under `OAI/` are copied unchanged from commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; only modules in the import closure of this library are included.
- **The statement's vocabulary.** The first part of [HomotopyHypothesis/Challenge.lean](HomotopyHypothesis/Challenge.lean) (globular sets, globular sums, globular theories, coherators, models and their weak equivalences) is copied from `ComparatorChallenges/GrothendieckElementaryExpansion.lean` in openai/math, Apache-2.0, with the namespace renamed and the challenge theorem omitted, as its header records.
