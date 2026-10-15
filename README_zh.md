[English](README.md) | [简体中文](README_zh.md)

# homotopy-hypothesis-lean4

Grothendieck 同伦假设（对 coherator，采用 Maltsiniotis 与 Ara 给出的形式）的 Lean 4 证明。

- **作者：** Yao Xu ([@cadamcat](https://github.com/cadamcat))；见[作者与署名说明](AUTHORS.md)。
- **数学结果：** OpenAI，[*The Grothendieck homotopy hypothesis via elementary expansions*](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Grothendieck-homotopy-hypothesis-via-elementary-expansions-September-24-2026/paper.pdf)（2026），建立在 S. Henry 的框架之上。
- 本项目在 AI 协助下开发；所有证明均由 Lean 4 内核验证。

## 陈述

`HomotopyHypothesis.Statement`，位于 [Challenge.lean](HomotopyHypothesis/Challenge.lean)，该文件只导入 Mathlib。对每个 coherator `C`（Ara 的定义），存在拓扑实现 `C → Top`；对每个实现，基本 ∞-广群函子 `Π_∞ : Top → ∞-Gpd_C` 把弱同伦等价映为 `C`-模型的弱等价，并使 `Ho(∞-Gpd_C)` 成为 `Top` 在弱同伦等价处的局部化。文件开头列出了陈述用到的全部定义。

## 主定理

`HomotopyHypothesis.Blueprint.main : HomotopyHypothesis.Statement`，位于 [Blueprint/Main.lean](HomotopyHypothesis/Blueprint/Main.lean)。它依赖的公理为 `propext`、`Classical.choice` 和 `Quot.sound`。

## 构建与验证

需要 Git 和 [elan](https://github.com/leanprover/elan)。在仓库根目录运行：

```sh
lake exe cache get
./scripts/verify.sh
```

`verify.sh` 构建整个库，并打印主定理依赖的公理（[Verification/Axioms.lean](Verification/Axioms.lean)）。`lake exe cache get` 下载预编译的 Mathlib 文件；不运行它，首次构建会从源码编译 Mathlib。

内核重放、与陈述对照的 Comparator 检查及其反例对照，记录在 [docs/verification.md](docs/verification.md)。

## 数学来源

- D. Ara，*On the homotopy theory of Grothendieck ∞-groupoids*，[arXiv:1206.2941](https://arxiv.org/abs/1206.2941)：`Statement` 所形式化的猜想形式。
- S. Henry，*Algebraic models of homotopy types and the homotopy hypothesis*，[arXiv:1609.04622](https://arxiv.org/abs/1609.04622)：这里遵循的证明路线，经由柱范畴与空间比较定理。
- OpenAI，[openai/math](https://github.com/openai/math)：关于 globular 理论和 coherator 的 Lean 理论，包括初等扩张定理，收录于 [OAI/](OAI)。`Challenge.lean` 的词汇部分取自其 Comparator 挑战。详见 [THIRD_PARTY.md](THIRD_PARTY.md)。
