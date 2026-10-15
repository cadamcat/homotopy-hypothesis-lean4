# Verification record

The Grothendieck homotopy hypothesis for coherators, release `v1.0.0`, commit `5481f84b13da0a14944ab7470441a7d4e53f3c55`.

| Check | Command or setup | Result |
| --- | --- | --- |
| Build | `LEAN_NUM_THREADS=12 lake build` | Exit 0; 9,645 jobs. |
| Axioms | `./scripts/verify.sh` | Exit 0; `HomotopyHypothesis.Blueprint.main` depends exactly on `[propext, Classical.choice, Quot.sound]`. |
| Kernel replay | `lake env leanchecker --fresh HomotopyHypothesis.Blueprint.Main` | Exit 0. |
| Comparator | Challenge: `HomotopyHypothesis/Challenge.lean` with `HomotopyHypothesis.Blueprint.main : HomotopyHypothesis.Statement` added as `sorry`; `definition_names` empty; nanoda enabled. | Exit 0: nanoda accepts the solution, Lean's default kernel accepts the solution, and Comparator reports `Your solution is okay!` |

Comparator checked the theorem with `definition_names` empty, so unfolded challenge definitions were compared by body. It ran with the development `fake-landrun.sh`, not a Landrun sandbox.

Tool versions: Lean `4.34.1`; Comparator `ca04cfc72b550331658ec314bf47685281bfd4bf`; lean4export `076e8e57707e813375e8f9da8bf989799ace9680`; nanoda_lib `3a2407216ee84a75f9e1aead6803d0578be06ae7`.

## Controls

- Nanoda accepted a small valid proof (exit 0) and rejected a proof by `sorry` (exit 1) because the export declares the unpermitted axiom `sorryAx`.
- Comparator rejected a challenge in which the universal quantifier over realizations was changed to an existential quantifier (exit 1): `Const does not match between challenge and target 'HomotopyHypothesis.Statement'`.
