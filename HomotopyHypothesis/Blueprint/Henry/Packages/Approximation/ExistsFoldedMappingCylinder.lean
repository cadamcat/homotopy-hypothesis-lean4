import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.FoldedCylinderPackage.ExistsFoldedMappingCylinderProof

/-!
# `exists_foldedMappingCylinder`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Approximation`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Henry.Packages

open SemiSSet

/-- **Folded relative mapping cylinder** (Rourke–Sanderson §4 and the folding argument of
Thm. 5.3). Let `W` be finite, `j : J ⟶ W` a monomorphism and
`F : ‖W‖ ⟶ ‖X‖` simplicial through `φ : W ⟶ X♯`, with `φ` equal to `g : J ⟶ X` on `J`. Build:

* `P₂ = X ⊔_J (J ⊗ Δ¹)`, the prism over `J` glued to `X` along `g` at one end (`b₂ : X ⟶ P₂`
  anodyne: a prism collapses onto either end), with the projection `ρ₂ : ‖P₂‖ ⟶ ‖X‖`;
* `P = X ⊔_J D`, where `D` is the double prism (two prisms over `J` glued at their `0`-ends), glued
  to `X` at one outer end; `t : J ⟶ P` is the other outer end and `V : P ⟶ P₂` folds the two prisms
  onto one;
* `M ⊇ P` (by the anodyne `i`), adding for every simplex `y ∉ J` with `φ y = (v, x)` the double
  cylinder: a prism followed by the staircase mapping cylinder of the vertex map `v` onto `x`
  (it collapses onto its sides and bottom); `a : W ⟶ M` is the outer end, equal to `t` on `J`;
* `ρ : ‖M‖ ⟶ ‖X‖`, affine on each staircase simplex, equal to `F` on `W` and to the folded `ρ₂`
  on `P`. -/
theorem exists_foldedMappingCylinder {W X J : SemiSSet.{u}} (hW : W.IsFinite) (j : J ⟶ W)
    [Mono j] (g : J ⟶ X) (F : realization.obj W ⟶ realization.obj X) (φ : W ⟶ sharp X)
    (hφ : ∀ (n : ℕ) (y : stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ W),
      ∃ (m : ℕ) (x : stdSimplex.obj (SemiSimplexCategory.mk m) ⟶ X)
        (v : Fin (n + 1) → Fin (m + 1)),
        φ.app (op (SemiSimplexCategory.mk n)) (uliftYonedaEquiv y) =
            sharpMk v (uliftYonedaEquiv x) ∧
          simplexChar y ≫ F = vertexMap v ≫ simplexChar x)
    (hφJ : ∀ (n : ℕ) (z : stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ J),
      φ.app (op (SemiSimplexCategory.mk n)) (uliftYonedaEquiv (z ≫ j)) =
        sharpMk id (uliftYonedaEquiv (z ≫ g))) :
    ∃ (P₂ P M : SemiSSet.{u}) (b₂ : X ⟶ P₂) (V : P ⟶ P₂) (i : P ⟶ M) (a : W ⟶ M) (t : J ⟶ P)
      (ρ₂ : realization.obj P₂ ⟶ realization.obj X) (ρ : realization.obj M ⟶ realization.obj X),
      anodyne b₂ ∧ anodyne i ∧ j ≫ a = t ≫ i ∧ t ≫ V = g ≫ b₂ ∧
        realization.map b₂ ≫ ρ₂ = 𝟙 _ ∧ realization.map i ≫ ρ = realization.map V ≫ ρ₂ ∧
          realization.map a ≫ ρ = F := by apply @_root_.HomotopyHypothesis.Henry.Packages.exists_foldedMappingCylinder_proof <;> assumption
