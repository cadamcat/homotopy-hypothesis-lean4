import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Homotopy.RelativeLifting.FinCellHomotopyRel

/-!
# `finCell_homotopicRel_iff`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Topology`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- **Relative cylinders of finite cell complexes are homotopies relative to a subcomplex.** For a
cofibration `i : A ⟶ B` of `FinCell` and two maps `f g : B ⟶ Y` into any space, `f` and `g` are
homotopic relative to `A` if and only if they are the two restrictions of a map `I_A B ⟶ Y` out of
some relative cylinder of `i` in `FinCell`. The standard cylinder
`B × [0, 1] ⊔_{A × [0, 1]} A` is a finite cell complex (Hatcher, Prop. 0.16's prism cells) and
gives one direction; for the other, any relative cylinder receives a map from the standard one
under `B ⊔_A B` (H Prop 2.2.8, `relHomotopic_equivalence`, in `FinCell`). -/
theorem finCell_homotopicRel_iff {A B : FinCell.{u}} (i : A ⟶ B)
    (hi : cofibrations FinCell.{u} i) {Y : TopCat.{u}} (f g : B.obj ⟶ Y) :
    f.hom.HomotopicRel g.hom (Set.range i.hom.hom) ↔
      ∃ (cyl : RelativeCylinder i) (h : cyl.I.obj ⟶ Y),
        (cyl.j₀ ≫ cyl.c).hom ≫ h = f ∧ (cyl.j₁ ≫ cyl.c).hom ≫ h = g := by apply @_root_.HomotopyHypothesis.Homotopy.RelativeLifting.finCell_homotopicRel_iff_proof <;> assumption
