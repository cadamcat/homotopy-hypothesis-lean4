import HomotopyHypothesis.Blueprint.Henry.Completion
/-!
# Finite cell complexes and cellular realizations

The cylinder category of finite cell complexes, used as the target of the comparison with spaces
(H:418, H:1440, Prop 2.4.18). Following the repair of H Remark 2.4.17, we use *finite cell
complexes* (finitely many cells attached along arbitrary continuous maps) rather than finite CW
complexes, since pushouts of finite CW complexes along arbitrary maps are not CW complexes:

* cofibrations are the relative finite cell complexes, i.e. finite composites of isomorphisms and
  pushouts of the boundary inclusions `∂𝔻 n ⟶ 𝔻 n` (with `∂𝔻 0 = ∅`);
* weak equivalences are the homotopy equivalences.

We also define the weak homotopy equivalences of spaces through the relative lifting property
against the cells (the compression criterion), the realizations of a cylinder category in spaces,
and the associated restriction (fundamental `∞`-groupoid) functor `TopCat ⥤ C̃` (H:2790).
-/

universe v u w

open CategoryTheory Limits HomotopicalAlgebra Opposite TopCat

namespace HomotopyHypothesis.Henry

namespace Top

/-- The boundary inclusions of the disks, `∂𝔻 n ⟶ 𝔻 n` for `n ≥ 0`. -/
def cellBoundaries : MorphismProperty TopCat.{w} :=
  MorphismProperty.ofHoms (fun n : ℕ => diskBoundaryInclusion.{w} n)

/-- Relative finite cell complexes: finite composites of isomorphisms and pushouts (along arbitrary
continuous maps) of the boundary inclusions `∂𝔻 n ⟶ 𝔻 n`. -/
def relativeFiniteCellComplexes : MorphismProperty TopCat.{w} :=
  (cellBoundaries.pushouts ⊔ MorphismProperty.isomorphisms TopCat.{w}).multiplicativeClosure

/-- A finite cell complex: a space `X` such that `∅ ⟶ X` is a relative finite cell complex. -/
def IsFiniteCellComplex : ObjectProperty TopCat.{w} := fun X =>
  relativeFiniteCellComplexes (initial.to X)

/-- Homotopy equivalences of spaces. -/
def homotopyEquivalences : MorphismProperty TopCat.{w} := fun X Y f =>
  ∃ g : Y ⟶ X, (f ≫ g).hom.Homotopic (𝟙 X : X ⟶ X).hom ∧ (g ≫ f).hom.Homotopic (𝟙 Y : Y ⟶ Y).hom

/-- Weak homotopy equivalences, by the compression criterion: `f : X ⟶ Y` is a weak homotopy
equivalence if every square from `∂𝔻 n ⟶ 𝔻 n` to `f` has a diagonal `l : 𝔻 n ⟶ X` making the upper
triangle commute and the lower triangle commute up to homotopy relative to `∂𝔻 n`. For `n = 0`
(`∂𝔻 0 = ∅`) this is surjectivity on path components. -/
def weakEquivalences : MorphismProperty TopCat.{w} := fun X Y f =>
  ∀ (n : ℕ) (a : diskBoundary.{w} n ⟶ X) (b : disk.{w} n ⟶ Y),
    a ≫ f = diskBoundaryInclusion n ≫ b →
      ∃ l : disk.{w} n ⟶ X, diskBoundaryInclusion n ≫ l = a ∧
        (l ≫ f).hom.HomotopicRel b.hom (Set.range (diskBoundaryInclusion.{w} n))

end Top

/-- The category of finite cell complexes (H:418, with the repair of H:1432–1440 replacing finite
CW complexes by finite cell complexes). -/
abbrev FinCell : Type (w + 1) :=
  ObjectProperty.FullSubcategory Top.IsFiniteCellComplex.{w}

instance : CategoryWithCofibrations FinCell.{w} where
  cofibrations := Top.relativeFiniteCellComplexes.inverseImage (ObjectProperty.ι _)

instance : CategoryWithWeakEquivalences FinCell.{w} where
  weakEquivalences := Top.homotopyEquivalences.inverseImage (ObjectProperty.ι _)

section Realization

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- A cellular realization of a cylinder category `C` in spaces: a functor `G : C ⥤ TopCat` with
values in finite cell complexes, sending cofibrations to relative finite cell complexes, weak
equivalences to homotopy equivalences, initial objects to initial objects, and pushout squares along
cofibrations to pushout squares of spaces. Equivalently, a morphism of cylinder categories
`C ⥤ FinCell` whose composite with the inclusion into spaces preserves these pushouts. -/
structure IsCellularRealization (G : C ⥤ TopCat.{w}) : Prop where
  obj_mem : ∀ X : C, Top.IsFiniteCellComplex (G.obj X)
  map_cofibration : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), cofibrations C f →
    Top.relativeFiniteCellComplexes (G.map f)
  map_weakEquivalence : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), weakEquivalences C f →
    Top.homotopyEquivalences (G.map f)
  map_initial : ∀ ⦃I : C⦄, IsInitial I → Nonempty (IsInitial (G.obj I))
  map_isPushout : ∀ ⦃A B X P : C⦄ (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ P) (j : X ⟶ P),
    IsPushout i f k j → cofibrations C i → IsPushout (G.map i) (G.map f) (G.map k) (G.map j)

/-- A cellular realization, viewed as a functor to finite cell complexes. -/
abbrev IsCellularRealization.toFinCell {G : C ⥤ TopCat.{w}} (hG : IsCellularRealization G) :
    C ⥤ FinCell.{w} :=
  ObjectProperty.lift _ G hG.obj_mem

/-- The fundamental `∞`-groupoid functor of a cellular realization `G` (H:2790, `π_∞ = R_G`):
a space `Y` goes to the presheaf `A ↦ Hom(G A, Y)` on `C`. -/
abbrev topRestriction {G : C ⥤ TopCat.{w}} (hG : IsCellularRealization G) :
    TopCat.{w} ⥤ Completion.{w} C :=
  restrictionAlong G hG.map_initial hG.map_isPushout

end Realization

end HomotopyHypothesis.Henry
