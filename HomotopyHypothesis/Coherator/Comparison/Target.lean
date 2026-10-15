import HomotopyHypothesis.Cylinder.SimplicialCategory.Cofibrations
import HomotopyHypothesis.Cylinder.SimplicialCategory.FreeAlgKan
import HomotopyHypothesis.Cylinder.SimplicialCategory.HornFiltration
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexContractions
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexLift
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexRealization
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexSubfunctors
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.SemisimplicialComparison.CDeltaFacts
import HomotopyHypothesis.Realization.SemisimplicialComparison.CellAttach
import HomotopyHypothesis.Coherator.Comparison.Nerve
/-!
# The nerve of a morphism of cofibration categories out of `C^Δ`

A morphism of cofibration categories `h : C^Δ ⥤ Y` gives cosimplicial data in `Y`: the images of the
free simplices, the images of the free horns (which realize the horns, since `h` preserves pushouts
along cofibrations), and the images of the canonical horn retractions. For every object `A` of `C^Δ`,
`h A` corepresents `A` along the resulting nerve `Y ⥤ AlgKan`, via the map sending a simplex of `A`
to the image under `h` of the corresponding map out of a free simplex.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Coherator.Comparison

open HomotopyHypothesis.Henry HomotopyHypothesis.Cylinder.SimplicialCategory

/-- The free simplices as a cosimplicial object of `C^Δ`. -/
@[simps]
noncomputable def stdSimplexFunctor : Henry.SemiSimplexCategory ⥤ CDelta.{u} where
  obj Δ := stdSimplexCDelta.{u} Δ.obj.len
  map g := stdSimplexCDeltaMap.{u} g
  map_id Δ := stdSimplexCDeltaMap_id.{u} Δ.obj.len
  map_comp f g := stdSimplexCDeltaMap_comp.{u} f g

lemma simplexToSemiSSet_stdSimplex {k n : ℕ}
    (y : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n)).obj
      (op (Henry.SemiSimplexCategory.mk k))) :
    simplexToSemiSSet y = SemiSSet.stdSimplex.{u}.map (ULift.down y) := by
  ext Δ g
  rfl

section SimplexHat

variable {A : CDelta.{u}}

/-- The map out of a free simplex classifying a simplex `y` of `A`. -/
noncomputable def simplexHat {k : ℕ} (y : A.obj.X.obj (op (Henry.SemiSimplexCategory.mk k))) :
    stdSimplexCDelta.{u} k ⟶ A :=
  ObjectProperty.homMk
    (freeAlgKan_isFreeOn (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) A.obj
      (simplexToSemiSSet y)).choose

lemma unit_simplexHat {k : ℕ} (y : A.obj.X.obj (op (Henry.SemiSimplexCategory.mk k))) :
    freeAlgKanUnit _ ≫ (simplexHat y).hom.hom = simplexToSemiSSet y :=
  (freeAlgKan_isFreeOn (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) A.obj
      (simplexToSemiSSet y)).choose_spec.1

lemma eq_simplexHat {k : ℕ} {y : A.obj.X.obj (op (Henry.SemiSimplexCategory.mk k))}
    {g : stdSimplexCDelta.{u} k ⟶ A} (hg : freeAlgKanUnit _ ≫ g.hom.hom = simplexToSemiSSet y) :
    g = simplexHat y :=
  ObjectProperty.hom_ext _
    ((freeAlgKan_isFreeOn (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) A.obj
      (simplexToSemiSSet y)).choose_spec.2 g.hom hg)

lemma simplexHat_map {k m : ℕ} (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m)
    (y : A.obj.X.obj (op (Henry.SemiSimplexCategory.mk m))) :
    simplexHat (A.obj.X.map θ.op y) = stdSimplexCDeltaMap θ ≫ simplexHat y := by
  symm
  apply eq_simplexHat
  change freeAlgKanUnit _ ≫ (freeAlgKanMap (SemiSSet.stdSimplex.{u}.map θ)).hom ≫
    (simplexHat y).hom.hom = _
  erw [← Category.assoc, freeAlgKanUnit_comp_freeAlgKanMap, Category.assoc, unit_simplexHat,
    stdSimplex_map_comp_simplexToSemiSSet]

lemma simplexHat_comp {B : CDelta.{u}} (f : A ⟶ B) {k : ℕ}
    (y : A.obj.X.obj (op (Henry.SemiSimplexCategory.mk k))) :
    simplexHat y ≫ f = simplexHat (f.hom.hom.app _ y) := by
  apply eq_simplexHat
  change freeAlgKanUnit _ ≫ (simplexHat y).hom.hom ≫ f.hom.hom = _
  erw [← Category.assoc, unit_simplexHat, simplexToSemiSSet_comp]

lemma simplexHat_unit {F : SemiSSet.{u}} (hCell : AlgKan.IsFinitelyCellular (freeAlgKan F))
    {k : ℕ} (x : F.obj (op (Henry.SemiSimplexCategory.mk k))) :
    simplexHat (A := ⟨freeAlgKan F, hCell⟩) ((freeAlgKanUnit F).app _ x) =
      ObjectProperty.homMk (freeAlgKanMap (simplexToSemiSSet x)) := by
  symm
  apply eq_simplexHat
  change freeAlgKanUnit _ ≫ (freeAlgKanMap (simplexToSemiSSet x)).hom = _
  rw [freeAlgKanUnit_comp_freeAlgKanMap, simplexToSemiSSet_comp]

lemma simplexHat_stdUnit {n k : ℕ}
    (x : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n)).obj
      (op (Henry.SemiSimplexCategory.mk k))) :
    simplexHat (A := stdSimplexCDelta.{u} n) ((freeAlgKanUnit _).app _ x) =
      stdSimplexCDeltaMap (ULift.down x) := by
  have := simplexHat_unit (F := SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n))
    (isFinitelyCellular_freeAlgKan_stdSimplex n) x
  rw [simplexToSemiSSet_stdSimplex] at this
  exact this

/-- The map out of a free horn classifying a horn of `A`. -/
noncomputable def hornHat {n : ℕ} {k : Fin (n + 2)}
    (α : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ A.obj.X) : hornCDelta.{u} n k ⟶ A :=
  ObjectProperty.homMk ((freeAlgKan_isFreeOn _ A.obj α).choose)

lemma unit_hornHat {n : ℕ} {k : Fin (n + 2)}
    (α : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ A.obj.X) :
    freeAlgKanUnit _ ≫ (hornHat α).hom.hom = α :=
  (freeAlgKan_isFreeOn _ A.obj α).choose_spec.1

end SimplexHat

/-- The composite of a face of `Δ_{n+1}` lying in the horn with the canonical horn retraction. -/
lemma stdSimplexCDeltaMap_comp_canonicalHornRetraction {n : ℕ} {k : Fin (n + 2)} {m : ℕ}
    (x : (SemiSSet.horn.{u} (n + 1) k).toFunctor.obj (op (Henry.SemiSimplexCategory.mk m))) :
    stdSimplexCDeltaMap (ULift.down x.1) ≫ canonicalHornRetraction.{u} n k =
      ObjectProperty.homMk (freeAlgKanMap (simplexToSemiSSet x)) := by
  apply ObjectProperty.hom_ext
  apply freeAlgKan_hom_ext
  have hx : simplexToSemiSSet x ≫ (SemiSSet.horn.{u} (n + 1) k).ι =
      SemiSSet.stdSimplex.{u}.map (ULift.down x.1) := by
    rw [simplexToSemiSSet_comp]
    exact simplexToSemiSSet_stdSimplex _
  change freeAlgKanUnit _ ≫ (freeAlgKanMap (SemiSSet.stdSimplex.{u}.map (ULift.down x.1))).hom ≫
      (canonicalHornRetraction.{u} n k).hom.hom =
    freeAlgKanUnit _ ≫ (freeAlgKanMap (simplexToSemiSSet x)).hom
  erw [← Category.assoc, freeAlgKanUnit_comp_freeAlgKanMap, Category.assoc,
    freeAlgKanUnit_comp_canonicalHornRetraction, freeAlgKanUnit_comp_freeAlgKanMap, ← hx,
    Category.assoc, (hornCDelta.{u} n k).obj.fill_spec]
  rfl

section Target

variable {Y : Type (u + 1)} [Category.{u} Y] [CategoryWithCofibrations Y]
  (h : CDelta.{u} ⥤ Y) (hh : IsCofibrationMorphism h)

/-- The cosimplicial data in `Y` induced by `h : C^Δ ⥤ Y`. -/
noncomputable def targetData : CosimplicialData Y where
  D := stdSimplexFunctor.{u} ⋙ h
  Q_horn n k :=
    (isUniversalCocone_mapFunctor_freeCDeltaCocone h hh (SemiSSet.horn.{u} (n + 1) k)
      (hasDimLe_subfunctor_stdSimplex (le_refl (n + 1)) (SemiSSet.horn.{u} (n + 1) k))).toRealization
  r_horn n k := h.map (canonicalHornRetraction.{u} n k)
  r_horn_spec n k m hm x := by
    change h.map (stdSimplexCDeltaMap (ULift.down x.1)) ≫ h.map (canonicalHornRetraction.{u} n k) =
      h.map (ObjectProperty.homMk (freeAlgKanMap (simplexToSemiSSet x)))
    rw [← h.map_comp, stdSimplexCDeltaMap_comp_canonicalHornRetraction]

lemma targetData_D : (targetData h hh).D = stdSimplexFunctor.{u} ⋙ h := rfl

/-- The semi-simplicial part of the unit `A ⟶ N_Y (h A)`. -/
noncomputable def unitYNat (A : CDelta.{u}) :
    A.obj.X ⟶ nerveSemiSSet (targetData h hh).D (h.obj A) where
  app Δ := ↾fun y => h.map (simplexHat (k := (unop Δ).obj.len) y)
  naturality Δ Δ' θ := by
    ext y
    exact (congrArg h.map (simplexHat_map θ.unop y)).trans (h.map_comp _ _)

/-- The unit `A ⟶ N_Y (h A)`: a simplex of `A` goes to the image of its classifying map. -/
noncomputable def unitY (A : CDelta.{u}) : A.obj ⟶ (targetData h hh).nerve.obj (h.obj A) where
  hom := unitYNat h hh A
  fill_hom n k α := by
    have hdesc : (targetData h hh).hornDesc (α ≫ unitYNat h hh A) = h.map (hornHat α) := by
      apply ((targetData h hh).Q_horn n k).hom_ext
      intro m hm x
      refine ((targetData h hh).ι_hornDesc _ m hm x).trans ?_
      change h.map (simplexHat (α.app _ x)) =
        h.map (ObjectProperty.homMk (freeAlgKanMap (simplexToSemiSSet x))) ≫ h.map (hornHat α)
      rw [← h.map_comp]
      congr 1
      symm
      apply eq_simplexHat
      change freeAlgKanUnit _ ≫ (freeAlgKanMap (simplexToSemiSSet x)).hom ≫ (hornHat α).hom.hom = _
      erw [← Category.assoc, freeAlgKanUnit_comp_freeAlgKanMap, Category.assoc, unit_hornHat,
        simplexToSemiSSet_comp]
    ext Δ g
    change h.map (simplexHat ((A.obj.fill n k α).app Δ g)) =
      h.map (stdSimplexCDeltaMap (ULift.down g)) ≫ h.map (canonicalHornRetraction.{u} n k) ≫
        (targetData h hh).hornDesc _
    erw [hdesc, ← h.map_comp, ← h.map_comp]
    congr 1
    symm
    apply eq_simplexHat
    change freeAlgKanUnit _ ≫ (freeAlgKanMap (SemiSSet.stdSimplex.{u}.map (ULift.down g))).hom ≫
      ((canonicalHornRetraction.{u} n k).hom ≫ (hornHat α).hom).hom = _
    erw [← Category.assoc, freeAlgKanUnit_comp_freeAlgKanMap, Category.assoc,
      canonicalHornRetraction_comp_hom_fill, unit_hornHat, ← simplexToSemiSSet_stdSimplex,
      simplexToSemiSSet_comp]

lemma unitY_app (A : CDelta.{u}) (Δ : Henry.SemiSimplexCategoryᵒᵖ) (y : A.obj.X.obj Δ) :
    (unitY h hh A).hom.app Δ y = h.map (simplexHat (k := (unop Δ).obj.len) y) := rfl

lemma unitY_naturality {A B : CDelta.{u}} (f : A ⟶ B) :
    unitY h hh A ≫ (targetData h hh).nerve.map (h.map f) = f.hom ≫ unitY h hh B := by
  apply AlgKan.Hom.ext
  ext Δ y
  change h.map (simplexHat (k := (unop Δ).obj.len) y) ≫ h.map f =
    h.map (simplexHat (k := (unop Δ).obj.len) (f.hom.hom.app Δ y))
  rw [← h.map_comp, simplexHat_comp]

/-- Free objects on a subfunctor of a simplex: `h` of the free object corepresents it. -/
lemma isCorep_unitY_free {M N : ℕ}
    (T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (hT : HasDimLe M T.toFunctor) :
    IsCorep (targetData h hh).nerve (freeAlgKan T.toFunctor)
      (h.obj ⟨freeAlgKan T.toFunctor, isFinitelyCellular_freeAlgKan_subfunctor T⟩)
      (unitY h hh ⟨freeAlgKan T.toFunctor, isFinitelyCellular_freeAlgKan_subfunctor T⟩) := by
  refine IsCorep.of_isFreeOn (targetData h hh) hT
    (isUniversalCocone_mapFunctor_freeCDeltaCocone h hh T hT).toRealization
    (freeAlgKan_isFreeOn _) _ ?_
  intro k hk x
  change h.map (simplexHat ((freeAlgKanUnit T.toFunctor).app _ x)) =
    h.map (ObjectProperty.homMk (freeAlgKanMap (simplexToSemiSSet x)) :
      stdSimplexCDelta.{u} k ⟶
        (⟨freeAlgKan T.toFunctor, isFinitelyCellular_freeAlgKan_subfunctor T⟩ : CDelta.{u}))
  erw [simplexHat_unit]

/-- `h` of a free simplex corepresents it. -/
lemma isCorep_unitY_stdSimplex (n : ℕ) :
    IsCorep (targetData h hh).nerve (stdSimplexCDelta.{u} n).obj (h.obj (stdSimplexCDelta.{u} n))
      (unitY h hh (stdSimplexCDelta.{u} n)) := by
  refine IsCorep.of_isFreeOn (targetData h hh) (hasDimLe_stdSimplex (le_refl n))
    (stdSimplexRealization (toUpTo (targetData h hh).D n) n (le_refl n))
    (freeAlgKan_isFreeOn _) _ ?_
  intro k hk x
  change h.map (simplexHat ((freeAlgKanUnit _).app _ x)) = h.map (stdSimplexCDeltaMap (ULift.down x))
  rw [simplexHat_stdUnit]

/-- An object of `C^Δ` whose underlying algebraic Kan complex is initial is initial. -/
noncomputable def isInitial_of_isInitial_obj {A : CDelta.{u}} (hA : IsInitial A.obj) : IsInitial A :=
  IsInitial.ofUniqueHom (fun Z => ObjectProperty.homMk (hA.to Z.obj))
    (fun _ _ => ObjectProperty.hom_ext _ (hA.hom_ext _ _))

/-- **Every object of `C^Δ` is corepresented by its image under `h`.** -/
theorem isCorep_unitY (A : CDelta.{u}) :
    IsCorep (targetData h hh).nerve A.obj (h.obj A) (unitY h hh A) := by
  obtain ⟨A, hA⟩ := A
  induction hA with
  | initial A hA =>
    obtain ⟨hA⟩ := hA
    exact IsCorep.of_isInitial hA
      (hh.map_initial (isInitial_of_isInitial_obj (A := ⟨A, _⟩) hA)).some _
  | @attach A A' j hAcell hj ih =>
    let d := Realization.SemisimplicialComparison.AlgKan.IsCellAttachment.data hj
    obtain ⟨abar, habar, -⟩ := freeAlgKan_isFreeOn _ A d.a
    obtain ⟨ybar, hybar, -⟩ := freeAlgKan_isFreeOn _ A' d.y
    have sq : IsPushout (boundaryCDeltaInclusion.{u} d.n).hom abar ybar j :=
      d.isPushout (freeAlgKan_isFreeOn _) (freeAlgKan_isFreeOn _)
        (freeAlgKanUnit_comp_freeAlgKanMap _) habar hybar
    have sqC : IsPushout (boundaryCDeltaInclusion.{u} d.n)
        (ObjectProperty.homMk abar : boundaryCDelta.{u} d.n ⟶ ⟨A, hAcell⟩)
        (ObjectProperty.homMk ybar : stdSimplexCDelta.{u} d.n ⟶ ⟨A', .attach j hAcell hj⟩)
        (ObjectProperty.homMk j) :=
      Realization.SemisimplicialComparison.isPushout_of_alg sq
    have sqY := hh.map_isPushout _ _ _ _ sqC (boundaryCDeltaInclusion_cofibration _)
    exact IsCorep.of_isPushout sq sqY
      (isCorep_unitY_free h hh (SemiSSet.boundary.{u} d.n)
        (hasDimLe_subfunctor_stdSimplex (le_refl d.n) (SemiSSet.boundary.{u} d.n)))
      (isCorep_unitY_stdSimplex h hh d.n) ih
      (unitY_naturality h hh (boundaryCDeltaInclusion.{u} d.n)).symm
      (unitY_naturality h hh (ObjectProperty.homMk abar : boundaryCDelta.{u} d.n ⟶ ⟨A, hAcell⟩)).symm
      (unitY_naturality h hh
        (ObjectProperty.homMk ybar : stdSimplexCDelta.{u} d.n ⟶ ⟨A', .attach j hAcell hj⟩)).symm
      (unitY_naturality h hh
        (ObjectProperty.homMk j : (⟨A, hAcell⟩ : CDelta.{u}) ⟶ ⟨A', .attach j hAcell hj⟩)).symm

end Target

end HomotopyHypothesis.Coherator.Comparison
