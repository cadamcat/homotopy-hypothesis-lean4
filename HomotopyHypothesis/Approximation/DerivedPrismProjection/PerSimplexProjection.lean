import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellAffine
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellSingular
import HomotopyHypothesis.Approximation.DerivedPrismTop.DerivedPositions
import HomotopyHypothesis.Approximation.DerivedPrismTop.LanProjection
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertex
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertexLanProjection
import HomotopyHypothesis.Approximation.DerivedPrismTop.TopCellRestriction
import HomotopyHypothesis.Approximation.DerivedPrismProjection.SimplexFactorization
import HomotopyHypothesis.Approximation.Topological.BaryCell.BaryCellBijective
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprismCos
import HomotopyHypothesis.Approximation.Topological.KanApproximation.Part1
import HomotopyHypothesis.Approximation.Topological.Projection
/-!
# Simplexwise projection formulas for the derived cylinder
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismProjection

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Approximation.DerivedPrismTop
  HomotopyHypothesis.Henry.SemiSSet

/-- The cell projection on the characteristic simplex is the affine cell map. -/
theorem dprismCellProjection_simplexChar {m n : ℕ}
    (z' : stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶
      dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk m)) :
    simplexChar z' ≫ dprismCellProjection.{u} m =
      dprismCellMap ((uliftYonedaEquiv z').down) := by
  let σ := uliftYonedaEquiv z'
  have hz : uliftYonedaEquiv.symm σ = z' := Equiv.symm_apply_apply _ _
  have hmap : realization.map z' = realization.map (uliftYonedaEquiv.symm σ) :=
    congrArg realization.map hz.symm
  unfold simplexChar
  rw [hmap]
  calc
    ((stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk n) ≫
        realization.map (uliftYonedaEquiv.symm σ)) ≫ dprismCellProjection.{u} m =
      dprismCellMap σ.down := (Category.assoc _ _ _).trans
        (dprismCellProjection_unit σ)
    _ = dprismCellMap ((uliftYonedaEquiv z').down) := by rfl

/-- A simplex characteristic map into the derived complex is injective. -/
theorem sdSimplexChar_injective {m n : ℕ}
    (z' : stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶
      sdCos.{u}.obj (Henry.SemiSimplexCategory.mk m)) :
    Function.Injective (simplexChar z').hom := by
  classical
  let σ := uliftYonedaEquiv z'
  let t := σ.down.1
  let p : PV m → Fin (n + 1) := fun a =>
    if h : a ∈ Set.range t then Classical.choose (Set.mem_range.mp h) else 0
  have hp : p ∘ t = id := by
    funext i
    dsimp [p, Function.comp]
    have hi : t i ∈ Set.range t := ⟨i, rfl⟩
    rw [dif_pos hi]
    exact σ.down.2.1.injective (Classical.choose_spec (Set.mem_range.mp hi))
  have hleft : simplexChar z' ≫ (sdComplex m).affineProj.{u} p = 𝟙 _ := by
    have h := Complex.unit_map_affineProj (sdComplex m) p σ
    have hz : uliftYonedaEquiv.symm σ = z' := Equiv.symm_apply_apply _ _
    have hmap : realization.map z' = realization.map (uliftYonedaEquiv.symm σ) :=
      congrArg realization.map hz.symm
    have hchar : simplexChar z' =
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk n) ≫
            realization.map (uliftYonedaEquiv.symm σ) := by
      unfold simplexChar
      rw [hmap]
    calc
      simplexChar z' ≫ (sdComplex m).affineProj.{u} p =
          ((stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
            (Henry.SemiSimplexCategory.mk n) ≫
              realization.map (uliftYonedaEquiv.symm σ)) ≫
            (sdComplex m).affineProj.{u} p := by rw [hchar]
      _ = affineMap (p ∘ t) := (Category.assoc _ _ _).trans h
      _ = 𝟙 _ := by rw [hp, affineMap_id_simplex]
  intro x y hxy
  have hx := congrArg (fun f => f.hom x) hleft
  have hy := congrArg (fun f => f.hom y) hleft
  calc
    x = ((sdComplex m).affineProj.{u} p).hom ((simplexChar z').hom x) := hx.symm
    _ = ((sdComplex m).affineProj.{u} p).hom ((simplexChar z').hom y) :=
      congrArg ((sdComplex m).affineProj.{u} p).hom hxy
    _ = y := hy

/-- The barycentric map on each simplex of the derived end is a linear embedding and is its
affine cell projection. -/
theorem dprismSdCellProjection {m n : ℕ}
    (z' : stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶
      sdCos.{u}.obj (Henry.SemiSimplexCategory.mk m)) :
    IsLinearEmbedding (simplexMapOfPoints.{u} n m
      (dprismPosition ∘ (uliftYonedaEquiv z').down.1)) ∧
      simplexChar z' ≫
          realization.{u}.map (sdToDprismCos.{u}.app
            (Henry.SemiSimplexCategory.mk m)) ≫ dprismCellProjection.{u} m =
        simplexMapOfPoints.{u} n m
          (dprismPosition ∘ (uliftYonedaEquiv z').down.1) := by
  classical
  let σ := uliftYonedaEquiv z'
  let le := simplexMapOfPoints.{u} n m (dprismPosition ∘ σ.down.1)
  let b := realization.{u}.map (sdToDprismCos.{u}.app
    (Henry.SemiSimplexCategory.mk m)) ≫ dprismCellProjection.{u} m
  have hcell : simplexChar z' ≫ b = le := by
    calc
      simplexChar z' ≫
          realization.{u}.map (sdToDprismCos.{u}.app
            (Henry.SemiSimplexCategory.mk m)) ≫ dprismCellProjection.{u} m =
        simplexChar (z' ≫ sdToDprismCos.{u}.app
          (Henry.SemiSimplexCategory.mk m)) ≫ dprismCellProjection.{u} m := by
            rw [simplexChar_comp]
            cat_disch
      _ = dprismCellMap ((uliftYonedaEquiv
          (z' ≫ sdToDprismCos.{u}.app
            (Henry.SemiSimplexCategory.mk m))).down) :=
            dprismCellProjection_simplexChar _
      _ = le := rfl
  constructor
  · change Convexity.IsAffineMap ℝ (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      (ULift.down (le.hom (ULift.up x)) : Convexity.StdSimplex ℝ (Fin (m + 1)))) ∧ _
    constructor
    · exact (Convexity.StdSimplex.affineMapMk (R := ℝ)
        (dprismPosition ∘ σ.down.1)).isAffineMap_toFun
    · have hb : Function.Injective b.hom := by
        have hb := (baryCell_bijective.{u} m).1
        change Function.Injective b.hom
        exact hb
      have hinj : Function.Injective (simplexChar z').hom := sdSimplexChar_injective z'
      intro x y hxy
      apply hinj
      apply hb
      have hx := congrArg (fun f => f.hom x) hcell
      have hy := congrArg (fun f => f.hom y) hcell
      simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at hx hy
      exact hx.trans (hxy.trans hy.symm)
  · exact hcell

/-- The glued last-vertex projection restricts to every semi-simplex cell. -/
theorem dprismLanLastVertexProjection_cell_any (j : Henry.SemiSimplexCategory) :
    realization.{u}.map
        ((stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app j) ≫
      dprismLanLastVertexProjection.{u}.app (stdSimplex.{u}.obj j) =
        dprismLastVertexCellProjection.{u} j.obj.len ≫
          (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app j := by
  cases j with
  | mk jObj =>
    cases jObj with
    | mk k =>
      simpa using dprismLanLastVertexProjection_cell.{u} k

/-- On a standard derived-cylinder cell, the last-vertex projection is the affine map
determined by the last vertices of the cell's ordered vertices. -/
theorem dprismLastVertexCellProjection_simplex {m n : ℕ}
    (z' : stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶
      dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk m)) :
    simplexChar z' ≫ dprismLastVertexCellProjection.{u} m =
      vertexMap (dprismLastVertex ∘ (uliftYonedaEquiv z').down.1) := by
  let σ := uliftYonedaEquiv z'
  have h := Complex.unit_map_affineProj (dprismComplex m) dprismLastVertex σ
  have hz : uliftYonedaEquiv.symm σ = z' := Equiv.symm_apply_apply _ _
  have hmap : realization.map z' = realization.map (uliftYonedaEquiv.symm σ) :=
    congrArg realization.map hz.symm
  have hchar : simplexChar z' =
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk n) ≫
          realization.map (uliftYonedaEquiv.symm σ) := by
    unfold simplexChar
    rw [hmap]
  calc
    simplexChar z' ≫ dprismLastVertexCellProjection.{u} m =
        ((stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk n) ≫
            realization.map (uliftYonedaEquiv.symm σ)) ≫
          dprismLastVertexCellProjection.{u} m := by rw [hchar]
    _ = ((stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk n) ≫
            realization.map (uliftYonedaEquiv.symm σ)) ≫
          (dprismComplex m).affineProj dprismLastVertex := by rfl
    _ = affineMap (dprismLastVertex ∘ σ.down.1) := by
      exact (Category.assoc _ _ _).trans h
    _ = vertexMap (dprismLastVertex ∘ (uliftYonedaEquiv z').down.1) := by
      dsimp [σ, HomotopyHypothesis.Henry.SemiSSet.vertexMap,
        HomotopyHypothesis.Approximation.Topological.affineMap]

/-- On the derived-simplex cell, the last-vertex projection is the affine map of its vertex labels.
-/
theorem dprismSdCellLastVertexProjection {m n : ℕ}
    (z' : stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶
      sdCos.{u}.obj (Henry.SemiSimplexCategory.mk m)) :
    simplexChar z' ≫ realization.{u}.map
        (sdToDprismCos.{u}.app (Henry.SemiSimplexCategory.mk m)) ≫
      dprismLastVertexCellProjection.{u} m =
        vertexMap (dprismLastVertex ∘ (uliftYonedaEquiv z').down.1) := by
  calc
    simplexChar z' ≫ realization.{u}.map
        (sdToDprismCos.{u}.app (Henry.SemiSimplexCategory.mk m)) ≫
      dprismLastVertexCellProjection.{u} m =
        simplexChar (z' ≫ sdToDprismCos.{u}.app
          (Henry.SemiSimplexCategory.mk m)) ≫ dprismLastVertexCellProjection.{u} m := by
            rw [simplexChar_comp]
            cat_disch
    _ = vertexMap (dprismLastVertex ∘
          (uliftYonedaEquiv (z' ≫ sdToDprismCos.{u}.app
            (Henry.SemiSimplexCategory.mk m))).down.1) :=
          dprismLastVertexCellProjection_simplex _
    _ = vertexMap (dprismLastVertex ∘ (uliftYonedaEquiv z').down.1) := by rfl

/-- Every simplex of the derived cylinder is affine on a vertex map into one of its cells. -/
theorem exists_dprismLan_simplex_lastVertex {V : Henry.SemiSSet.{u}} {n : ℕ}
    (z : stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶ dprismLan.{u}.obj V) :
    ∃ (m : ℕ) (w : stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m) ⟶ V)
      (v : Fin (n + 1) → Fin (m + 1)),
      simplexChar z ≫ dprismLanLastVertexProjection.{u}.app V =
        vertexMap v ≫ simplexChar w := by
  classical
  obtain ⟨c, z', hz⟩ := exists_dprismLan_simplex_cell z
  rcases c with ⟨j, r, f⟩
  cases r
  cases j with
  | mk jObj =>
    cases jObj with
    | mk m =>
      let v := dprismLastVertex ∘ (uliftYonedaEquiv z').down.1
      refine ⟨m, f, v, ?_⟩
      have hpr :
          realization.{u}.map (dprismLan.{u}.map f) ≫
              dprismLanLastVertexProjection.{u}.app V =
            dprismLanLastVertexProjection.{u}.app
                (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) ≫
              realization.{u}.map f := by
        simpa only [Functor.comp_map, Functor.const_obj_obj] using
          dprismLanLastVertexProjection.{u}.naturality f
      have harg : z' ≫
            (stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
              (Henry.SemiSimplexCategory.mk m) ≫ dprismLan.{u}.map f =
          (z' ≫
            (stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
              (Henry.SemiSimplexCategory.mk m)) ≫ dprismLan.{u}.map f :=
        (Category.assoc _ _ _).symm
      calc
        simplexChar z ≫ dprismLanLastVertexProjection.{u}.app V =
            simplexChar (z' ≫
              (stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
                (Henry.SemiSimplexCategory.mk m) ≫
              dprismLan.{u}.map f) ≫
                dprismLanLastVertexProjection.{u}.app V := by rw [hz]
        _ = (simplexChar z' ≫
              realization.{u}.map
                ((stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
                  (Henry.SemiSimplexCategory.mk m))) ≫
              (realization.{u}.map (dprismLan.{u}.map f) ≫
                dprismLanLastVertexProjection.{u}.app V) := by
          rw [harg, simplexChar_comp, simplexChar_comp]
          cat_disch
        _ = (simplexChar z' ≫
              realization.{u}.map
                ((stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
                  (Henry.SemiSimplexCategory.mk m))) ≫
              (dprismLanLastVertexProjection.{u}.app
                  (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) ≫
                realization.{u}.map f) := by rw [hpr]
        _ = (simplexChar z' ≫
              (realization.{u}.map
                  ((stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
                    (Henry.SemiSimplexCategory.mk m)) ≫
                dprismLanLastVertexProjection.{u}.app
                  (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)))) ≫
              realization.{u}.map f := by cat_disch
        _ = (simplexChar z' ≫
              (dprismLastVertexCellProjection.{u} m ≫
                (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                  (Henry.SemiSimplexCategory.mk m))) ≫
              realization.{u}.map f := by
          exact congrArg (fun g => (simplexChar z' ≫ g) ≫
              realization.{u}.map f)
            (dprismLanLastVertexProjection_cell.{u} m)
        _ = ((simplexChar z' ≫ dprismLastVertexCellProjection.{u} m) ≫
              (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                (Henry.SemiSimplexCategory.mk m)) ≫
              realization.{u}.map f := by
          exact congrArg (fun g => g ≫ realization.{u}.map f)
            (Category.assoc (simplexChar z')
              (dprismLastVertexCellProjection.{u} m)
              ((stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                (Henry.SemiSimplexCategory.mk m))).symm
        _ = (vertexMap v ≫
              (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                (Henry.SemiSimplexCategory.mk m)) ≫
              realization.{u}.map f := by
          rw [dprismLastVertexCellProjection_simplex]
        _ = vertexMap v ≫ simplexChar f := by
          have hfchar : simplexChar f =
              (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                  (Henry.SemiSimplexCategory.mk m) ≫ realization.{u}.map f := rfl
          rw [hfchar]
          exact Category.assoc _ _ _

/-- Every simplex of the derived end comes from one of its derived-simplex cells. -/
theorem exists_sdLan_simplex_cell {V : Henry.SemiSSet.{u}} {n : ℕ}
    (z : stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶ sdLan.{u}.obj V) :
    ∃ (c : CostructuredArrow Henry.SemiSSet.stdSimplex.{u} V)
      (z' : stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶ sdCos.{u}.obj c.left),
      z = z' ≫
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}).app c.left ≫
          sdLan.{u}.map c.hom := by
  classical
  let P := CostructuredArrow.proj Henry.SemiSSet.stdSimplex.{u} V
  let S := P ⋙ sdCos.{u}
  let ev := (CategoryTheory.evaluation (Henry.SemiSimplexCategoryᵒᵖ) (Type u)).obj
    (op (Henry.SemiSimplexCategory.mk n))
  let Sₙ := S ⋙ ev
  let E : Functor.LeftExtension Henry.SemiSSet.stdSimplex.{u} sdCos.{u} :=
    Functor.LeftExtension.mk sdLan.{u}
      (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u})
  have hEall : E.IsPointwiseLeftKanExtension :=
    Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension sdLan.{u}
      (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u})
  let c := E.coconeAt V
  have hc : IsColimit c := hEall V
  let cₙ := ev.mapCocone c
  have hcₙ : IsColimit cₙ := isColimitOfPreserves ev hc
  obtain ⟨c', x, hx⟩ :=
    CategoryTheory.Limits.Concrete.isColimit_exists_rep Sₙ hcₙ (uliftYonedaEquiv z)
  have hleg : c.ι.app c' =
      (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}).app c'.left ≫
        sdLan.{u}.map c'.hom := by
    rfl
  have hx' :
      ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}).app c'.left ≫
        sdLan.{u}.map c'.hom).app (op (Henry.SemiSimplexCategory.mk n)) x =
          uliftYonedaEquiv z := by
    change ev.map (c.ι.app c') x = uliftYonedaEquiv z at hx
    rw [hleg] at hx
    exact hx
  refine ⟨c', uliftYonedaEquiv.symm x, ?_⟩
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp]
  exact hx'.symm

/-- The derived-end map restricts to the derived-cylinder map on each standard cell. -/
theorem sdLanToDprism_cell (m : ℕ) :
    (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}).app
        (Henry.SemiSimplexCategory.mk m) ≫
      sdLanToDprism.{u}.app
        (Henry.SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) =
      sdToDprismCos.{u}.app (Henry.SemiSimplexCategory.mk m) ≫
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
          (Henry.SemiSimplexCategory.mk m) := by
  simpa only [sdLanToDprism, NatTrans.comp_app] using
    (Functor.descOfIsLeftKanExtension_fac_app
      (F' := sdLan.{u})
      (α := Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u})
      dprismLan.{u}
      (sdToDprismCos.{u} ≫
        Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
      (Henry.SemiSimplexCategory.mk m))

/-- Every simplex of the derived end maps affinely and by last vertices into a cell of its source.
-/
theorem exists_sdLan_simplex_projections {V : Henry.SemiSSet.{u}} {n : ℕ}
    (z : stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶ sdLan.{u}.obj V) :
    ∃ (m : ℕ) (w : stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m) ⟶ V)
      (le : toTop.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶
        toTop.{u}.obj (Henry.SemiSimplexCategory.mk m))
      (v : Fin (n + 1) → Fin (m + 1)),
      IsLinearEmbedding le ∧
        simplexChar z ≫ realization.{u}.map (sdLanToDprism.{u}.app V) ≫
            dprismLanProjection.{u}.app V = le ≫ simplexChar w ∧
        simplexChar z ≫ realization.{u}.map (sdLanToDprism.{u}.app V) ≫
            dprismLanLastVertexProjection.{u}.app V = vertexMap v ≫ simplexChar w := by
  classical
  obtain ⟨c, z', hz⟩ := exists_sdLan_simplex_cell z
  rcases c with ⟨j, r, f⟩
  cases r
  cases j with
  | mk jObj =>
    cases jObj with
    | mk m =>
      let σ := uliftYonedaEquiv z'
      let ηs := (stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}).app
        (Henry.SemiSimplexCategory.mk m)
      let ηd := (stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
        (Henry.SemiSimplexCategory.mk m)
      let ηt := (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk m)
      let le := simplexMapOfPoints.{u} n m (dprismPosition ∘ σ.down.1)
      let v := dprismLastVertex ∘ σ.down.1
      have hα : realization.{u}.map (sdLan.{u}.map f) ≫
          realization.{u}.map (sdLanToDprism.{u}.app V) =
        realization.{u}.map (sdLanToDprism.{u}.app
          (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m))) ≫
          realization.{u}.map (dprismLan.{u}.map f) := by
        calc
          _ = realization.{u}.map
              (sdLan.{u}.map f ≫ sdLanToDprism.{u}.app V) :=
                (CategoryTheory.Functor.map_comp realization _ _).symm
          _ = realization.{u}.map
              (sdLanToDprism.{u}.app
                (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) ≫
                dprismLan.{u}.map f) :=
                congrArg realization.{u}.map (sdLanToDprism.naturality f)
          _ = _ := CategoryTheory.Functor.map_comp realization _ _
      have hchar : simplexChar (z' ≫ ηs ≫ sdLan.{u}.map f) =
          (simplexChar z' ≫ realization.{u}.map ηs) ≫
            realization.{u}.map (sdLan.{u}.map f) := by
        have harg : z' ≫ ηs ≫ sdLan.{u}.map f =
            (z' ≫ ηs) ≫ sdLan.{u}.map f := (Category.assoc _ _ _).symm
        rw [harg, simplexChar_comp, simplexChar_comp]
      have htransport (q : dprismLan.{u} ⋙ realization.{u} ⟶ realization.{u})
          (cellProj : realization.{u}.obj
              (dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk m)) ⟶
            toTop.{u}.obj (Henry.SemiSimplexCategory.mk m))
          (hqcell : realization.{u}.map ηd ≫
            q.app (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) =
              cellProj ≫ ηt) :
          simplexChar z ≫ realization.{u}.map (sdLanToDprism.{u}.app V) ≫ q.app V =
            ((simplexChar z' ≫ realization.{u}.map
                (sdToDprismCos.{u}.app (Henry.SemiSimplexCategory.mk m)) ≫ cellProj) ≫
              (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                (Henry.SemiSimplexCategory.mk m)) ≫ realization.{u}.map f := by
        have hcell : realization.{u}.map ηs ≫
            (realization.{u}.map (sdLanToDprism.{u}.app
              (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m))) ≫
            q.app (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m))) =
              realization.{u}.map (sdToDprismCos.{u}.app
                (Henry.SemiSimplexCategory.mk m)) ≫ (cellProj ≫ ηt) := by
          rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
            sdLanToDprism_cell, CategoryTheory.Functor.map_comp,
            Category.assoc, hqcell]
          rfl
        have hqnat : realization.{u}.map (dprismLan.{u}.map f) ≫ q.app V =
            q.app (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) ≫
              realization.{u}.map f := by
          simpa only [Functor.comp_map, Functor.const_obj_obj] using q.naturality f
        calc
          simplexChar z ≫ realization.{u}.map (sdLanToDprism.{u}.app V) ≫ q.app V =
              simplexChar (z' ≫ ηs ≫ sdLan.{u}.map f) ≫
                realization.{u}.map (sdLanToDprism.{u}.app V) ≫ q.app V := by rw [hz]
          _ = ((simplexChar z' ≫ realization.{u}.map ηs) ≫
                realization.{u}.map (sdLan.{u}.map f)) ≫
                realization.{u}.map (sdLanToDprism.{u}.app V) ≫ q.app V := by rw [hchar]
          _ = (simplexChar z' ≫ realization.{u}.map ηs) ≫
                (realization.{u}.map (sdLan.{u}.map f) ≫
                  realization.{u}.map (sdLanToDprism.{u}.app V)) ≫ q.app V := by cat_disch
          _ = (simplexChar z' ≫ realization.{u}.map ηs) ≫
                (realization.{u}.map (sdLanToDprism.{u}.app
                  (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m))) ≫
                  realization.{u}.map (dprismLan.{u}.map f)) ≫ q.app V := by rw [hα]
          _ = (simplexChar z' ≫ realization.{u}.map ηs) ≫
                realization.{u}.map (sdLanToDprism.{u}.app
                  (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m))) ≫
                (realization.{u}.map (dprismLan.{u}.map f) ≫ q.app V) := by cat_disch
          _ = (simplexChar z' ≫ realization.{u}.map ηs) ≫
                realization.{u}.map (sdLanToDprism.{u}.app
                  (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m))) ≫
                (q.app (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) ≫
                  realization.{u}.map f) := by rw [hqnat]
          _ = (simplexChar z' ≫
                (realization.{u}.map ηs ≫
                  realization.{u}.map (sdLanToDprism.{u}.app
                    (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m))) ≫
                  q.app (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)))) ≫
                realization.{u}.map f := by cat_disch
          _ = ((simplexChar z' ≫ realization.{u}.map
                (sdToDprismCos.{u}.app (Henry.SemiSimplexCategory.mk m)) ≫ cellProj) ≫
              (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                (Henry.SemiSimplexCategory.mk m)) ≫ realization.{u}.map f := by
                  rw [hcell]
                  dsimp [ηt]
                  erw [Category.assoc]
      have hsd := dprismSdCellProjection z'
      have hlast := dprismSdCellLastVertexProjection z'
      have hfchar : simplexChar f =
          (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
            (Henry.SemiSimplexCategory.mk m) ≫ realization.{u}.map f := rfl
      refine ⟨m, f, le, v, hsd.1, ?_, ?_⟩
      · calc
          simplexChar z ≫ realization.{u}.map (sdLanToDprism.{u}.app V) ≫
              dprismLanProjection.{u}.app V =
            ((simplexChar z' ≫ realization.{u}.map
                (sdToDprismCos.{u}.app (Henry.SemiSimplexCategory.mk m)) ≫
              dprismCellProjection.{u} m) ≫
              (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                (Henry.SemiSimplexCategory.mk m)) ≫ realization.{u}.map f :=
                htransport dprismLanProjection.{u} (dprismCellProjection.{u} m)
                  (dprismLanProjection_cell.{u} m)
          _ = (le ≫ (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                (Henry.SemiSimplexCategory.mk m)) ≫ realization.{u}.map f :=
              congrArg (fun g => (g ≫
                (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                  (Henry.SemiSimplexCategory.mk m)) ≫ realization.{u}.map f) hsd.2
          _ = le ≫ simplexChar f := by
              rw [hfchar]
              exact Category.assoc _ _ _
      · calc
          simplexChar z ≫ realization.{u}.map (sdLanToDprism.{u}.app V) ≫
              dprismLanLastVertexProjection.{u}.app V =
            ((simplexChar z' ≫ realization.{u}.map
                (sdToDprismCos.{u}.app (Henry.SemiSimplexCategory.mk m)) ≫
              dprismLastVertexCellProjection.{u} m) ≫
              (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                (Henry.SemiSimplexCategory.mk m)) ≫ realization.{u}.map f :=
                htransport dprismLanLastVertexProjection.{u}
                  (dprismLastVertexCellProjection.{u} m)
                  (dprismLanLastVertexProjection_cell.{u} m)
          _ = (vertexMap v ≫
                (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                  (Henry.SemiSimplexCategory.mk m)) ≫ realization.{u}.map f :=
              congrArg (fun g => (g ≫
                (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
                  (Henry.SemiSimplexCategory.mk m)) ≫ realization.{u}.map f) hlast
          _ = vertexMap v ≫ simplexChar f := by
              rw [hfchar]
              exact Category.assoc _ _ _

end HomotopyHypothesis.Approximation.DerivedPrismProjection
