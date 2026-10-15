import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.RealizationExistsFiniteSubcomplex
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.Boundary.HornPrism
import HomotopyHypothesis.Realization.Boundary.RealizationBoundary
import HomotopyHypothesis.Realization.Boundary.RealizationGeometry
import HomotopyHypothesis.Realization.Boundary.SimplexDisk
/-!
# Realization of a semi-simplicial horn

The realized horn is the union of the coordinate faces other than the omitted face.
-/

universe u

open CategoryTheory Limits Opposite Convexity
open HomotopyHypothesis.Henry HomotopyHypothesis.Realization.Boundary

namespace HomotopyHypothesis.Horn.DeformationRetraction

/-- A horn is a subfunctor of the boundary. -/
theorem horn_le_boundary (n : ℕ) (k : Fin (n + 1)) :
    SemiSSet.horn.{u} n k ≤ SemiSSet.boundary n := by
  intro c f hf
  obtain ⟨i, _, hi⟩ := hf
  exact ⟨i, hi⟩

/-- A horn has finitely many semi-simplices. -/
theorem finite_horn_elements (n : ℕ) (k : Fin (n + 1)) :
    Finite (SemiSSet.horn.{u} n k).toFunctor.Elements := by
  let i := Subfunctor.homOfLe (horn_le_boundary n k)
  letI := finite_boundary_elements.{u} n
  apply Finite.of_injective i.mapElements.obj
  intro e e' h
  cases e with
  | @mk c x =>
    cases e' with
    | @mk d y =>
      have hcd : c = d := congrArg Functor.Elements.obj h
      subst d
      have hxy : i.app c x = i.app c y := by
        injection h
      have he : x = y := by
        apply Subtype.ext
        exact congrArg (fun z : (SemiSSet.boundary.{u} n).toFunctor.obj c => z.val) hxy
      cases he
      rfl

/-- A horn realization is compact, as a finite colimit of compact simplices. -/
theorem compactSpace_realization_horn (n : ℕ) (k : Fin (n + 1)) :
    CompactSpace (SemiSSet.realization.obj (SemiSSet.horn.{u} n k).toFunctor) := by
  classical
  let P := (SemiSSet.horn.{u} n k).toFunctor
  let D := Presheaf.functorToRepresentables P ⋙ SemiSSet.realization.{u}
  have hFinite : Finite P.Elements := finite_horn_elements n k
  letI : Finite P.Elements := hFinite
  letI : Finite P.Elementsᵒᵖ := Finite.of_injective (fun j : P.Elementsᵒᵖ => j.unop) (by
    intro j j' h
    cases j
    cases j'
    cases h
    rfl)
  letI : PreservesColimitsOfSize.{0, u, u, u, u + 1, u + 1} SemiSSet.realization := by
    change PreservesColimitsOfSize.{0, u, u, u, u + 1, u + 1}
      (SemiSSet.stdSimplex.leftKanExtension SemiSSet.toTop)
    exact Presheaf.preservesColimitsOfSize_leftKanExtension.{0, 0, u, 0, 0, u + 1, u}
      (A := SemiSSet.toTop.{u})
  have hCompact : ∀ j : P.Elementsᵒᵖ, CompactSpace (D.obj j) := by
    intro j
    change CompactSpace (SemiSSet.realization.{u}.obj
      (SemiSSet.stdSimplex.{u}.obj ((Functor.Elements.π P).obj j.unop).unop))
    let e := realization_representable_iso ((Functor.Elements.π P).obj j.unop).unop
    exact @Homeomorph.compactSpace _ _ _ _ (by
      change CompactSpace (ULift (Convexity.StdSimplex ℝ
        (Fin (((Functor.Elements.π P).obj j.unop).unop.obj.len + 1))))
      exact Homeomorph.compactSpace Homeomorph.ulift.symm) (TopCat.homeoOfIso e).symm
  let c := SemiSSet.realization.{u}.mapCocone (Presheaf.coconeOfRepresentable P)
  have hc : IsColimit c :=
    isColimitOfPreserves SemiSSet.realization.{u} (Presheaf.colimitOfRepresentable P)
  letI : Small.{u} P.Elementsᵒᵖ := small_self _
  letI : HasColimit D := by dsimp [D]; infer_instance
  let e : c.pt ≅ (colimit D : TopCat.{u}) := hc.coconePointUniqueUpToIso (colimit.isColimit D)
  letI : CompactSpace ((colimit D : TopCat.{u})) := compactSpace_colimit_of_finite_index D hCompact
  change CompactSpace c.pt
  exact @Homeomorph.compactSpace _ _ _ _ inferInstance (TopCat.homeoOfIso e.symm)

theorem hornRepresentableMap_eq_stdSimplexMap (n : ℕ) (k : Fin (n + 1))
    (e : (SemiSSet.horn.{u} n k).toFunctor.Elements) :
    (Presheaf.coconeOfRepresentable (SemiSSet.horn.{u} n k).toFunctor).ι.app (Opposite.op e) ≫
      (SemiSSet.horn n k).ι =
        SemiSSet.stdSimplex.map e.val.val.down := by
  let P := (SemiSSet.horn.{u} n k).toFunctor
  let Q := SemiSSet.stdSimplex.{u}.obj
    (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
  let e' : Q.Elements := (SemiSSet.horn n k).ι.mapElements.obj e
  have hNat := Presheaf.coconeOfRepresentable_naturality (SemiSSet.horn n k).ι (Opposite.op e)
  have hval : e'.val.down = e.val.val.down := by
    dsimp [e', NatTrans.mapElements]
    rfl
  have h1 : (Presheaf.coconeOfRepresentable P).ι.app (Opposite.op e) ≫
      (SemiSSet.horn n k).ι =
        (Presheaf.coconeOfRepresentable Q).ι.app (Opposite.op e') := by
    simpa [P, Q, e'] using hNat
  have h2 := stdSimplexCoconeLeg_eq_map n e'
  rw [hval] at h2
  exact h1.trans h2

/-- The canonical map from the realized horn to barycentric coordinates on the simplex. -/
noncomputable def hornRealizationToCoords (n : ℕ) (k : Fin (n + 1)) :
    SemiSSet.realization.{u}.obj (SemiSSet.horn.{u} n k).toFunctor ⟶
      TopCat.of (LiftedClosedCoordSimplex n) :=
  SemiSSet.realization.{u}.map (SemiSSet.horn.{u} n k).ι ≫
    (realizationSimplexCoordsIso n).hom

theorem hornRealizationToCoords_mem (n : ℕ) (k : Fin (n + 1))
    (x : SemiSSet.realization.{u}.obj (SemiSSet.horn.{u} n k).toFunctor) :
    ((hornRealizationToCoords n k).hom x).down ∈ coordinateHorn n k := by
  classical
  let P := (SemiSSet.horn.{u} n k).toFunctor
  let D := Presheaf.functorToRepresentables P ⋙ SemiSSet.realization.{u}
  let c := SemiSSet.realization.{u}.mapCocone (Presheaf.coconeOfRepresentable P)
  letI : PreservesColimitsOfSize.{0, u, u, u, u + 1, u + 1} SemiSSet.realization := by
    change PreservesColimitsOfSize.{0, u, u, u, u + 1, u + 1}
      (SemiSSet.stdSimplex.{u}.leftKanExtension SemiSSet.toTop.{u})
    exact Presheaf.preservesColimitsOfSize_leftKanExtension.{0, 0, u, 0, 0, u + 1, u}
      (A := SemiSSet.toTop.{u})
  have hc : IsColimit c :=
    isColimitOfPreserves SemiSSet.realization.{u} (Presheaf.colimitOfRepresentable P)
  have hcol : IsColimit ((forget TopCat).mapCocone c) := isColimitOfPreserves (forget TopCat) hc
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcol x
  let e : P.Elements := j.unop
  let c₀ : HomotopyHypothesis.Henry.SemiSimplexCategory :=
    ((Functor.Elements.π P).obj e).unop
  change SemiSSet.realization.{u}.obj (SemiSSet.stdSimplex.{u}.obj c₀) at y
  let f : c₀ ⟶ HomotopyHypothesis.Henry.SemiSimplexCategory.mk n := e.val.val.down
  obtain ⟨i, hik, hi⟩ := e.val.property
  have hmissing : i ∉ Set.range
      (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom := by
    rintro ⟨a, ha⟩
    exact hi ⟨a, ha⟩
  have hC : c.ι.app j = SemiSSet.realization.{u}.map
      ((Presheaf.coconeOfRepresentable P).ι.app (Opposite.op e)) := rfl
  have hfactor : c.ι.app j ≫ SemiSSet.realization.{u}.map (SemiSSet.horn.{u} n k).ι =
      SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) := by
    rw [hC]
    exact (Functor.map_comp _ _ _).symm.trans
      (congrArg (SemiSSet.realization.{u}.map)
        (hornRepresentableMap_eq_stdSimplexMap n k e))
  have htoCoords : c.ι.app j ≫ hornRealizationToCoords n k =
      SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
        (realizationSimplexCoordsIso n).hom := by
    change c.ι.app j ≫
      (SemiSSet.realization.{u}.map (SemiSSet.horn.{u} n k).ι ≫
        (realizationSimplexCoordsIso n).hom) = _
    rw [← Category.assoc, hfactor]
    rfl
  have hy' : (c.ι.app j).hom y = x := by
    simpa using hy
  let s : StdSimplex ℝ (Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj c₀).len + 1)) :=
    ULift.down ((realization_representable_iso c₀).hom.hom y)
  refine ⟨i, hik, ?_⟩
  have hEval := congrArg
    (fun g : D.obj j ⟶ TopCat.of (LiftedClosedCoordSimplex n) => g.hom y) htoCoords
  have hEval' : (hornRealizationToCoords n k).hom x =
      ((SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
        (realizationSimplexCoordsIso n).hom).hom y) := by
    have hEval2 : (hornRealizationToCoords n k).hom ((c.ι.app j).hom y) =
        (realizationSimplexCoordsIso n).hom.hom
          ((SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f)).hom y) := by
      change (c.ι.app j ≫ hornRealizationToCoords n k).hom y =
        (SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
          (realizationSimplexCoordsIso n).hom).hom y
      exact hEval
    rw [hy'] at hEval2
    exact hEval2
  have hIsoEval :
      ((SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
        (realizationSimplexCoordsIso n).hom).hom y) =
      (((realization_representable_iso c₀).hom ≫ SemiSSet.toTop.{u}.map f ≫
        (toTopSimplexCoordsIso (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom).hom y) := by
    exact congrArg
      (fun g : SemiSSet.realization.{u}.obj (SemiSSet.stdSimplex.{u}.obj c₀) ⟶
        TopCat.of (LiftedClosedCoordSimplex n) => g.hom y)
      (realizationRepresentableCoordsIso_map f)
  have hs : (realization_representable_iso c₀).hom.hom y = ULift.up s := by
    apply ULift.ext
    rfl
  have htopEval :
      (toTopSimplexCoordsIso
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom.hom
          ((SemiSSet.toTop.{u}.map f).hom ((realization_representable_iso c₀).hom.hom y)) =
        ULift.up (stdSimplexCoordsEquiv n (StdSimplex.map
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom s)) := by
    calc
      (toTopSimplexCoordsIso
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom.hom
            ((SemiSSet.toTop.{u}.map f).hom ((realization_representable_iso c₀).hom.hom y)) =
          (toTopSimplexCoordsIso
            (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom.hom
              ((SemiSSet.toTop.{u}.map f).hom (ULift.up s)) := by
                exact congrArg
                  (fun z => (toTopSimplexCoordsIso
                    (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom.hom
                    ((SemiSSet.toTop.{u}.map f).hom z)) hs
      _ = _ := toTopSimplexCoordsIso_map f s
  rw [hEval', hIsoEval]
  change closedCoordBarycentricWeights n
      (ULift.down ((toTopSimplexCoordsIso
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom.hom
        ((SemiSSet.toTop.{u}.map f).hom ((realization_representable_iso c₀).hom.hom y)))) i = 0
  rw [htopEval]
  exact stdSimplexMap_weight_eq_zero_of_not_mem_range f s i hmissing

theorem hornRealizationToCoords_face {m : ℕ} (k i : Fin (m + 2)) (hik : i ≠ k)
    (s : StdSimplex ℝ (Fin (m + 1))) :
    ∃ x : SemiSSet.realization.{u}.obj (SemiSSet.horn.{u} (m + 1) k).toFunctor,
      (hornRealizationToCoords (m + 1) k).hom x =
        ULift.up (stdSimplexCoordsEquiv (m + 1) (StdSimplex.map
          (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i)) s)) := by
  classical
  let c := HomotopyHypothesis.Henry.SemiSimplexCategory.mk m
  let d := HomotopyHypothesis.Henry.SemiSimplexCategory.mk (m + 1)
  let face : SimplexCategory.mk m ⟶ SimplexCategory.mk (m + 1) :=
    SimplexCategory.Hom.mk (Fin.succAboveOrderEmb i).toOrderHom
  have hfaceMono : Mono face := by
    change Mono (SimplexCategory.δ i)
    infer_instance
  let f : HomotopyHypothesis.Henry.SemiSimplexCategory.mk m ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk (m + 1) :=
    ⟨face, hfaceMono⟩
  have hmissing : i ∉ Set.range (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom := by
    change i ∉ Set.range face.toOrderHom
    simp [face, SimplexCategory.Hom.toOrderHom_mk, Fin.range_succAboveOrderEmb]
  let P := (SemiSSet.horn.{u} (m + 1) k).toFunctor
  have hval : (ULift.up f : (SemiSSet.stdSimplex.{u}.obj d).obj (Opposite.op c)) ∈
      (SemiSSet.horn.{u} (m + 1) k).obj (Opposite.op c) := ⟨i, hik, hmissing⟩
  let e : P.Elements := Functor.elementsMk P (Opposite.op c) ⟨ULift.up f, hval⟩
  let leg := (Presheaf.coconeOfRepresentable P).ι.app (Opposite.op e)
  let s' : StdSimplex ℝ
      (Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj c).len + 1)) := by
    simpa [c, HomotopyHypothesis.Henry.SemiSimplexCategory.incl] using s
  have hs' : s' = s := by
    apply StdSimplex.ext
    ext j
    simp [s', c, HomotopyHypothesis.Henry.SemiSimplexCategory.incl]
  let y := (realization_representable_iso c).inv.hom (ULift.up s')
  refine ⟨(SemiSSet.realization.{u}.map leg).hom y, ?_⟩
  have hfactor : SemiSSet.realization.{u}.map leg ≫
      SemiSSet.realization.{u}.map (SemiSSet.horn.{u} (m + 1) k).ι =
        SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) := by
    exact (Functor.map_comp _ _ _).symm.trans
      (congrArg (SemiSSet.realization.{u}.map)
        (hornRepresentableMap_eq_stdSimplexMap (m + 1) k e))
  have hcoords : SemiSSet.realization.{u}.map leg ≫
      hornRealizationToCoords (m + 1) k =
        SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
          (realizationSimplexCoordsIso (m + 1)).hom := by
    change SemiSSet.realization.{u}.map leg ≫
      (SemiSSet.realization.{u}.map (SemiSSet.horn.{u} (m + 1) k).ι ≫
        (realizationSimplexCoordsIso (m + 1)).hom) = _
    rw [← Category.assoc, hfactor]
    rfl
  have hEval := congrArg (fun g => g.hom y) hcoords
  have hIsoEval := congrArg (fun g => g.hom y)
    (realizationRepresentableCoordsIso_map f)
  have hs : (realization_representable_iso c).hom.hom y = ULift.up s' := by
    simpa [y] using Iso.inv_hom_id_apply (realization_representable_iso c) (ULift.up s')
  have htopEval :
      (toTopSimplexCoordsIso d).hom.hom
        ((SemiSSet.toTop.{u}.map f).hom ((realization_representable_iso c).hom.hom y)) =
      ULift.up (stdSimplexCoordsEquiv (m + 1) (StdSimplex.map
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom s')) := by
    calc
      (toTopSimplexCoordsIso d).hom.hom
          ((SemiSSet.toTop.{u}.map f).hom ((realization_representable_iso c).hom.hom y)) =
        (toTopSimplexCoordsIso d).hom.hom
          ((SemiSSet.toTop.{u}.map f).hom (ULift.up s')) :=
            congrArg (fun z => (toTopSimplexCoordsIso d).hom.hom
              ((SemiSSet.toTop.{u}.map f).hom z)) hs
      _ = _ := by
        simpa [d] using toTopSimplexCoordsIso_map f s'
  have hMapFace : StdSimplex.map
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f).toOrderHom s' =
      StdSimplex.map (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i)) s := by
    rw [hs']
    change StdSimplex.map face.toOrderHom s =
      StdSimplex.map (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i)) s
    simp [face, SimplexCategory.δ, SimplexCategory.Hom.toOrderHom_mk]
  calc
    (hornRealizationToCoords (m + 1) k).hom ((SemiSSet.realization.{u}.map leg).hom y) =
        ((SemiSSet.realization.{u}.map leg ≫ hornRealizationToCoords (m + 1) k).hom y) := rfl
    _ = ((SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map f) ≫
        (realizationSimplexCoordsIso (m + 1)).hom).hom y) := hEval
    _ = (((realization_representable_iso c).hom ≫ SemiSSet.toTop.{u}.map f ≫
        (toTopSimplexCoordsIso d).hom).hom y) := hIsoEval
    _ = ULift.up (stdSimplexCoordsEquiv (m + 1) (StdSimplex.map
        (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i)) s)) :=
      htopEval.trans (congrArg ULift.up
        (congrArg (stdSimplexCoordsEquiv (m + 1)) hMapFace))

theorem hornRealizationToCoords_surjective (n : ℕ) (k : Fin (n + 1))
    (x : ClosedCoordSimplex n) (hx : x ∈ coordinateHorn n k) :
    ∃ y : SemiSSet.realization.{u}.obj (SemiSSet.horn.{u} n k).toFunctor,
      (hornRealizationToCoords n k).hom y = ULift.up x := by
  cases n with
  | zero =>
    obtain ⟨i, hik, hi⟩ := hx
    exact False.elim (hik (Fin.ext (by omega)))
  | succ n =>
    obtain ⟨i, hik, hi⟩ := hx
    let t := (stdSimplexCoordsEquiv (n + 1)).symm x
    have ht : t.weights i = 0 := by
      simpa [t, hornPrismWeight, closedCoordBarycentricWeights] using hi
    obtain ⟨s, hmap⟩ := exists_stdSimplex_preimage_face i t ht
    obtain ⟨y, hy⟩ := hornRealizationToCoords_face (m := n) k i hik s
    have hcoords : stdSimplexCoordsEquiv (n + 1)
        (StdSimplex.map (Fin.succAboveOrderEmb i) s) = x := by
      rw [hmap]
      exact Equiv.apply_symm_apply (stdSimplexCoordsEquiv (n + 1)) x
    exact ⟨y, hy.trans (congrArg ULift.up hcoords)⟩

/-- The realized horn maps homeomorphically to its coordinate faces. -/
noncomputable def hornRealizationHomeomorph (n : ℕ) (k : Fin (n + 1)) :
    SemiSSet.realization.{u}.obj (SemiSSet.horn.{u} n k).toFunctor ≃ₜ
      {z : LiftedClosedCoordSimplex.{u} n // z.down ∈ coordinateHorn n k} := by
  classical
  let f := (hornRealizationToCoords n k).hom
  have hf : ∀ x, (f x).down ∈ coordinateHorn n k := hornRealizationToCoords_mem n k
  let F := fun x => (⟨f x, hf x⟩ :
    {z : LiftedClosedCoordSimplex.{u} n // z.down ∈ coordinateHorn n k})
  have hInj : Function.Injective f := by
    have h := (Packages.realization_exists_finite_subcomplex
      (SemiSSet.stdSimplex.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))).1
        (SemiSSet.horn n k)
    exact (TopCat.homeoOfIso (realizationSimplexCoordsIso n)).injective.comp h
  have hBij : Function.Bijective F := by
    constructor
    · intro x y hxy
      exact hInj (congrArg Subtype.val hxy)
    · intro z
      obtain ⟨x, hx⟩ := hornRealizationToCoords_surjective.{u} n k z.val.down z.property
      refine ⟨x, Subtype.ext (hx.trans ?_)⟩
      exact ULift.ext _ _ rfl
  let e := Equiv.ofBijective F hBij
  letI := compactSpace_realization_horn.{u} n k
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    (f.continuous.subtype_mk hf)

end HomotopyHypothesis.Horn.DeformationRetraction
