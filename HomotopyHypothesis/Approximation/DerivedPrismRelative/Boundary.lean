import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.AnodyneCells.Proofs
import HomotopyHypothesis.Approximation.DerivedPrismCollapse.Proof
import HomotopyHypothesis.Approximation.DerivedPrismRelative.BoundarySupport
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdry
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdryIota
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdHom
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprismCos
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
import HomotopyHypothesis.Approximation.Topological.RelPrismApproximation.Part1
/-!
# Relative anodyne collapse of the derived cylinder

The relative derived-cylinder map is built by attaching the missing simplices in increasing
dimension. Each attachment is the image of the derived-cylinder boundary inclusion.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismRelative

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological

private theorem types_isPushout_of_cover {A B C P : Type u}
    {f : A ⟶ B} {g : A ⟶ C} {l : B ⟶ P} {r : C ⟶ P}
    (hcomm : ∀ a, l (f a) = r (g a)) (hl : Function.Injective l)
    (hr : Function.Injective r)
    (hcover : ∀ p, (PSigma fun b => l b = p) ⊕ (PSigma fun c => r c = p))
    (hoverlap : ∀ b c, l b = r c → ∃ a, f a = b ∧ g a = c) :
    IsPushout f g l r := by
  classical
  let condition : f ≫ l = g ≫ r := by
    ext a
    exact hcomm a
  let rep : ∀ p : P, (PSigma fun b : B => l b = p) ⊕ (PSigma fun c : C => r c = p) := hcover
  let desc : ∀ s : PushoutCocone f g, P ⟶ s.pt := fun s => ↾fun p =>
    match rep p with
    | Sum.inl ⟨b, _⟩ => s.inl b
    | Sum.inr ⟨c, _⟩ => s.inr c
  refine IsPushout.of_isColimit (c := PushoutCocone.mk l r condition)
    (PushoutCocone.IsColimit.mk condition desc ?_ ?_ ?_)
  · intro s
    apply ConcreteCategory.hom_ext
    intro b
    change desc s (l b) = s.inl b
    dsimp only [desc]
    cases hrep : rep (l b) with
    | inl h =>
        obtain ⟨b', hb'⟩ := h
        have : b' = b := hl (hb'.trans rfl)
        subst b'
        simp only [ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply, hrep]
    | inr h =>
        obtain ⟨c, hc⟩ := h
        obtain ⟨a, rfl, rfl⟩ := hoverlap b c hc.symm
        have hsq := congrArg (fun e : A ⟶ s.pt => e a) s.condition
        simpa only [types_comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply,
          hrep] using hsq.symm
  · intro s
    apply ConcreteCategory.hom_ext
    intro c
    change desc s (r c) = s.inr c
    dsimp only [desc]
    cases hrep : rep (r c) with
    | inl h =>
        obtain ⟨b, hb⟩ := h
        obtain ⟨a, rfl, rfl⟩ := hoverlap b c hb
        have hsq := congrArg (fun e : A ⟶ s.pt => e a) s.condition
        simpa only [types_comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply,
          hrep] using hsq
    | inr h =>
        obtain ⟨c', hc'⟩ := h
        have : c' = c := hr (hc'.trans rfl)
        subst c'
        simp only [ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply, hrep]
  · intro s m hm₁ hm₂
    apply ConcreteCategory.hom_ext
    intro p
    change m p = desc s p
    dsimp only [desc]
    cases hrep : rep p with
    | inl h =>
        obtain ⟨b, rfl⟩ := h
        simpa only [types_comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply,
          hrep] using congrArg (fun e : B ⟶ s.pt => e b) hm₁
    | inr h =>
        obtain ⟨c, rfl⟩ := h
        simpa only [types_comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply,
          hrep] using congrArg (fun e : C ⟶ s.pt => e c) hm₂

private theorem iso_app_apply_inv {A B : SemiSSet.{u}} (e : A ≅ B)
    (X : Henry.SemiSimplexCategoryᵒᵖ) (x : B.obj X) :
    e.hom.app X (e.inv.app X x) = x := by
  have h := congrArg (fun f => f.app X) e.inv_hom_id
  have h' := ConcreteCategory.congr_hom h x
  simpa only [NatTrans.comp_app, CategoryTheory.comp_apply, NatTrans.id_app,
    CategoryTheory.id_apply, CategoryTheory.hom_id] using h'

noncomputable abbrev sdLanElementsDiagram (X : SemiSSet.{u}) :=
  (Functor.Elements.π X).leftOp ⋙ sdCos.{u}

noncomputable def sdLanElementsDiagramIso (X : SemiSSet.{u}) :
    Presheaf.functorToRepresentables.{u} X ⋙ sdLan.{u} ≅ sdLanElementsDiagram X := by
  change (((Functor.Elements.π X).leftOp ⋙ uliftYoneda.{u}) ⋙ sdLan.{u}) ≅ _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.Elements.π X).leftOp
      (sdLanRepresentableIso)

noncomputable def sdLanElementsCocone (X : SemiSSet.{u}) :
    Cocone (sdLanElementsDiagram X) :=
  (Cocone.precompose (sdLanElementsDiagramIso X).inv).obj
    (sdLan.{u}.mapCocone (Presheaf.coconeOfRepresentable X))

noncomputable def sdLanElementsCocone_isColimit (X : SemiSSet.{u}) :
    IsColimit (sdLanElementsCocone X) := by
  letI : PreservesColimitsOfSize.{0, u} sdLan.{u} :=
    Presheaf.preservesColimitsOfSize_leftKanExtension.{0, 0, u, 0, 0, u + 1, u}
      sdCos.{u}
  exact (IsColimit.precomposeHomEquiv (sdLanElementsDiagramIso X).symm
      (sdLan.{u}.mapCocone (Presheaf.coconeOfRepresentable X))).symm
    (isColimitOfPreserves sdLan.{u} (Presheaf.colimitOfRepresentable X))

noncomputable def sdLanElementsColimitIso (X : SemiSSet.{u}) :
    sdLan.{u}.obj X ≅ colimit (sdLanElementsDiagram X) :=
  (sdLanElementsCocone_isColimit X).coconePointUniqueUpToIso (colimit.isColimit _)

noncomputable def dprismLanBoundaryToSideMap (k : ℕ) :
    dprismLan.{u}.obj (Henry.SemiSSet.boundary.{u} k).toFunctor ⟶
      (dprismSideComplex k).toSemiSSet.{u} :=
  (dprismLanElementsCocone_isColimit.{u}
    (Henry.SemiSSet.boundary.{u} k).toFunctor).desc
      (dprismLanBoundarySideCocone.{u} k)

theorem dprismLanBoundaryToSideMap_leg {k n : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
    (τ : (dprismCos.obj e.obj.unop).obj
      (op (Henry.SemiSimplexCategory.mk n))) :
    (dprismLanBoundaryToSideMap.{u} k).app (op (Henry.SemiSimplexCategory.mk n))
        (((dprismLanElementsCocone.{u}
          (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app (op e)).app
            (op (Henry.SemiSimplexCategory.mk n)) τ) =
      ((dprismLanBoundarySideCocone.{u} k).ι.app (op e)).app
        (op (Henry.SemiSimplexCategory.mk n)) τ := by
  let X : SemiSSet.{u} := (Henry.SemiSSet.boundary.{u} k).toFunctor
  let D : X.Elementsᵒᵖ ⥤ SemiSSet.{u} := dprismLanElementsDiagram.{u} X
  let C : Cocone D := dprismLanElementsCocone.{u} X
  let S := dprismLanBoundarySideCocone.{u} k
  let i := op e
  have h := (dprismLanElementsCocone_isColimit.{u} X).fac S i
  exact congrArg
    (fun f : dprismCos.{u}.obj e.obj.unop ⟶ (dprismSideComplex k).toSemiSSet.{u} =>
      f.app (op (Henry.SemiSimplexCategory.mk n)) τ) h

private theorem dprismSideZero_isEmpty (n : ℕ) :
    IsEmpty ((dprismSideComplex 0).toSemiSSet.{u}.obj
      (op (Henry.SemiSimplexCategory.mk n))) := by
  refine ⟨fun x => ?_⟩
  let σ := x.down
  let A : Finset (PV 0) := Finset.univ.image σ.1
  have hA : (dprismComplex 0).S A := σ.2.2.1
  obtain ⟨i, hiTop, hiMid⟩ := σ.2.2.2
  let j₀ : Fin (n + 1) := 0
  cases hvertex : σ.1 j₀ with
  | top j =>
      have hji : j = i := Fin.ext (by have := j.isLt; have := i.isLt; omega)
      have htop : PV.top i ∈ A := by
        apply Finset.mem_image.mpr
        exact ⟨j₀, Finset.mem_univ _, by rw [hvertex]; exact congrArg PV.top hji⟩
      exact hiTop htop
  | mid S =>
      have hmid : PV.mid S ∈ A := by
        apply Finset.mem_image.mpr
        exact ⟨j₀, Finset.mem_univ _, hvertex⟩
      obtain ⟨j, hj⟩ := hA.1 S hmid
      have hji : j = i := Fin.ext (by have := j.isLt; have := i.isLt; omega)
      exact hiMid S hmid (hji ▸ hj)

theorem dprismLanBoundaryToSideMap_isIso (k : ℕ) :
    IsIso (dprismLanBoundaryToSideMap.{u} k) := by
  classical
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  cases d with
  | op c =>
    cases c with
    | mk c =>
      cases c with
      | mk n =>
        rw [isIso_iff_bijective]
        constructor
        · intro x y hxy
          by_cases hk : 0 < k
          ·
            let X : SemiSSet.{u} := (Henry.SemiSSet.boundary.{u} k).toFunctor
            let D : X.Elementsᵒᵖ ⥤ SemiSSet.{u} := dprismLanElementsDiagram.{u} X
            let C : Cocone D := dprismLanElementsCocone.{u} X
            let ev : SemiSSet.{u} ⥤ Type u :=
              (evaluation (Henry.SemiSimplexCategoryᵒᵖ) (Type u)).obj
                (op (Henry.SemiSimplexCategory.mk n))
            let Dn := D ⋙ ev
            have hColim : IsColimit (ev.mapCocone C) :=
              isColimitOfPreserves ev
                (dprismLanElementsCocone_isColimit.{u} X)
            obtain ⟨i, τ, hτ⟩ := Types.jointly_surjective_of_isColimit hColim x
            obtain ⟨i', τ', hτ'⟩ := Types.jointly_surjective_of_isColimit hColim y
            have hside : ((dprismLanBoundarySideCocone.{u} k).ι.app i).app
                  (op (Henry.SemiSimplexCategory.mk n)) τ =
                ((dprismLanBoundarySideCocone.{u} k).ι.app i').app
                  (op (Henry.SemiSimplexCategory.mk n)) τ' := by
              let q := (dprismLanBoundaryToSideMap.{u} k).app
                (op (Henry.SemiSimplexCategory.mk n))
              have hleg : q (((C.ι.app i).app
                  (op (Henry.SemiSimplexCategory.mk n))) τ) =
                  ((dprismLanBoundarySideCocone.{u} k).ι.app i).app
                    (op (Henry.SemiSimplexCategory.mk n)) τ :=
                dprismLanBoundaryToSideMap_leg.{u} (k := k) (n := n) i.unop τ
              have hleg' : q (((C.ι.app i').app
                  (op (Henry.SemiSimplexCategory.mk n))) τ') =
                  ((dprismLanBoundarySideCocone.{u} k).ι.app i').app
                    (op (Henry.SemiSimplexCategory.mk n)) τ' :=
                dprismLanBoundaryToSideMap_leg.{u} (k := k) (n := n) i'.unop τ'
              exact hleg.symm.trans ((congrArg q hτ).trans
                (hxy.trans ((congrArg q hτ'.symm).trans hleg')))
            have hleg := boundary_side_representatives_equal.{u}
              i.unop i'.unop τ τ' hside
            exact hτ.symm.trans (hleg.trans hτ')
          · have hk0 : k = 0 := by omega
            subst k
            haveI : IsEmpty ((dprismLan.{u}.obj
                (Henry.SemiSSet.boundary.{u} 0).toFunctor).obj
                (op (Henry.SemiSimplexCategory.mk n))) :=
              ⟨fun x => (dprismSideZero_isEmpty n).false
                ((dprismLanBoundaryToSideMap.{u} 0).app
                  (op (Henry.SemiSimplexCategory.mk n)) x)⟩
            exact isEmptyElim x
        · intro z
          by_cases hk : 0 < k
          · obtain ⟨e, τ, hτ⟩ := exists_side_boundary_representation.{u}
              (k := k) (n := n) hk z
            refine ⟨((dprismLanElementsCocone.{u}
              (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app (op e)).app
                (op (Henry.SemiSimplexCategory.mk n)) τ, ?_⟩
            rw [dprismLanBoundaryToSideMap_leg.{u}]
            simpa [Henry.SemiSimplexCategory.mk, dprismLanBoundarySideCocone] using hτ
          · have hk0 : k = 0 := by omega
            subst k
            exact False.elim ((dprismSideZero_isEmpty n).false z)

noncomputable def dprismLanBoundarySideIso (k : ℕ) :
    dprismLan.obj (Henry.SemiSSet.boundary.{u} k).toFunctor ≅
      (dprismSideComplex k).toSemiSSet := by
  letI : IsIso (dprismLanBoundaryToSideMap.{u} k) :=
    dprismLanBoundaryToSideMap_isIso.{u} k
  exact asIso (dprismLanBoundaryToSideMap.{u} k)

theorem sdLanBoundary_leg {k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements) :
    (sdLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app (op e) ≫
      sdLan.map (Henry.SemiSSet.boundary.{u} k).ι ≫
      sdLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) =
        sdCos.map (boundaryElementFace e) := by
  let c := e.obj.unop
  let f := uliftYonedaEquiv.symm e.val
  let g := (Henry.SemiSSet.boundary.{u} k).ι
  have hchar : f ≫ g = Henry.SemiSSet.stdSimplex.map (boundaryElementFace e) :=
    boundaryElement_map_eq_stdSimplexMap e
  have hmap : sdLan.map f ≫ sdLan.map g = sdLan.map (f ≫ g) :=
    (sdLan.map_comp f g).symm
  have hnat : sdLan.map (Henry.SemiSSet.stdSimplex.map (boundaryElementFace e)) ≫
      sdLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) =
        sdLanRepresentableIso.hom.app c ≫ sdCos.map (boundaryElementFace e) := by
    simpa using sdLanRepresentableIso.hom.naturality (boundaryElementFace e)
  change (sdLanRepresentableIso.inv.app c ≫ sdLan.map f) ≫
      sdLan.map g ≫ sdLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) = _
  calc
    _ = ((sdLanRepresentableIso.inv.app c ≫ sdLan.map f) ≫ sdLan.map g) ≫
        sdLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) := by rfl
    _ = (sdLanRepresentableIso.inv.app c ≫ (sdLan.map f ≫ sdLan.map g)) ≫
        sdLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) := by
          simp only [Category.assoc]
    _ = (sdLanRepresentableIso.inv.app c ≫ sdLan.map (f ≫ g)) ≫
        sdLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) := by rw [hmap]
    _ = (sdLanRepresentableIso.inv.app c ≫
        sdLan.map (Henry.SemiSSet.stdSimplex.map (boundaryElementFace e))) ≫
          sdLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) := by rw [hchar]
    _ = sdLanRepresentableIso.inv.app c ≫
        (sdLanRepresentableIso.hom.app c ≫ sdCos.map (boundaryElementFace e)) := by
          rw [Category.assoc, hnat]
    _ = sdCos.map (boundaryElementFace e) := by simp [Category.assoc]

theorem exists_sd_boundary_representation {k n : ℕ} (hk : 0 < k)
    (σ : (sdComplex k).Simplex n)
    (hSide : ∃ i : Fin (k + 1),
      PV.top i ∉ Finset.univ.image σ.1 ∧
        ∀ S, PV.mid S ∈ Finset.univ.image σ.1 → i ∉ S) :
    ∃ (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
      (τ : (sdCos.obj e.obj.unop).obj (op (Henry.SemiSimplexCategory.mk n))),
      ∀ j, PV.map (boundaryElementFace e).1.toOrderHom (τ.down.1 j) = σ.1 j := by
  let z : (dprismSideComplex k).Simplex n :=
    ⟨σ.1, σ.2.1, ⟨σ.2.2.1, hSide⟩⟩
  obtain ⟨e, τ₀, hτ₀⟩ := exists_side_boundary_representation hk (ULift.up z)
  let θ := boundaryElementFace e
  have hmap : ∀ j, PV.map θ.1.toOrderHom (τ₀.down.1 j) = σ.1 j := by
    intro j
    change (faceDprismToSideMap θ (boundaryElementFace_not_surjective e)).app
        (op (Henry.SemiSimplexCategory.mk n)) τ₀ = ULift.up z at hτ₀
    have h := congrArg (fun x : ULift ((dprismSideComplex k).Simplex n) => x.down.1 j) hτ₀
    change PV.map θ.1.toOrderHom (τ₀.down.1 j) = σ.1 j
    change PV.map θ.1.toOrderHom (τ₀.down.1 j) = σ.1 j at h
    exact h
  have hNoTop : ∀ i, PV.top i ∉ Finset.univ.image τ₀.down.1 := by
    intro i hi
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hi
    have hvertex := hmap j
    rw [hj] at hvertex
    simp only [PV.map] at hvertex
    have hσtop : PV.top (θ.1.toOrderHom i) ∈ Finset.univ.image σ.1 := by
      apply Finset.mem_image.mpr
      exact ⟨j, Finset.mem_univ j, hvertex.symm⟩
    exact σ.2.2.2 _ hσtop
  let τ : (sdComplex e.obj.unop.obj.len).Simplex n :=
    ⟨τ₀.down.1, τ₀.down.2.1, ⟨τ₀.down.2.2, hNoTop⟩⟩
  refine ⟨e, ULift.up τ, ?_⟩
  intro j
  exact hmap j

private theorem sdLanToDprism_representable (c : Henry.SemiSimplexCategory) :
    sdLanRepresentableIso.{u}.hom.app c ≫ sdToDprismCos.{u}.app c =
      sdLanToDprism.{u}.app (Henry.SemiSSet.stdSimplex.obj c) ≫
        dprismLanRepresentableIso.{u}.hom.app c := by
  let α := Henry.SemiSSet.stdSimplex.leftKanExtensionUnit sdCos.{u}
  let β := Henry.SemiSSet.stdSimplex.leftKanExtensionUnit dprismCos.{u}
  have hfac := sdLan.{u}.descOfIsLeftKanExtension_fac_app α dprismLan.{u}
    (sdToDprismCos.{u} ≫ β) c
  have hfac' : α.app c ≫ sdLanToDprism.{u}.app
      (Henry.SemiSSet.stdSimplex.obj c) = sdToDprismCos.{u}.app c ≫ β.app c := by
    change α.app c ≫
        (sdLan.{u}.descOfIsLeftKanExtension α dprismLan.{u}
          (sdToDprismCos.{u} ≫ β)).app (Henry.SemiSSet.stdSimplex.obj c) =
      (sdToDprismCos.{u} ≫ β).app c
    exact hfac
  have hα : sdLanRepresentableIso.{u}.hom.app c ≫ α.app c = 𝟙 _ := by
    exact Iso.hom_inv_id_app (sdLanRepresentableIso.{u}) c
  have hβ : β.app c ≫ dprismLanRepresentableIso.{u}.hom.app c = 𝟙 _ := by
    exact Iso.inv_hom_id_app (dprismLanRepresentableIso.{u}) c
  calc
    sdLanRepresentableIso.{u}.hom.app c ≫ sdToDprismCos.{u}.app c =
      sdLanRepresentableIso.{u}.hom.app c ≫
          (sdToDprismCos.{u}.app c ≫ β.app c) ≫
            dprismLanRepresentableIso.{u}.hom.app c := by
              simp only [Category.assoc, hβ, Category.comp_id]
    _ = sdLanRepresentableIso.{u}.hom.app c ≫
          (α.app c ≫ sdLanToDprism.{u}.app
            (Henry.SemiSSet.stdSimplex.obj c)) ≫
              dprismLanRepresentableIso.{u}.hom.app c := by rw [hfac'.symm]
    _ = sdLanToDprism.{u}.app (Henry.SemiSSet.stdSimplex.obj c) ≫
          dprismLanRepresentableIso.{u}.hom.app c := by
            simpa [Category.assoc] using congrArg
              (fun f => f ≫ sdLanToDprism.{u}.app
                (Henry.SemiSSet.stdSimplex.obj c) ≫
                dprismLanRepresentableIso.{u}.hom.app c) hα

private theorem sdLanToDprism_representable_inv (c : Henry.SemiSimplexCategory) :
    sdLanRepresentableIso.{u}.inv.app c ≫
        sdLanToDprism.{u}.app (Henry.SemiSSet.stdSimplex.obj c) =
      sdToDprismCos.{u}.app c ≫ dprismLanRepresentableIso.{u}.inv.app c := by
  apply (cancel_mono (dprismLanRepresentableIso.{u}.hom.app c)).1
  calc
    _ = sdLanRepresentableIso.{u}.inv.app c ≫
        (sdLanToDprism.{u}.app (Henry.SemiSSet.stdSimplex.obj c) ≫
          dprismLanRepresentableIso.{u}.hom.app c) := by simp [Category.assoc]
    _ = sdLanRepresentableIso.{u}.inv.app c ≫
        (sdLanRepresentableIso.{u}.hom.app c ≫ sdToDprismCos.{u}.app c) := by
          rw [← sdLanToDprism_representable.{u} c]
    _ = (sdToDprismCos.{u}.app c ≫ dprismLanRepresentableIso.{u}.inv.app c) ≫
        dprismLanRepresentableIso.{u}.hom.app c := by
          simpa [Category.assoc] using congrArg
            (fun f => f ≫ sdToDprismCos.{u}.app c)
            (Iso.inv_hom_id_app sdLanRepresentableIso.{u} c)

private theorem sdLanElementsCocone_map_dprism {X : SemiSSet.{u}}
    (e : X.Elements) :
    (sdLanElementsCocone.{u} X).ι.app (op e) ≫ sdLanToDprism.{u}.app X =
      sdToDprismCos.{u}.app e.obj.unop ≫
        (dprismLanElementsCocone.{u} X).ι.app (op e) := by
  let c := e.obj.unop
  let f := uliftYonedaEquiv.symm e.val
  change (sdLanRepresentableIso.{u}.inv.app c ≫ sdLan.{u}.map f) ≫
      sdLanToDprism.{u}.app X =
    sdToDprismCos.{u}.app c ≫
      (dprismLanRepresentableIso.{u}.inv.app c ≫ dprismLan.{u}.map f)
  calc
    _ = sdLanRepresentableIso.{u}.inv.app c ≫
        (sdLan.{u}.map f ≫ sdLanToDprism.{u}.app X) := by simp [Category.assoc]
    _ = sdLanRepresentableIso.{u}.inv.app c ≫
        (sdLanToDprism.{u}.app (Henry.SemiSSet.stdSimplex.obj c) ≫
          dprismLan.{u}.map f) := by
            rw [sdLanToDprism.naturality f]
    _ = (sdLanRepresentableIso.{u}.inv.app c ≫
        sdLanToDprism.{u}.app (Henry.SemiSSet.stdSimplex.obj c)) ≫
          dprismLan.{u}.map f := by
            simp only [Category.assoc]
    _ = (sdToDprismCos.{u}.app c ≫ dprismLanRepresentableIso.{u}.inv.app c) ≫
        dprismLan.{u}.map f := by
          exact congrArg (fun g => g ≫ dprismLan.{u}.map f)
            (sdLanToDprism_representable_inv.{u} c)
    _ = sdToDprismCos.{u}.app c ≫
        (dprismLanRepresentableIso.{u}.inv.app c ≫ dprismLan.{u}.map f) := by
          simp [Category.assoc]

private noncomputable def sdCosToDprismBdry (k : ℕ) :
    sdCos.{u}.obj (Henry.SemiSimplexCategory.mk k) ⟶ dprismBdry.{u} k := by
  simpa [sdCos] using (sdToDprismBdryHom k).toSemiSSet

private noncomputable def sdSimplexToDprismBdry (k : ℕ) :
    sdLan.{u}.obj (Henry.SemiSSet.stdSimplex.obj
      (Henry.SemiSimplexCategory.mk k)) ⟶ dprismBdry.{u} k :=
  sdLanRepresentableIso.{u}.hom.app (Henry.SemiSimplexCategory.mk k) ≫
    sdCosToDprismBdry k

private noncomputable def dprismBoundaryToDprismBdry (k : ℕ) :
    dprismLan.{u}.obj (Henry.SemiSSet.boundary.{u} k).toFunctor ⟶ dprismBdry.{u} k :=
  dprismLanBoundaryToSideMap.{u} k ≫ (dprismSideToBdryHom k).toSemiSSet

private theorem sdCosFaceToDprismBdry_eq {k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements) :
    sdCos.{u}.map (boundaryElementFace e) ≫ (sdToDprismBdryHom k).toSemiSSet =
      sdToDprismCos.{u}.app e.obj.unop ≫
        (dprismLanBoundarySideCocone.{u} k).ι.app (op e) ≫
          (dprismSideToBdryHom k).toSemiSSet := by
  ext d τ
  rfl

private theorem sdBoundaryToDprismBdry_comm (k : ℕ) :
    sdLan.{u}.map (Henry.SemiSSet.boundary.{u} k).ι ≫ sdSimplexToDprismBdry.{u} k =
      sdLanToDprism.{u}.app (Henry.SemiSSet.boundary.{u} k).toFunctor ≫
        dprismBoundaryToDprismBdry.{u} k := by
  let X := (Henry.SemiSSet.boundary.{u} k).toFunctor
  let C := sdLanElementsCocone.{u} X
  let D := dprismLanElementsCocone.{u} X
  apply (sdLanElementsCocone_isColimit.{u} X).hom_ext
  intro e
  let θ := boundaryElementFace e.unop
  have hleft := sdLanBoundary_leg.{u} e.unop
  have htransfer := sdLanElementsCocone_map_dprism.{u} (X := X) e.unop
  have htransfer' : C.ι.app e ≫ sdLanToDprism.{u}.app X =
      sdToDprismCos.{u}.app e.unop.obj.unop ≫ D.ι.app e := by
    change (sdLanElementsCocone.{u} X).ι.app (op e.unop) ≫
        sdLanToDprism.{u}.app X =
      sdToDprismCos.{u}.app e.unop.obj.unop ≫
        (dprismLanElementsCocone.{u} X).ι.app (op e.unop)
    exact htransfer
  have hside : D.ι.app e ≫ dprismLanBoundaryToSideMap.{u} k =
      (dprismLanBoundarySideCocone.{u} k).ι.app e := by
    exact (dprismLanElementsCocone_isColimit.{u} X).fac _ e
  calc
    C.ι.app e ≫ sdLan.{u}.map (Henry.SemiSSet.boundary.{u} k).ι ≫
        sdSimplexToDprismBdry.{u} k =
      sdCos.{u}.map θ ≫ (sdToDprismBdryHom k).toSemiSSet := by
        change ((sdLanElementsCocone.{u} X).ι.app (op e.unop) ≫
            sdLan.{u}.map (Henry.SemiSSet.boundary.{u} k).ι ≫
              sdLanRepresentableIso.{u}.hom.app
                (Henry.SemiSimplexCategory.mk k)) ≫
            (sdToDprismBdryHom k).toSemiSSet = _
        rw [hleft]
    _ = sdToDprismCos.{u}.app e.unop.obj.unop ≫
        (dprismLanBoundarySideCocone.{u} k).ι.app e ≫
          (dprismSideToBdryHom k).toSemiSSet :=
            sdCosFaceToDprismBdry_eq.{u} e.unop
    _ = C.ι.app e ≫ sdLanToDprism.{u}.app X ≫
        dprismBoundaryToDprismBdry.{u} k := by
          calc
            _ = sdToDprismCos.{u}.app e.unop.obj.unop ≫
                (D.ι.app e ≫ dprismLanBoundaryToSideMap.{u} k) ≫
                  (dprismSideToBdryHom k).toSemiSSet := by
                    exact congrArg
                      (fun f => sdToDprismCos.{u}.app e.unop.obj.unop ≫ f ≫
                        (dprismSideToBdryHom k).toSemiSSet) hside.symm
            _ = (C.ι.app e ≫ sdLanToDprism.{u}.app X) ≫
                  dprismLanBoundaryToSideMap.{u} k ≫
                    (dprismSideToBdryHom k).toSemiSSet := by
                      calc
                        _ = (sdToDprismCos.{u}.app e.unop.obj.unop ≫ D.ι.app e) ≫
                              dprismLanBoundaryToSideMap.{u} k ≫
                                (dprismSideToBdryHom k).toSemiSSet := by
                                  exact congrArg (fun f => f ≫
                                    (dprismSideToBdryHom k).toSemiSSet)
                                    (Category.assoc
                                      (sdToDprismCos.{u}.app e.unop.obj.unop)
                                      (D.ι.app e) (dprismLanBoundaryToSideMap.{u} k)).symm
                        _ = (C.ι.app e ≫ sdLanToDprism.{u}.app X) ≫
                              dprismLanBoundaryToSideMap.{u} k ≫
                                (dprismSideToBdryHom k).toSemiSSet :=
                                  (congrArg (fun f => f ≫
                                    dprismLanBoundaryToSideMap.{u} k ≫
                                      (dprismSideToBdryHom k).toSemiSSet)
                                    htransfer').symm
            _ = C.ι.app e ≫ sdLanToDprism.{u}.app X ≫
                  dprismBoundaryToDprismBdry.{u} k := by
                    rfl

private theorem dprismLanBoundary_square_isPushout (k : ℕ) :
    IsPushout
      (sdLan.{u}.map (Henry.SemiSSet.boundary.{u} k).ι)
      (sdLanToDprism.{u}.app (Henry.SemiSSet.boundary.{u} k).toFunctor)
      (sdSimplexToDprismBdry.{u} k)
      (dprismBoundaryToDprismBdry.{u} k) := by
  classical
  have hcomm := sdBoundaryToDprismBdry_comm.{u} k
  apply IsPushout.of_forall_isPushout_app
  intro X
  cases X with
  | op c =>
    cases c with
    | mk c =>
      cases c with
      | mk n =>
        apply types_isPushout_of_cover
        · intro a
          exact congrFun (congrArg (fun f => f.app (op { obj := { len := n } })
            ) hcomm) a
        · intro x y hxy
          have hxy₀ : ((sdToDprismBdryHom k).toSemiSSet.app
              (op { obj := { len := n } }))
              (((sdLanRepresentableIso.{u}.hom.app
                (Henry.SemiSimplexCategory.mk k)).app
                (op { obj := { len := n } })) x) =
            ((sdToDprismBdryHom k).toSemiSSet.app
              (op { obj := { len := n } }))
              (((sdLanRepresentableIso.{u}.hom.app
                (Henry.SemiSimplexCategory.mk k)).app
                (op { obj := { len := n } })) y) := by
            exact hxy
          have hinc : Function.Injective ((sdToDprismBdryHom k).toSemiSSet.app
              (op { obj := { len := n } })) := by
            intro x y h
            apply ULift.ext
            apply Subtype.ext
            exact congrArg (fun z => z.down.1) h
          have hxy' :
              ((sdLanRepresentableIso.{u}.hom.app
                (Henry.SemiSimplexCategory.mk k)).app
                (op { obj := { len := n } })) x =
              ((sdLanRepresentableIso.{u}.hom.app
                (Henry.SemiSimplexCategory.mk k)).app
                (op { obj := { len := n } })) y := by
            exact hinc hxy₀
          have hinj : Function.Injective ((sdLanRepresentableIso.{u}.hom.app
              (Henry.SemiSimplexCategory.mk k)).app
              (op { obj := { len := n } })) := by
            haveI : Mono ((sdLanRepresentableIso.{u}.hom.app
                (Henry.SemiSimplexCategory.mk k)).app
                (op { obj := { len := n } })) := inferInstance
            exact (mono_iff_injective _).1 inferInstance
          exact hinj hxy'
        · intro x y hxy
          have hxy₀ : ((dprismSideToBdryHom k).toSemiSSet.app
              (op { obj := { len := n } }))
              (((dprismLanBoundaryToSideMap.{u} k).app
                (op { obj := { len := n } })) x) =
            ((dprismSideToBdryHom k).toSemiSSet.app
              (op { obj := { len := n } }))
              (((dprismLanBoundaryToSideMap.{u} k).app
                (op { obj := { len := n } })) y) := by
            simpa only [dprismBoundaryToDprismBdry, NatTrans.comp_app,
              hom_comp, Function.comp_apply, types_comp_apply] using hxy
          have hinc : Function.Injective ((dprismSideToBdryHom k).toSemiSSet.app
              (op { obj := { len := n } })) := by
            intro x y h
            apply ULift.ext
            apply Subtype.ext
            exact congrArg (fun z => z.down.1) h
          have hxy' :
              ((dprismLanBoundarySideIso.{u} k).hom.app
                (op { obj := { len := n } })) x =
              ((dprismLanBoundarySideIso.{u} k).hom.app
                (op { obj := { len := n } })) y := by
            simpa [dprismLanBoundarySideIso] using hinc hxy₀
          have hinj : Function.Injective ((dprismLanBoundarySideIso.{u} k).hom.app
              (op { obj := { len := n } })) := by
            haveI : Mono ((dprismLanBoundarySideIso.{u} k).hom.app
                (op { obj := { len := n } })) := inferInstance
            exact (mono_iff_injective _).1 inferInstance
          exact hinj hxy'
        · intro p
          let σ : (dprismBdryComplex k).Simplex n := p.down
          have hcase := (dprismBdry_S_iff k (Finset.univ.image σ.1)).mp σ.2.2
          by_cases hsd : (sdComplex k).S (Finset.univ.image σ.1)
          · let σ' : (sdComplex k).Simplex n := ⟨σ.1, σ.2.1, hsd⟩
            let σcos : (sdCos.{u}.obj (Henry.SemiSimplexCategory.mk k)).obj
                (op { obj := { len := n } }) := by
              simpa [sdCos, Complex.toSemiSSet] using (ULift.up σ')
            let b := ((sdLanRepresentableIso.{u}.inv.app
              (Henry.SemiSimplexCategory.mk k)).app
              (op { obj := { len := n } })) σcos
            refine Sum.inl ⟨b, ?_⟩
            change ((sdSimplexToDprismBdry.{u} k).app
              (op { obj := { len := n } })) b = p
            have hpoint := iso_app_apply_inv
              (sdLanRepresentableIso.{u}.app (Henry.SemiSimplexCategory.mk k))
              (op { obj := { len := n } }) σcos
            change (ConcreteCategory.hom
                ((sdLanRepresentableIso.{u}.hom.app
                  (Henry.SemiSimplexCategory.mk k)).app
                  (op { obj := { len := n } })))
                ((ConcreteCategory.hom
                  ((sdLanRepresentableIso.{u}.inv.app
                    (Henry.SemiSimplexCategory.mk k)).app
                    (op { obj := { len := n } }))) σcos) = σcos at hpoint
            change ((sdLanRepresentableIso.{u}.hom.app
                (Henry.SemiSimplexCategory.mk k) ≫
                sdCosToDprismBdry k).app
                (op { obj := { len := n } }))
                (((sdLanRepresentableIso.{u}.inv.app
                  (Henry.SemiSimplexCategory.mk k)).app
                  (op { obj := { len := n } })) σcos) = p
            simp only [NatTrans.comp_app, CategoryTheory.comp_apply]
            rw [hpoint]
            apply ULift.ext
            apply Subtype.ext
            rfl
          · have hside : (dprismSideComplex k).S (Finset.univ.image σ.1) :=
              hcase.resolve_left hsd
            by_cases hk : 0 < k
            · let σ' : (dprismSideComplex k).Simplex n := ⟨σ.1, σ.2.1, hside⟩
              let σside : (dprismSideComplex k).toSemiSSet.{u}.obj
                  (op { obj := { len := n } }) := by
                simpa [Complex.toSemiSSet] using (ULift.up σ')
              let c := ((dprismLanBoundarySideIso.{u} k).inv.app
                (op { obj := { len := n } })) σside
              refine Sum.inr ⟨c, ?_⟩
              change ((dprismBoundaryToDprismBdry.{u} k).app
                (op { obj := { len := n } })) c = p
              letI : IsIso (dprismLanBoundaryToSideMap.{u} k) :=
                dprismLanBoundaryToSideMap_isIso.{u} k
              have hpoint := iso_app_apply_inv
                (asIso (dprismLanBoundaryToSideMap.{u} k))
                (op { obj := { len := n } }) σside
              change (ConcreteCategory.hom
                  ((dprismLanBoundaryToSideMap.{u} k).app
                    (op { obj := { len := n } })))
                  ((ConcreteCategory.hom
                    ((dprismLanBoundarySideIso.{u} k).inv.app
                      (op { obj := { len := n } }))) σside) = σside at hpoint
              change ((dprismLanBoundaryToSideMap.{u} k ≫
                  (dprismSideToBdryHom k).toSemiSSet).app
                  (op { obj := { len := n } }))
                  (((dprismLanBoundarySideIso.{u} k).inv.app
                    (op { obj := { len := n } })) σside) = p
              simp only [NatTrans.comp_app, CategoryTheory.comp_apply]
              rw [hpoint]
              apply ULift.ext
              apply Subtype.ext
              rfl
            · have hk0 : k = 0 := by omega
              subst k
              haveI : IsEmpty ((dprismSideComplex 0).toSemiSSet.{u}.obj
                  (op { obj := { len := n } })) := dprismSideZero_isEmpty n
              exact False.elim ((dprismSideZero_isEmpty n).false
                (ULift.up.{u, 0} ⟨σ.1, σ.2.1, hside⟩))
        · intro b c hbc
          let σ : (sdComplex k).Simplex n :=
            ((sdLanRepresentableIso.{u}.hom.app
              (Henry.SemiSimplexCategory.mk k)).app
              (op { obj := { len := n } }) b).down
          let σside : (dprismSideComplex k).Simplex n :=
            ((dprismLanBoundarySideIso.{u} k).hom.app
              (op { obj := { len := n } }) c).down
          have hvertices : σ.1 = σside.1 := by
            have hbc' : ((sdCosToDprismBdry k).app
                (op { obj := { len := n } }))
                (((sdLanRepresentableIso.{u}.hom.app
                  (Henry.SemiSimplexCategory.mk k)).app
                  (op { obj := { len := n } })) b) =
              ((dprismSideToBdryHom k).toSemiSSet.app
                (op { obj := { len := n } }))
                (((dprismLanBoundaryToSideMap.{u} k).app
                  (op { obj := { len := n } })) c) := by
              simpa only [sdSimplexToDprismBdry, dprismBoundaryToDprismBdry,
                NatTrans.comp_app, CategoryTheory.comp_apply] using hbc
            have hleft : ((((sdCosToDprismBdry k).app
                (op { obj := { len := n } }))
                (((sdLanRepresentableIso.{u}.hom.app
                  (Henry.SemiSimplexCategory.mk k)).app
                  (op { obj := { len := n } })) b)).down).1 = σ.1 := rfl
            have hright : ((((dprismSideToBdryHom k).toSemiSSet.app
                (op { obj := { len := n } }))
                (((dprismLanBoundaryToSideMap.{u} k).app
                  (op { obj := { len := n } })) c)).down).1 = σside.1 := rfl
            calc
              σ.1 = ((((sdCosToDprismBdry k).app
                  (op { obj := { len := n } }))
                  (((sdLanRepresentableIso.{u}.hom.app
                    (Henry.SemiSimplexCategory.mk k)).app
                    (op { obj := { len := n } })) b)).down).1 := hleft.symm
              _ = ((((dprismSideToBdryHom k).toSemiSSet.app
                  (op { obj := { len := n } }))
                  (((dprismLanBoundaryToSideMap.{u} k).app
                    (op { obj := { len := n } })) c)).down).1 := by
                    exact congrArg (fun z : (dprismBdryComplex k).toSemiSSet.{u}.obj
                      (op { obj := { len := n } }) => z.down.1) hbc'
              _ = σside.1 := hright
          have hside : (dprismSideComplex k).S (Finset.univ.image σ.1) := by
            rw [hvertices]
            exact σside.2.2
          by_cases hk : 0 < k
          · obtain ⟨e, τ, hτ⟩ := exists_sd_boundary_representation.{u}
              (k := k) (n := n) hk σ hside.2
            let a := ((sdLanElementsCocone.{u}
              (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app (op e)).app
                (op { obj := { len := n } }) τ
            have hface : ((sdLanRepresentableIso.{u}.hom.app
                (Henry.SemiSimplexCategory.mk k)).app
                (op { obj := { len := n } }))
                (((sdLan.{u}.map (Henry.SemiSSet.boundary.{u} k).ι).app
                  (op { obj := { len := n } })) a) = ULift.up σ := by
              have hleg := congrArg (fun f => f.app
                (op { obj := { len := n } }) τ)
                (sdLanBoundary_leg.{u} (k := k) e)
              have hmap : (sdCos.{u}.map (boundaryElementFace e)).app
                  (op { obj := { len := n } }) τ = ULift.up σ := by
                apply ULift.ext
                apply Subtype.ext
                funext j
                exact hτ j
              have hleg' : ((sdLanRepresentableIso.{u}.hom.app
                  (Henry.SemiSimplexCategory.mk k)).app
                  (op { obj := { len := n } }))
                  (((sdLan.{u}.map (Henry.SemiSSet.boundary.{u} k).ι).app
                    (op { obj := { len := n } })) a) =
                (sdCos.{u}.map (boundaryElementFace e)).app
                  (op { obj := { len := n } }) τ := by
                change ((sdLanRepresentableIso.{u}.hom.app
                  (Henry.SemiSimplexCategory.mk k)).app
                  (op { obj := { len := n } }))
                    (((sdLan.{u}.map (Henry.SemiSSet.boundary.{u} k).ι).app
                      (op { obj := { len := n } })) a) =
                  (sdCos.{u}.map (boundaryElementFace e)).app
                    (op { obj := { len := n } }) τ at hleg
                exact hleg
              exact hleg'.trans hmap
            have hfa : ((sdLan.{u}.map (Henry.SemiSSet.boundary.{u} k).ι).app
                (op { obj := { len := n } })) a = b := by
              have hαb : ((sdLanRepresentableIso.{u}.hom.app
                  (Henry.SemiSimplexCategory.mk k)).app
                  (op { obj := { len := n } })) b = ULift.up σ := rfl
              have hinj : Function.Injective ((sdLanRepresentableIso.{u}.hom.app
                  (Henry.SemiSimplexCategory.mk k)).app
                  (op { obj := { len := n } })) := by
                haveI : Mono ((sdLanRepresentableIso.{u}.hom.app
                    (Henry.SemiSimplexCategory.mk k)).app
                    (op { obj := { len := n } })) := inferInstance
                exact (mono_iff_injective _).1 inferInstance
              exact hinj (hface.trans hαb.symm)
            have hgc : ((sdLanToDprism.{u}.app
                (Henry.SemiSSet.boundary.{u} k).toFunctor).app
                (op { obj := { len := n } })) a = c := by
              have hcomm' := congrFun (congrArg (fun f => f.app
                (op { obj := { len := n } })) hcomm) a
              have hr : Function.Injective ((dprismBoundaryToDprismBdry.{u} k).app
                  (op { obj := { len := n } })) := by
                intro x y hxy
                have hinc : Function.Injective
                    ((dprismSideToBdryHom k).toSemiSSet.app
                      (op { obj := { len := n } })) := by
                  intro s t h
                  apply ULift.ext
                  apply Subtype.ext
                  exact congrArg (fun z => z.down.1) h
                have hmap : ((dprismLanBoundaryToSideMap.{u} k).app
                    (op { obj := { len := n } })) x =
                  ((dprismLanBoundaryToSideMap.{u} k).app
                    (op { obj := { len := n } })) y := by
                  apply hinc
                  simpa only [dprismBoundaryToDprismBdry, NatTrans.comp_app,
                    CategoryTheory.comp_apply] using hxy
                have hside : ((dprismLanBoundarySideIso.{u} k).hom.app
                    (op { obj := { len := n } })) x =
                  ((dprismLanBoundarySideIso.{u} k).hom.app
                    (op { obj := { len := n } })) y := by
                  simpa [dprismLanBoundarySideIso] using hmap
                haveI : Mono ((dprismLanBoundarySideIso.{u} k).hom.app
                    (op { obj := { len := n } })) := inferInstance
                exact (mono_iff_injective _).1 inferInstance hside
              have hEqR := hcomm'.symm.trans
                (congrArg ((sdSimplexToDprismBdry.{u} k).app
                  (op { obj := { len := n } })) hfa)
              exact hr (hEqR.trans hbc)
            exact ⟨a, hfa, hgc⟩
          · have hk0 : k = 0 := by omega
            subst k
            haveI : IsEmpty ((dprismSideComplex 0).toSemiSSet.{u}.obj
                (op { obj := { len := n } })) := dprismSideZero_isEmpty n
            exact False.elim ((dprismSideZero_isEmpty n).false (ULift.up.{u, 0} σside))


private theorem dprismLanBoundaryToSide_comp (k : ℕ) :
    dprismLanBoundaryToSideMap.{u} k ≫
        (dprismSideToDprismHom k).toSemiSSet =
      dprismLan.{u}.map (Henry.SemiSSet.boundary.{u} k).ι ≫
        dprismLanRepresentableIso.{u}.hom.app
          (Henry.SemiSimplexCategory.mk k) := by
  let X := (Henry.SemiSSet.boundary.{u} k).toFunctor
  apply (dprismLanElementsCocone_isColimit.{u} X).hom_ext
  intro e
  erw [← Category.assoc,
    (dprismLanElementsCocone_isColimit.{u} X).fac]
  change (faceDprismToSide (boundaryElementFace e.unop)
      (boundaryElementFace_not_surjective e.unop)).toSemiSSet ≫
    (dprismSideToDprismHom k).toSemiSSet = _
  exact (dprismCos_map_factors_side.{u} (boundaryElementFace e.unop)
    (boundaryElementFace_not_surjective e.unop)).trans
      (dprismLanBoundary_leg.{u} e.unop).symm

/-- The relative derived-cylinder map of a simplex boundary is anodyne. -/
theorem anodyne_dprismLan_boundary (k : ℕ) :
    anodyne (pushout.desc
      (sdLanToDprism.{u}.app
        (Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk k)))
      (dprismLan.{u}.map (Henry.SemiSSet.boundary.{u} k).ι)
      (sdLanToDprism.{u}.naturality (Henry.SemiSSet.boundary.{u} k).ι)) := by
  let c := Henry.SemiSimplexCategory.mk k
  let sq := dprismLanBoundary_square_isPushout.{u} k
  let e := sq.isoPushout.symm
  let d : dprismLan.{u}.obj (Henry.SemiSSet.stdSimplex.obj c) ≅ dprism.{u} k :=
    dprismLanRepresentableIso.{u}.app c
  have hfac :
      pushout.desc (sdLanToDprism.{u}.app (Henry.SemiSSet.stdSimplex.obj c))
        (dprismLan.{u}.map (Henry.SemiSSet.boundary.{u} k).ι)
        (sdLanToDprism.{u}.naturality (Henry.SemiSSet.boundary.{u} k).ι) =
      e.hom ≫ dprismBdryι.{u} k ≫ d.inv := by
    apply (cancel_mono d.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply pushout.hom_ext
    · erw [pushout.inl_desc_assoc]
      rw [← Category.assoc]
      rw [show pushout.inl _ _ ≫ e.hom = sdSimplexToDprismBdry.{u} k from
        sq.inl_isoPushout_inv]
      simp only [sdSimplexToDprismBdry, Category.assoc]
      have hi : sdCosToDprismBdry.{u} k ≫ dprismBdryι.{u} k =
          sdToDprismCos.{u}.app c := by
        ext i x
        rfl
      rw [hi]
      exact (sdLanToDprism_representable.{u} c).symm
    · erw [pushout.inr_desc_assoc]
      rw [← Category.assoc]
      rw [show pushout.inr _ _ ≫ e.hom = dprismBoundaryToDprismBdry.{u} k from
        sq.inr_isoPushout_inv]
      simp only [dprismBoundaryToDprismBdry, Category.assoc]
      have hi : (dprismSideToBdryHom k).toSemiSSet ≫ dprismBdryι.{u} k =
          (dprismSideToDprismHom k).toSemiSSet := by
        ext i x
        rfl
      rw [hi]
      exact (dprismLanBoundaryToSide_comp.{u} k).symm
  have hiso : ∀ {A B : SemiSSet.{u}} (i : A ≅ B), anodyne i.hom := by
    intro A B i
    exact MorphismProperty.le_multiplicativeClosure _ _ (Or.inr inferInstance)
  rw [hfac]
  exact anodyne_comp' (hiso e)
    (anodyne_comp' (HomotopyHypothesis.Approximation.DerivedPrismCollapse.anodyne_dprismBdryι_proof k)
      (hiso d.symm))

#print axioms anodyne_dprismLan_boundary

end HomotopyHypothesis.Approximation.DerivedPrismRelative
