import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.AnodyneCells.Proofs
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderCellProof.Part1
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Rank
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.AnodyneDprismLanRel
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLanTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTopCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.PrismP
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.PrismTop
import HomotopyHypothesis.Approximation.Topological.DerivedSubdivisionCompare.NonemptySdLanIso
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
import HomotopyHypothesis.Approximation.Topological.KanApproximation.Part1
import HomotopyHypothesis.Approximation.Topological.RelPrismApproximation.Part1
/-!
# Isomorphism invariance for derived prism constructions
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.PrismGluing

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological

private def simplexHomOfStrictMono {n k : ℕ} (f : Fin (n + 1) → Fin (k + 1))
    (hf : StrictMono f) : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk k :=
  ⟨SimplexCategory.Hom.mk ⟨f, hf.monotone⟩, SimplexCategory.mono_iff_injective.2 hf.injective⟩

private def dprismTopOnly {k n : ℕ} (x : (dprism k).obj (op (Henry.SemiSimplexCategory.mk n))) :
    Prop := ∀ i, ∃ j : Fin (k + 1), x.down.1 i = PV.top j

private theorem dprismTop_app_down {k n : ℕ}
    (θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk k) :
    ((dprismTop.{u} k).app (op (Henry.SemiSimplexCategory.mk n)) (ULift.up θ)).down.1 =
      fun i => PV.top (θ.1.toOrderHom i) := by
  rfl

private theorem dprismTop_range_iff_topOnly (k n : ℕ)
    (x : (dprism k).obj (op (Henry.SemiSimplexCategory.mk n))) :
    x ∈ Set.range ((dprismTop.{u} k).app (op (Henry.SemiSimplexCategory.mk n))) ↔
      dprismTopOnly x := by
  classical
  constructor
  · rintro ⟨y, rfl⟩
    let θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk k := ULift.down y
    intro i
    refine ⟨θ.1.toOrderHom i, ?_⟩
    have hy : y = ULift.up θ := rfl
    rw [hy]
    exact congrFun (dprismTop_app_down.{u} θ) i
  · intro hx
    choose f hf using hx
    have hstrict : StrictMono f := by
      intro i j hij
      have hlt : PV.top (f i) < PV.top (f j) := by
        rw [← hf i, ← hf j]
        exact x.down.2.1 hij
      change PV.rank (PV.top (f i)) < PV.rank (PV.top (f j)) at hlt
      simpa [PV.rank, Prod.Lex.toLex_lt_toLex] using hlt
    let θ := simplexHomOfStrictMono f hstrict
    refine ⟨ULift.up θ, ?_⟩
    apply ULift.ext
    apply Subtype.ext
    funext i
    rw [dprismTop_app_down.{u} θ]
    change PV.top (θ.1.toOrderHom i) = x.down.1 i
    rw [show θ.1.toOrderHom = f by rfl, (hf i).symm]

private theorem dprismTopCos_range_iff_topOnly (X : Henry.SemiSimplexCategory) (n : ℕ)
    (x : (dprismCos.{u}.obj X).obj (op (Henry.SemiSimplexCategory.mk n))) :
    x ∈ Set.range ((dprismTopCos.{u}.app X).app
      (op (Henry.SemiSimplexCategory.mk n))) ↔ dprismTopOnly x := by
  change x ∈ Set.range ((dprismTop.{u} X.obj.len).app
    (op (Henry.SemiSimplexCategory.mk n))) ↔ dprismTopOnly x
  exact dprismTop_range_iff_topOnly X.obj.len n x

private theorem dprismTop_app_injective (k n : ℕ) :
    Function.Injective ((dprismTop.{u} k).app (op (Henry.SemiSimplexCategory.mk n))) := by
  intro x y hxy
  cases x with
  | up x =>
    cases y with
    | up y =>
      have hfun := congrArg (fun z => z.down.1) hxy
      have hθ : x.1.toOrderHom = y.1.toOrderHom := by
        apply OrderHom.ext
        funext i
        have htop := congrFun hfun i
        rw [congrFun (dprismTop_app_down.{u} x) i,
          congrFun (dprismTop_app_down.{u} y) i] at htop
        exact (PV.top.inj htop)
      have hhom : x = y := by
        apply WideSubcategory.hom_ext
        apply SimplexCategory.Hom.ext
        exact hθ
      exact congrArg ULift.up hhom

private theorem dprismCos_map_reflect_topOnly {X Y : Henry.SemiSimplexCategory}
    (θ : X ⟶ Y) {n : ℕ} (x : (dprismCos.{u}.obj X).obj
      (op (Henry.SemiSimplexCategory.mk n))) :
    dprismTopOnly ((dprismCos.{u}.map θ).app
      (op (Henry.SemiSimplexCategory.mk n)) x) → dprismTopOnly x := by
  intro hx i
  obtain ⟨j, hj⟩ := hx i
  change PV.map θ.1.toOrderHom (x.down.1 i) = PV.top j at hj
  cases hxi : x.down.1 i with
  | top a =>
    exact ⟨a, rfl⟩
  | mid S =>
    simp [PV.map, hxi] at hj

private def dprismNoTopOnly {k n : ℕ}
    (x : (dprism k).obj (op (Henry.SemiSimplexCategory.mk n))) : Prop :=
  ∀ i, ∃ S, x.down.1 i = PV.mid S

private theorem dprismEnd_range_iff_noTop (X : Henry.SemiSimplexCategory) (n : ℕ)
    (x : (dprismCos.{u}.obj X).obj (op (Henry.SemiSimplexCategory.mk n))) :
    x ∈ Set.range ((sdToDprismCos.{u}.app X).app
      (op (Henry.SemiSimplexCategory.mk n))) ↔ dprismNoTopOnly x := by
  classical
  constructor
  · rintro ⟨y, hy⟩
    have hcoord := congrArg (fun z => z.down.1) hy
    change ((sdToDprism X.obj.len).f ∘ y.down.1) = x.down.1 at hcoord
    have hval : y.down.1 = x.down.1 := by
      simpa [sdToDprism] using hcoord
    intro i
    cases hxi : x.down.1 i with
    | top j =>
      have hmem : PV.top j ∈ Finset.univ.image y.down.1 :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (congrFun hval i).trans hxi⟩
      exact (y.down.2.2.2 j hmem).elim
    | mid S => exact ⟨S, rfl⟩
  · intro hx
    let y : (sdComplex X.obj.len).Simplex n :=
      ⟨x.down.1, x.down.2.1, by
        refine ⟨x.down.2.2, ?_⟩
        intro j hj
        obtain ⟨i, -, hji⟩ := Finset.mem_image.mp hj
        obtain ⟨S, hS⟩ := hx i
        cases hji.symm.trans hS⟩
    refine ⟨ULift.up.{u, 0} y, ?_⟩
    apply ULift.ext
    apply Subtype.ext
    rfl

private theorem dprismEnd_app_injective (X : Henry.SemiSimplexCategory) (n : ℕ) :
    Function.Injective ((sdToDprismCos.{u}.app X).app
      (op (Henry.SemiSimplexCategory.mk n))) := by
  intro y z h
  have hcoord := congrArg (fun q => q.down.1) h
  change ((sdToDprism X.obj.len).f ∘ y.down.1) =
    ((sdToDprism X.obj.len).f ∘ z.down.1) at hcoord
  have hval : y.down.1 = z.down.1 := by
    simpa [sdToDprism] using hcoord
  apply ULift.ext
  apply Subtype.ext
  exact hval

private theorem dprismCos_map_reflect_noTop {X Y : Henry.SemiSimplexCategory}
    (θ : X ⟶ Y) {n : ℕ} (x : (dprismCos.{u}.obj X).obj
      (op (Henry.SemiSimplexCategory.mk n))) :
    dprismNoTopOnly ((dprismCos.{u}.map θ).app
      (op (Henry.SemiSimplexCategory.mk n)) x) → dprismNoTopOnly x := by
  intro hx i
  obtain ⟨S, hS⟩ := hx i
  change PV.map θ.1.toOrderHom (x.down.1 i) = PV.mid S at hS
  cases hxi : x.down.1 i with
  | top a => simp [PV.map, hxi] at hS
  | mid A => exact ⟨A, rfl⟩

universe v r

/-- A pointwise injective map of diagrams induces an injective colimit map when its image is
preserved and reflected by every transition map. -/
theorem colimitMap_mono_of_stableRange {I : Type v} [Category.{r} I]
    {F G : I ⥤ Type u} [HasColimitsOfShape I (Type u)] (α : F ⟶ G)
    (hα : ∀ i, Function.Injective (α.app i))
    (hbackward : ∀ {i j} (f : i ⟶ j) {x : G.obj i},
      (∃ y : F.obj j, α.app j y = G.map f x) → ∃ y : F.obj i, α.app i y = x) :
    Mono (colimMap α) := by
  apply (mono_iff_injective _).2
  intro x y hxy
  obtain ⟨i, xi, hxi⟩ :=
    CategoryTheory.Limits.Concrete.isColimit_exists_rep F (colimit.isColimit F) x
  obtain ⟨j, yj, hyj⟩ :=
    CategoryTheory.Limits.Concrete.isColimit_exists_rep F (colimit.isColimit F) y
  have hG : colimit.ι G i (α.app i xi) = colimit.ι G j (α.app j yj) := by
    calc
      colimit.ι G i (α.app i xi) = colimMap α (colimit.ι F i xi) :=
        (ConcreteCategory.congr_hom (colimit.ι_map α i) xi).symm
      _ = colimMap α x := congrArg (colimMap α) hxi
      _ = colimMap α y := hxy
      _ = colimMap α (colimit.ι F j yj) := congrArg (colimMap α) hyj.symm
      _ = colimit.ι G j (α.app j yj) := ConcreteCategory.congr_hom (colimit.ι_map α j) yj
  have hEqv := CategoryTheory.Limits.Types.colimit_eq hG
  let inRange : (Σ i, G.obj i) → Prop := fun z => ∃ x : F.obj z.1, α.app z.1 x = z.2
  have hstable : ∀ {p q : Σ i, G.obj i}, Relation.EqvGen G.ColimitTypeRel p q →
      (inRange p ↔ inRange q) := by
    intro p q hpq
    induction hpq with
    | refl p => exact Iff.rfl
    | @rel p q hpq =>
      obtain ⟨f, hf⟩ := hpq
      constructor
      · intro hp
        obtain ⟨a, ha⟩ := hp
        refine ⟨F.map f a, ?_⟩
        calc
          α.app q.1 (F.map f a) = G.map f (α.app p.1 a) := NatTrans.naturality_apply α f a
          _ = G.map f p.2 := congrArg (G.map f) ha
          _ = q.2 := hf.symm
      · intro hq
        obtain ⟨b, hb⟩ := hq
        have hImage : inRange ⟨q.1, G.map f p.2⟩ := by
          refine ⟨b, ?_⟩
          calc
            α.app q.1 b = q.2 := hb
            _ = G.map f p.2 := hf
        exact hbackward f hImage
    | @symm p q hpq ih => exact ih.symm
    | @trans p q r hpq hqr ih₁ ih₂ => exact ih₁.trans ih₂
  have hLift : ∀ {p q : Σ i, G.obj i}, Relation.EqvGen G.ColimitTypeRel p q →
      ∀ {a : F.obj p.1} {b : F.obj q.1}, α.app p.1 a = p.2 → α.app q.1 b = q.2 →
        Relation.EqvGen F.ColimitTypeRel ⟨p.1, a⟩ ⟨q.1, b⟩ := by
    intro p q hpq
    induction hpq with
    | refl p =>
      intro a b ha hb
      have hab : a = b := hα p.1 (ha.trans hb.symm)
      subst b
      exact Relation.EqvGen.refl _
    | @rel p q hpq =>
      obtain ⟨f, hf⟩ := hpq
      intro a b ha hb
      have hab : F.map f a = b := hα q.1 <| by
        calc
          α.app q.1 (F.map f a) = G.map f (α.app p.1 a) := NatTrans.naturality_apply α f a
          _ = G.map f p.2 := congrArg (G.map f) ha
          _ = q.2 := hf.symm
          _ = α.app q.1 b := hb.symm
      apply Relation.EqvGen.rel
      exact ⟨f, hab.symm⟩
    | @symm p q hpq ih =>
      intro a b ha hb
      exact (ih hb ha).symm
    | @trans p q r hpq hqr ih₁ ih₂ =>
      intro a c ha hc
      obtain ⟨b, hb⟩ := (hstable hpq).mp ⟨a, ha⟩
      let x : Σ i, F.obj i := ⟨p.1, a⟩
      let y : Σ i, F.obj i := ⟨q.1, b⟩
      let z : Σ i, F.obj i := ⟨r.1, c⟩
      have h₁ : Relation.EqvGen F.ColimitTypeRel x y := ih₁ ha hb
      have h₂ : Relation.EqvGen F.ColimitTypeRel y z := ih₂ hb hc
      exact Relation.EqvGen.trans x y z h₁ h₂
  have hSourceEqv : Relation.EqvGen F.ColimitTypeRel ⟨i, xi⟩ ⟨j, yj⟩ :=
    hLift hEqv rfl rfl
  have hSource : colimit.ι F i xi = colimit.ι F j yj := by
    apply (CategoryTheory.Limits.Types.colimitEquivColimitType F).injective
    simp only [CategoryTheory.Limits.Types.colimitEquivColimitType_apply]
    exact Quot.eq.2 hSourceEqv
  calc
    x = colimit.ι F i xi := hxi.symm
    _ = colimit.ι F j yj := hSource
    _ = y := hyj

theorem mono_dprismLanTop_proof (W : SemiSSet.{u}) : Mono (dprismLanTop.app W) := by
  classical
  have hLevel : ∀ n : ℕ,
      Mono ((dprismLanTop.app W).app (op (Henry.SemiSimplexCategory.mk n))) := by
    intro n
    let P := CostructuredArrow.proj Henry.SemiSSet.stdSimplex.{u} W
    let S := P ⋙ Henry.SemiSSet.stdSimplex.{u}
    let T := P ⋙ dprismCos.{u}
    let α : S ⟶ T := Functor.whiskerLeft P dprismTopCos.{u}
    let ev := (CategoryTheory.evaluation (Henry.SemiSimplexCategoryᵒᵖ) (Type u)).obj
      (op (Henry.SemiSimplexCategory.mk n))
    let Sₙ := S ⋙ ev
    let Tₙ := T ⋙ ev
    let αₙ : Sₙ ⟶ Tₙ := Functor.whiskerRight α ev
    let E : Functor.LeftExtension Henry.SemiSSet.stdSimplex.{u} dprismCos.{u} :=
      Functor.LeftExtension.mk dprismLan.{u}
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
    have hEall : E.IsPointwiseLeftKanExtension :=
      Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension dprismLan.{u}
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
    let cS : Cocone S := Presheaf.tautologicalCocone' W
    have hS : IsColimit cS := Presheaf.isColimitTautologicalCocone' W
    let cT : Cocone T := E.coconeAt W
    have hT : IsColimit cT := hEall W
    let cSₙ := ev.mapCocone cS
    have hSₙ : IsColimit cSₙ := isColimitOfPreserves ev hS
    let cTₙ := ev.mapCocone cT
    have hTₙ : IsColimit cTₙ := isColimitOfPreserves ev hT
    let ηₙ : cSₙ.pt ⟶ cTₙ.pt := by
      change W.obj (op (Henry.SemiSimplexCategory.mk n)) ⟶
        (dprismLan.{u}.obj W).obj (op (Henry.SemiSimplexCategory.mk n))
      exact (dprismLanTop.app W).app (op (Henry.SemiSimplexCategory.mk n))
    have hBack : ∀ {c c'} (f : c ⟶ c') {x : Tₙ.obj c},
        (∃ y : Sₙ.obj c', αₙ.app c' y = Tₙ.map f x) →
          ∃ y : Sₙ.obj c, αₙ.app c y = x := by
      intro c c' f x hx
      obtain ⟨y, hy⟩ := hx
      have hy' := hy
      change ((dprismTopCos.{u}.app c'.left).app
          (op (Henry.SemiSimplexCategory.mk n))) y =
        ((dprismCos.{u}.map f.left).app
          (op (Henry.SemiSimplexCategory.mk n))) x at hy'
      have htop : dprismTopOnly
          (((dprismCos.{u}.map f.left).app
            (op (Henry.SemiSimplexCategory.mk n))) x) := by
        apply (dprismTopCos_range_iff_topOnly c'.left n _).1
        exact ⟨y, hy'⟩
      have htop' := dprismCos_map_reflect_topOnly f.left x htop
      change ∃ y, ((dprismTopCos.{u}.app c.left).app
        (op (Henry.SemiSimplexCategory.mk n))) y = x
      exact (dprismTopCos_range_iff_topOnly c.left n x).2 htop'
    have hTypeMap : Mono (colimMap αₙ) :=
      colimitMap_mono_of_stableRange αₙ
        (fun c => by
          change Function.Injective ((dprismTop.{u} c.left.obj.len).app
            (op (Henry.SemiSimplexCategory.mk n)))
          exact dprismTop_app_injective _ _)
        hBack
    let sIso := hSₙ.coconePointUniqueUpToIso (colimit.isColimit Sₙ)
    let tIso := hTₙ.coconePointUniqueUpToIso (colimit.isColimit Tₙ)
    have hMapLeg : ∀ c : CostructuredArrow Henry.SemiSSet.stdSimplex W,
        c.hom ≫ dprismLanTop.app W =
          dprismTopCos.{u}.app c.left ≫
            (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c.left ≫
              dprismLan.{u}.map c.hom := by
      intro c
      haveI : (Functor.id SemiSSet.{u}).IsLeftKanExtension
          (Iso.refl (Henry.SemiSSet.stdSimplex.{u} ⋙ Functor.id SemiSSet.{u})).hom :=
        Presheaf.isLeftKanExtension_of_preservesColimits.{u} (Functor.id SemiSSet.{u})
          (Iso.refl (Henry.SemiSSet.stdSimplex.{u} ⋙ Functor.id SemiSSet.{u}))
      have hfac := Functor.descOfIsLeftKanExtension_fac_app
        (F' := Functor.id SemiSSet.{u})
        (α := (Iso.refl
          (Henry.SemiSSet.stdSimplex.{u} ⋙ Functor.id SemiSSet.{u})).hom) (G := dprismLan.{u})
        (β := dprismTopCos.{u} ≫
          Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}) c.left
      have hRep : dprismLanTop.app (Henry.SemiSSet.stdSimplex.obj c.left) =
          dprismTopCos.{u}.app c.left ≫
            (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c.left := by
        simpa [dprismLanTop] using hfac
      calc
        c.hom ≫ dprismLanTop.app W =
            dprismLanTop.app (Henry.SemiSSet.stdSimplex.obj c.left) ≫ dprismLan.{u}.map c.hom := by
              simpa using (dprismLanTop.naturality c.hom)
        _ = _ := by rw [hRep]; rfl
    have hMapLegₙ (c : CostructuredArrow Henry.SemiSSet.stdSimplex W) :
        cSₙ.ι.app c ≫ ηₙ =
          αₙ.app c ≫ cTₙ.ι.app c := by
      have hEval : ev.map c.hom ≫ ηₙ =
          ev.map (dprismTopCos.{u}.app c.left) ≫
            ev.map ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c.left ≫
              dprismLan.{u}.map c.hom) := by
        calc
          ev.map c.hom ≫ ηₙ = ev.map c.hom ≫ ev.map (dprismLanTop.app W) := by rfl
          _ = ev.map (c.hom ≫ dprismLanTop.app W) := by rw [← Functor.map_comp]
          _ = ev.map (dprismTopCos.{u}.app c.left ≫
              (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c.left ≫
                dprismLan.{u}.map c.hom) := congrArg (fun f => ev.map f) (hMapLeg c)
          _ = _ := by simp [Functor.map_comp, Category.assoc]
      change ev.map c.hom ≫ ηₙ =
        ev.map (dprismTopCos.{u}.app c.left) ≫
          ev.map ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c.left ≫
            dprismLan.{u}.map c.hom)
      exact hEval
    have hMap : sIso.inv ≫ ηₙ ≫ tIso.hom = colimMap αₙ := by
      apply colimit.hom_ext
      intro c
      have hs := hSₙ.comp_coconePointUniqueUpToIso_hom (colimit.isColimit Sₙ) c
      have ht := hTₙ.comp_coconePointUniqueUpToIso_hom (colimit.isColimit Tₙ) c
      calc
        (colimit.cocone Sₙ).ι.app c ≫ (sIso.inv ≫ ηₙ ≫ tIso.hom) =
            αₙ.app c ≫ (colimit.cocone Tₙ).ι.app c := by
          calc
            (colimit.cocone Sₙ).ι.app c ≫ (sIso.inv ≫ ηₙ ≫ tIso.hom) =
                (cSₙ.ι.app c ≫ sIso.hom) ≫ sIso.inv ≫ ηₙ ≫ tIso.hom := by
                  rw [← hs]
            _ = cSₙ.ι.app c ≫ ηₙ ≫ tIso.hom := by simp [Category.assoc]
            _ = αₙ.app c ≫ cTₙ.ι.app c ≫ tIso.hom := by
              simpa only [Category.assoc] using
                congrArg (fun f => f ≫ tIso.hom) (hMapLegₙ c)
            _ = αₙ.app c ≫ (colimit.cocone Tₙ).ι.app c := by rw [ht]
        _ = (colimit.cocone Sₙ).ι.app c ≫ colimMap αₙ :=
          (colimit.ι_map αₙ c).symm
    letI : Mono (colimMap αₙ) := hTypeMap
    have hη : ηₙ =
        sIso.hom ≫ colimMap αₙ ≫ tIso.inv := by
      calc
        _ = sIso.hom ≫ (sIso.inv ≫ ηₙ ≫ tIso.hom) ≫ tIso.inv := by
              simp [Category.assoc]
        _ = sIso.hom ≫ colimMap αₙ ≫ tIso.inv := by rw [hMap]
    have hηmono : Mono ηₙ := by
      rw [hη]
      infer_instance
    change Mono ηₙ
    exact hηmono
  rw [NatTrans.mono_iff_mono_app]
  intro a
  cases a with
  | op b =>
    cases b with
    | mk c =>
      cases c with
      | mk n => exact hLevel n

theorem mono_sdLanToDprism_proof (W : SemiSSet.{u}) : Mono (sdLanToDprism.app W) := by
  classical
  have hLevel : ∀ n : ℕ,
      Mono ((sdLanToDprism.app W).app (op (Henry.SemiSimplexCategory.mk n))) := by
    intro n
    let P := CostructuredArrow.proj Henry.SemiSSet.stdSimplex.{u} W
    let S := P ⋙ sdCos.{u}
    let T := P ⋙ dprismCos.{u}
    let α : S ⟶ T := Functor.whiskerLeft P sdToDprismCos.{u}
    let ev := (CategoryTheory.evaluation (Henry.SemiSimplexCategoryᵒᵖ) (Type u)).obj
      (op (Henry.SemiSimplexCategory.mk n))
    let Sₙ := S ⋙ ev
    let Tₙ := T ⋙ ev
    let αₙ : Sₙ ⟶ Tₙ := Functor.whiskerRight α ev
    let ES : Functor.LeftExtension Henry.SemiSSet.stdSimplex.{u} sdCos.{u} :=
      Functor.LeftExtension.mk sdLan.{u}
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u})
    have hESall : ES.IsPointwiseLeftKanExtension :=
      Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension sdLan.{u}
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u})
    let ET : Functor.LeftExtension Henry.SemiSSet.stdSimplex.{u} dprismCos.{u} :=
      Functor.LeftExtension.mk dprismLan.{u}
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
    have hETall : ET.IsPointwiseLeftKanExtension :=
      Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension dprismLan.{u}
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
    let cS : Cocone S := ES.coconeAt W
    have hS : IsColimit cS := hESall W
    let cT : Cocone T := ET.coconeAt W
    have hT : IsColimit cT := hETall W
    let cSₙ := ev.mapCocone cS
    have hSₙ : IsColimit cSₙ := isColimitOfPreserves ev hS
    let cTₙ := ev.mapCocone cT
    have hTₙ : IsColimit cTₙ := isColimitOfPreserves ev hT
    let ηₙ : cSₙ.pt ⟶ cTₙ.pt := by
      change (sdLan.{u}.obj W).obj (op (Henry.SemiSimplexCategory.mk n)) ⟶
        (dprismLan.{u}.obj W).obj (op (Henry.SemiSimplexCategory.mk n))
      exact (sdLanToDprism.app W).app (op (Henry.SemiSimplexCategory.mk n))
    have hBack : ∀ {c c'} (f : c ⟶ c') {x : Tₙ.obj c},
        (∃ y : Sₙ.obj c', αₙ.app c' y = Tₙ.map f x) →
          ∃ y : Sₙ.obj c, αₙ.app c y = x := by
      intro c c' f x hx
      obtain ⟨y, hy⟩ := hx
      have hy' := hy
      change ((sdToDprismCos.{u}.app c'.left).app
          (op (Henry.SemiSimplexCategory.mk n))) y =
        ((dprismCos.{u}.map f.left).app
          (op (Henry.SemiSimplexCategory.mk n))) x at hy'
      have hNoTop : dprismNoTopOnly
          (((dprismCos.{u}.map f.left).app
            (op (Henry.SemiSimplexCategory.mk n))) x) := by
        apply (dprismEnd_range_iff_noTop c'.left n _).1
        exact ⟨y, hy'⟩
      have hNoTop' := dprismCos_map_reflect_noTop f.left x hNoTop
      change ∃ y, (((sdToDprismCos.{u}.app c.left).app
        (op (Henry.SemiSimplexCategory.mk n))) y) = x
      exact (dprismEnd_range_iff_noTop c.left n x).2 hNoTop'
    have hTypeMap : Mono (colimMap αₙ) :=
      colimitMap_mono_of_stableRange αₙ
        (fun c => by
          change Function.Injective ((sdToDprismCos.{u}.app c.left).app
            (op (Henry.SemiSimplexCategory.mk n)))
          exact dprismEnd_app_injective _ _)
        hBack
    let sIso := hSₙ.coconePointUniqueUpToIso (colimit.isColimit Sₙ)
    let tIso := hTₙ.coconePointUniqueUpToIso (colimit.isColimit Tₙ)
    have hfac (c : Henry.SemiSimplexCategory) := Functor.descOfIsLeftKanExtension_fac_app
      (F' := sdLan.{u})
      (α := Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u})
      (G := dprismLan.{u})
      (β := sdToDprismCos.{u} ≫
        Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}) c
    have hRep (c : CostructuredArrow Henry.SemiSSet.stdSimplex W) :
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}).app c.left ≫
          sdLanToDprism.app (Henry.SemiSSet.stdSimplex.obj c.left) =
        sdToDprismCos.{u}.app c.left ≫
          (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c.left := by
      simpa [sdLanToDprism] using hfac c.left
    have hMapLeg (c : CostructuredArrow Henry.SemiSSet.stdSimplex W) :
        cS.ι.app c ≫ sdLanToDprism.app W =
          sdToDprismCos.{u}.app c.left ≫
            (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c.left ≫
              dprismLan.{u}.map c.hom := by
      change ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}).app c.left ≫
          sdLan.{u}.map c.hom) ≫ sdLanToDprism.app W = _
      calc
        _ = (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}).app c.left ≫
              (sdLan.{u}.map c.hom ≫ sdLanToDprism.app W) := by simp [Category.assoc]
        _ = (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}).app c.left ≫
              (sdLanToDprism.app (Henry.SemiSSet.stdSimplex.obj c.left) ≫
                dprismLan.{u}.map c.hom) := by rw [sdLanToDprism.naturality c.hom]
        _ = ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit sdCos.{u}).app c.left ≫
              sdLanToDprism.app (Henry.SemiSSet.stdSimplex.obj c.left)) ≫
                dprismLan.{u}.map c.hom := by simp [Category.assoc]
        _ = _ := by rw [hRep c]; simp [Category.assoc]
    have hMapLegₙ (c : CostructuredArrow Henry.SemiSSet.stdSimplex W) :
        cSₙ.ι.app c ≫ ηₙ = αₙ.app c ≫ cTₙ.ι.app c := by
      have hEval : ev.map (cS.ι.app c) ≫ ηₙ =
          ev.map (sdToDprismCos.{u}.app c.left) ≫
            ev.map ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c.left ≫
              dprismLan.{u}.map c.hom) := by
        calc
          ev.map (cS.ι.app c) ≫ ηₙ =
              ev.map (cS.ι.app c) ≫ ev.map (sdLanToDprism.app W) := by rfl
          _ = ev.map (cS.ι.app c ≫ sdLanToDprism.app W) := by rw [← Functor.map_comp]
          _ = ev.map (sdToDprismCos.{u}.app c.left ≫
              (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c.left ≫
                dprismLan.{u}.map c.hom) := congrArg (fun f => ev.map f) (hMapLeg c)
          _ = _ := by simp [Functor.map_comp, Category.assoc]
      change ev.map (cS.ι.app c) ≫ ηₙ =
        ev.map (sdToDprismCos.{u}.app c.left) ≫
          ev.map ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c.left ≫
            dprismLan.{u}.map c.hom)
      exact hEval
    have hMap : sIso.inv ≫ ηₙ ≫ tIso.hom = colimMap αₙ := by
      apply colimit.hom_ext
      intro c
      have hs := hSₙ.comp_coconePointUniqueUpToIso_hom (colimit.isColimit Sₙ) c
      have ht := hTₙ.comp_coconePointUniqueUpToIso_hom (colimit.isColimit Tₙ) c
      calc
        (colimit.cocone Sₙ).ι.app c ≫ (sIso.inv ≫ ηₙ ≫ tIso.hom) =
            αₙ.app c ≫ (colimit.cocone Tₙ).ι.app c := by
          calc
            (colimit.cocone Sₙ).ι.app c ≫ (sIso.inv ≫ ηₙ ≫ tIso.hom) =
                (cSₙ.ι.app c ≫ sIso.hom) ≫ sIso.inv ≫ ηₙ ≫ tIso.hom := by rw [← hs]
            _ = cSₙ.ι.app c ≫ ηₙ ≫ tIso.hom := by simp [Category.assoc]
            _ = αₙ.app c ≫ cTₙ.ι.app c ≫ tIso.hom := by
              simpa only [Category.assoc] using congrArg (fun f => f ≫ tIso.hom) (hMapLegₙ c)
            _ = αₙ.app c ≫ (colimit.cocone Tₙ).ι.app c := by rw [ht]
        _ = (colimit.cocone Sₙ).ι.app c ≫ colimMap αₙ := (colimit.ι_map αₙ c).symm
    letI : Mono (colimMap αₙ) := hTypeMap
    have hη : ηₙ = sIso.hom ≫ colimMap αₙ ≫ tIso.inv := by
      calc
        _ = sIso.hom ≫ (sIso.inv ≫ ηₙ ≫ tIso.hom) ≫ tIso.inv := by simp [Category.assoc]
        _ = sIso.hom ≫ colimMap αₙ ≫ tIso.inv := by rw [hMap]
    have hηmono : Mono ηₙ := by
      rw [hη]
      infer_instance
    change Mono ηₙ
    exact hηmono
  rw [NatTrans.mono_iff_mono_app]
  intro a
  cases a with
  | op b =>
    cases b with
    | mk c =>
      cases c with
      | mk n => exact hLevel n

private theorem finite_costructuredArrow_of_isFinite {W : SemiSSet.{u}}
    (hW : W.IsFinite) : Finite (CostructuredArrow Henry.SemiSSet.stdSimplex.{u} W) := by
  classical
  letI : Finite (Simplicial.BarycentricSubdivision.FaceCategory W) := Simplicial.BarycentricSubdivision.finite_faceCategory_of_isFinite hW
  let e := CategoryTheory.Functor.Elements.costructuredArrowULiftYonedaEquivalence.{u} W
  apply Finite.of_surjective e.functor.obj
  intro c
  refine ⟨e.inverse.obj c, ?_⟩
  change CostructuredArrow.mk (uliftYonedaEquiv.symm (uliftYonedaEquiv c.hom)) = c
  exact CostructuredArrow.obj_ext
    (CostructuredArrow.mk (uliftYonedaEquiv.symm (uliftYonedaEquiv c.hom))) c rfl (by simp)

private noncomputable instance pvFintype (k : ℕ) : Fintype (PV k) := by
  letI : Fintype (Finset (Fin (k + 1))) := inferInstance
  exact Fintype.ofEquiv (Fin (k + 1) ⊕ Finset (Fin (k + 1)))
    { toFun := Sum.elim PV.top PV.mid
      invFun := fun
        | PV.top i => Sum.inl i
        | PV.mid S => Sum.inr S
      left_inv := by intro x; cases x <;> rfl
      right_inv := by intro x; cases x <;> rfl }

private theorem dprism_empty_of_card_lt (k n : ℕ)
    (hcard : Fintype.card (PV k) < n) :
    IsEmpty ((dprism k).obj (op (Henry.SemiSimplexCategory.mk n))) := by
  letI : Fintype (PV k) := inferInstance
  refine ⟨fun x => ?_⟩
  have hle := Fintype.card_le_of_injective x.down.1 x.down.2.1.injective
  simp only [Fintype.card_fin] at hle
  omega

private theorem dprism_level_finite (k n : ℕ) :
    Finite ((dprism k).obj (op (Henry.SemiSimplexCategory.mk n))) := by
  letI : Fintype (PV k) := inferInstance
  refine Finite.of_injective (fun x => x.down.1) ?_
  intro x y h
  apply ULift.ext
  apply Subtype.ext
  exact h

theorem isFinite_dprismLan_proof {W : SemiSSet.{u}} (hW : W.IsFinite) :
    (dprismLan.obj W).IsFinite := by
  classical
  obtain ⟨N, hN⟩ := hW.2
  let M := Finset.univ.sup (fun k : Fin (N + 1) => Fintype.card (PV k.val))
  have hcardBound (k : ℕ) (hk : k ≤ N) : Fintype.card (PV k) ≤ M := by
    let j : Fin (N + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    exact Finset.le_sup (f := fun k : Fin (N + 1) => Fintype.card (PV k.val))
      (Finset.mem_univ j)
  constructor
  · intro n
    let P := CostructuredArrow.proj Henry.SemiSSet.stdSimplex.{u} W
    let T := P ⋙ dprismCos.{u}
    let ev := (CategoryTheory.evaluation (Henry.SemiSimplexCategoryᵒᵖ) (Type u)).obj
      (op (Henry.SemiSimplexCategory.mk n))
    let Tₙ := T ⋙ ev
    let E : Functor.LeftExtension Henry.SemiSSet.stdSimplex.{u} dprismCos.{u} :=
      Functor.LeftExtension.mk dprismLan.{u}
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
    have hE : E.IsPointwiseLeftKanExtension :=
      Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension dprismLan.{u}
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
    let cT := ev.mapCocone (E.coconeAt W)
    have hT : IsColimit cT := isColimitOfPreserves ev (hE W)
    change Finite cT.pt
    let tIso := hT.coconePointUniqueUpToIso (colimit.isColimit Tₙ)
    have hColimFinite : Finite (colimit.cocone Tₙ).pt := by
      letI : Finite (CostructuredArrow Henry.SemiSSet.stdSimplex.{u} W) :=
        finite_costructuredArrow_of_isFinite hW
      letI : ∀ c : CostructuredArrow Henry.SemiSSet.stdSimplex.{u} W, Finite (Tₙ.obj c) := by
        intro c
        change Finite ((dprism c.left.obj.len).obj (op (Henry.SemiSimplexCategory.mk n)))
        exact dprism_level_finite c.left.obj.len n
      letI : Finite (Σ c : CostructuredArrow Henry.SemiSSet.stdSimplex.{u} W, Tₙ.obj c) :=
        inferInstance
      apply Finite.of_surjective (fun z : Σ c, Tₙ.obj c => colimit.ι Tₙ z.1 z.2)
      intro x
      obtain ⟨c, y, hy⟩ :=
        CategoryTheory.Limits.Concrete.isColimit_exists_rep Tₙ (colimit.isColimit Tₙ) x
      exact ⟨⟨c, y⟩, hy⟩
    letI : Finite (colimit.cocone Tₙ).pt := hColimFinite
    apply Finite.of_injective tIso.hom
    intro x y hxy
    exact (mono_iff_injective _).mp (inferInstance : Mono tIso.hom) hxy
  · refine ⟨M, fun n hn => ?_⟩
    let P := CostructuredArrow.proj Henry.SemiSSet.stdSimplex.{u} W
    let T := P ⋙ dprismCos.{u}
    let ev := (CategoryTheory.evaluation (Henry.SemiSimplexCategoryᵒᵖ) (Type u)).obj
      (op (Henry.SemiSimplexCategory.mk n))
    let Tₙ := T ⋙ ev
    let E : Functor.LeftExtension Henry.SemiSSet.stdSimplex.{u} dprismCos.{u} :=
      Functor.LeftExtension.mk dprismLan.{u}
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
    have hE : E.IsPointwiseLeftKanExtension :=
      Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension dprismLan.{u}
        (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
    let cT := ev.mapCocone (E.coconeAt W)
    have hT : IsColimit cT := isColimitOfPreserves ev (hE W)
    change IsEmpty cT.pt
    refine ⟨fun x => ?_⟩
    obtain ⟨c, y, hy⟩ :=
      CategoryTheory.Limits.Concrete.isColimit_exists_rep Tₙ hT x
    let k := c.left.obj.len
    have hlen : Henry.SemiSimplexCategory.mk k = c.left := by
      apply WideSubcategory.ext
      exact SimplexCategory.mk_len c.left.obj
    let hlenOp := congrArg Opposite.op hlen
    let wy : W.obj (op (Henry.SemiSimplexCategory.mk k)) :=
      W.map (eqToHom hlenOp.symm) (uliftYonedaEquiv c.hom)
    have hk : k ≤ N := by
      by_contra hkn
      exact (hN k (Nat.lt_of_not_ge hkn)).false wy
    have hcard : Fintype.card (PV k) ≤ M := hcardBound k hk
    change (dprism k).obj (op (Henry.SemiSimplexCategory.mk n)) at y
    exact (dprism_empty_of_card_lt k n (by omega)).false y


/-- Finiteness is invariant under isomorphism of semi-simplicial sets. -/
theorem isFinite_of_iso_proof {A B : SemiSSet.{u}} (e : A ≅ B) (hB : B.IsFinite) :
    A.IsFinite := by
  constructor
  · intro n
    let k := op (Henry.SemiSimplexCategory.mk n)
    haveI : Finite (B.obj k) := hB.1 n
    apply Finite.of_injective (e.hom.app k)
    intro x y hxy
    haveI : Mono e.hom := inferInstance
    have hm : Mono (e.hom.app k) :=
      (NatTrans.mono_iff_mono_app (f := e.hom)).mp (inferInstance : Mono e.hom) k
    exact (mono_iff_injective _).mp hm hxy
  · obtain ⟨N, hN⟩ := hB.2
    refine ⟨N, fun n hn => ?_⟩
    let k := op (Henry.SemiSimplexCategory.mk n)
    letI : IsEmpty (B.obj k) := hN n hn
    exact ⟨fun x => isEmptyElim (e.hom.app k x)⟩

/-- Ordered simplicial complex structure is invariant under isomorphism. -/
theorem isSimplicialComplex_of_iso_proof {A B : SemiSSet.{u}} (e : A ≅ B)
    (hB : B.IsSimplicialComplex) : A.IsSimplicialComplex := by
  haveI : IsIso (realization.map e.hom) := Functor.map_isIso realization e.hom
  have hMapHomeo : IsHomeomorph (realization.map e.hom).hom :=
    (TopCat.isIso_iff_isHomeomorph (realization.map e.hom)).mp inferInstance
  have hMapInjective : Function.Injective (realization.map e.hom).hom :=
    hMapHomeo.bijective.injective
  constructor
  · intro n σ
    have hσ := hB.1 n (σ ≫ e.hom)
    intro i j hij
    apply hσ
    simpa only [simplexChar_comp, TopCat.hom_comp, ContinuousMap.comp_apply] using
      congrArg (fun x => (realization.map e.hom).hom x) hij
  · intro n σ τ hRange
    let vσ : Fin (n + 1) → realization.obj A := fun i =>
      (simplexChar σ).hom (simplexVertex i)
    let vτ : Fin (n + 1) → realization.obj A := fun i =>
      (simplexChar τ).hom (simplexVertex i)
    let g : realization.obj A → realization.obj B := (realization.map e.hom).hom
    have hCompRange : Set.range (fun i => g (vσ i)) = Set.range (fun i => g (vτ i)) := by
      simpa only [vσ, vτ, Set.range_comp'] using
        congrArg (fun S : Set (realization.obj A) => g '' S) hRange
    have hRange' : Set.range vσ = Set.range vτ := by
      apply Set.ext
      intro x
      constructor
      · rintro ⟨i, rfl⟩
        have hx : g (vσ i) ∈ Set.range (fun j => g (vτ j)) := by
          rw [← hCompRange]
          exact ⟨i, rfl⟩
        rcases hx with ⟨j, hj⟩
        refine ⟨j, ?_⟩
        apply hMapInjective
        simpa only [Function.comp_apply] using hj
      · rintro ⟨j, rfl⟩
        have hx : g (vτ j) ∈ Set.range (fun i => g (vσ i)) := by
          rw [hCompRange]
          exact ⟨j, rfl⟩
        rcases hx with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        apply hMapInjective
        simpa only [Function.comp_apply] using hi
    have hRangeB : Set.range (fun i =>
        (simplexChar (σ ≫ e.hom)).hom (simplexVertex i)) =
        Set.range (fun i => (simplexChar (τ ≫ e.hom)).hom (simplexVertex i)) := by
      simpa only [vσ, vτ, g, Function.comp_def, simplexChar_comp, TopCat.hom_comp,
        ContinuousMap.comp_apply] using hCompRange
    have hEq : σ ≫ e.hom = τ ≫ e.hom := hB.2 n (σ ≫ e.hom) (τ ≫ e.hom) hRangeB
    exact (cancel_mono e.hom).1 hEq

private theorem anodyne_iso_hom {A B : SemiSSet.{u}} (e : A ≅ B) : anodyne e.hom := by
  unfold anodyne
  exact .of _ (Or.inr (MorphismProperty.isomorphisms.infer_property e.hom))

theorem anodyne_prismTop_proof (W : SemiSSet.{u}) (J : Subfunctor W) (hW : W.IsFinite) :
    anodyne (pushout.desc (prismTop.app W) (prismP.map J.ι) (prismTop.naturality J.ι) :
      pushout ((sdLan ⋙ sdLan).map J.ι) (prismTop.app J.toFunctor) ⟶ prismP.obj W) := by
  classical
  let F2 := sdLan ⋙ sdLan
  let W' := sdLan.obj W
  let J' := sdLan.obj J.toFunctor
  let W'' := F2.obj W
  let J'' := F2.obj J.toFunctor
  let j' : J' ⟶ W' := sdLan.map J.ι
  let j'' : J'' ⟶ W'' := F2.map J.ι
  let αW : W' ⟶ dprismLan.obj W := sdLanToDprism.app W
  let αJ : J' ⟶ dprismLan.obj J.toFunctor := sdLanToDprism.app J.toFunctor
  let αJ' : J'' ⟶ dprismLan.obj J' := sdLanToDprism.app J'
  let αW' : W'' ⟶ dprismLan.obj W' := sdLanToDprism.app W'
  let τW' : W' ⟶ dprismLan.obj W' := dprismLanTop.app W'
  let τJ' : J' ⟶ dprismLan.obj J' := dprismLanTop.app J'
  let e : sdLan ≅ Simplicial.BarycentricSubdivision.firstSubdivision := Classical.choice nonempty_sdLanIso
  have hW' : W'.IsFinite :=
    isFinite_of_iso_proof (e.app W) (Simplicial.BarycentricSubdivision.firstSubdivision_isFinite hW)
  have hMonoJ' : Mono j' := by
    haveI : Mono (e.hom.app J.toFunctor) := inferInstance
    haveI : Mono (Simplicial.BarycentricSubdivision.firstSubdivision.map J.ι) :=
      Simplicial.BarycentricSubdivision.firstSubdivision_map_mono J.ι
    haveI : Mono (inv (e.hom.app W)) := inferInstance
    have hfactor : j' = e.hom.app J.toFunctor ≫
        Simplicial.BarycentricSubdivision.firstSubdivision.map J.ι ≫ inv (e.hom.app W) := by
      dsimp [j']
      calc
        _ = (sdLan.map J.ι ≫ e.hom.app W) ≫ inv (e.hom.app W) := by simp [Category.assoc]
        _ = (e.hom.app J.toFunctor ≫ Simplicial.BarycentricSubdivision.firstSubdivision.map J.ι) ≫
              inv (e.hom.app W) := by rw [e.hom.naturality J.ι]
        _ = _ := by simp [Category.assoc]
    rw [hfactor]
    infer_instance
  let K : Subfunctor W' := Subfunctor.range j'
  let eRange : J' ≅ K.toFunctor := Cylinder.AnodyneCells.rangeIso j'
  have heRange : eRange.hom ≫ K.ι = j' := by
    simpa [eRange, K, Cylinder.AnodyneCells.rangeIso] using Subfunctor.toRange_ι j'
  let eRange' : J'' ≅ sdLan.obj K.toFunctor := sdLan.mapIso eRange
  let AK : SemiSSet := pushout (sdLan.map K.ι) (sdLanToDprism.app K.toFunctor)
  let AJ : SemiSSet := pushout j'' αJ'
  let Q : SemiSSet := pushout j'' (prismTop.app J.toFunctor)
  let qK : AK ⟶ dprismLan.obj W' :=
    pushout.desc αW' (dprismLan.map K.ι) (sdLanToDprism.naturality K.ι)
  have hqK : anodyne qK := by
    exact anodyne_dprismLan_rel W' K hW'
  have heqLeft : j'' ≫ 𝟙 W'' = eRange'.hom ≫ sdLan.map K.ι := by
    dsimp [j'', F2, eRange']
    simp only [Category.comp_id]
    rw [← Functor.map_comp, heRange]
  have heqRight : αJ' ≫ dprismLan.map eRange.hom =
      eRange'.hom ≫ sdLanToDprism.app K.toFunctor := by
    exact (sdLanToDprism.naturality eRange.hom).symm
  let eA0 := pushout.map j'' αJ' (sdLan.map K.ι) (sdLanToDprism.app K.toFunctor)
    (𝟙 W'') (dprismLan.map eRange.hom) eRange'.hom heqLeft heqRight
  haveI : IsIso eA0 := by
    dsimp [eA0]
    infer_instance
  let eA : AJ ≅ AK := asIso eA0
  have heAleft : pushout.inl j'' αJ' ≫ eA.hom =
      pushout.inl (sdLan.map K.ι) (sdLanToDprism.app K.toFunctor) := by
    dsimp [eA, eA0, pushout.map]
    rw [pushout.inl_desc]
    simp
  have heAright : pushout.inr j'' αJ' ≫ eA.hom =
      dprismLan.map eRange.hom ≫
        pushout.inr (sdLan.map K.ι) (sdLanToDprism.app K.toFunctor) := by
    dsimp [eA, eA0, pushout.map]
    rw [pushout.inr_desc]
  have hqKright :
      pushout.inr (sdLan.map K.ι) (sdLanToDprism.app K.toFunctor) ≫ qK =
        dprismLan.map K.ι := by
    dsimp [qK]
    exact pushout.inr_desc _ _ _
  let qJ : AJ ⟶ dprismLan.obj W' :=
    pushout.desc αW' (dprismLan.map j') (sdLanToDprism.naturality j')
  have hqJfactor : qJ = eA.hom ≫ qK := by
    apply pushout.hom_ext
    · calc
        pushout.inl j'' αJ' ≫ qJ = αW' := pushout.inl_desc _ _ _
        _ = pushout.inl (sdLan.map K.ι) (sdLanToDprism.app K.toFunctor) ≫ qK :=
          (pushout.inl_desc _ _ _).symm
        _ = pushout.inl j'' αJ' ≫ eA.hom ≫ qK := by
          exact congrArg (fun f => f ≫ qK) heAleft.symm
    · calc
        pushout.inr j'' αJ' ≫ qJ = dprismLan.map j' := pushout.inr_desc _ _ _
        _ = dprismLan.map eRange.hom ≫ dprismLan.map K.ι := by
          rw [← Functor.map_comp, heRange]
        _ = pushout.inr j'' αJ' ≫ eA.hom ≫ qK := by
          calc
            dprismLan.map eRange.hom ≫ dprismLan.map K.ι =
                dprismLan.map eRange.hom ≫
                  (pushout.inr (sdLan.map K.ι) (sdLanToDprism.app K.toFunctor) ≫ qK) := by
                    rw [hqKright]
            _ = (dprismLan.map eRange.hom ≫
                  pushout.inr (sdLan.map K.ι) (sdLanToDprism.app K.toFunctor)) ≫ qK := by
                    rw [← Category.assoc]
            _ = (pushout.inr j'' αJ' ≫ eA.hom) ≫ qK := by
                    rw [heAright.symm]
            _ = pushout.inr j'' αJ' ≫ eA.hom ≫ qK := by
                    rw [Category.assoc]
  have hqJ : anodyne qJ := by
    rw [hqJfactor]
    exact anodyne_comp' (anodyne_iso_hom eA) hqK

  let pJ : SemiSSet := prismP.obj J.toFunctor
  let pJinJ' : dprismLan.obj J' ⟶ pJ :=
    pushout.inr αJ τJ'
  let pJinJ : dprismLan.obj J.toFunctor ⟶ pJ := pushout.inl αJ τJ'
  let dJ'W' : dprismLan.obj J' ⟶ dprismLan.obj W' := dprismLan.map j'
  let R : SemiSSet := pushout dJ'W' pJinJ'
  let rE : dprismLan.obj W' ⟶ R := pushout.inl dJ'W' pJinJ'
  let rPJ : pJ ⟶ R := pushout.inr dJ'W' pJinJ'
  let q0 : Q ⟶ prismP.obj W :=
    pushout.desc (prismTop.app W) (prismP.map J.ι) (prismTop.naturality J.ι)

  have hTopJ : prismTop.app J.toFunctor = αJ' ≫ pJinJ' := by
    change αJ' ≫ pushout.inr αJ τJ' = αJ' ≫ pushout.inr αJ τJ'
    rfl
  let iA : AJ ⟶ Q := pushout.desc (pushout.inl j'' (prismTop.app J.toFunctor))
    (pJinJ' ≫ pushout.inr j'' (prismTop.app J.toFunctor)) (by
      calc
        j'' ≫ pushout.inl j'' (prismTop.app J.toFunctor) =
            prismTop.app J.toFunctor ≫ pushout.inr j'' (prismTop.app J.toFunctor) :=
          pushout.condition
        _ = αJ' ≫ (pJinJ' ≫ pushout.inr j'' (prismTop.app J.toFunctor)) := by
          rw [← Category.assoc, ← hTopJ])
  have hiAleft : pushout.inl j'' αJ' ≫ iA = pushout.inl j'' (prismTop.app J.toFunctor) := by
    dsimp [iA]
    exact pushout.inl_desc _ _ _
  have hiAright : pushout.inr j'' αJ' ≫ iA =
      pJinJ' ≫ pushout.inr j'' (prismTop.app J.toFunctor) := by
    dsimp [iA]
    exact pushout.inr_desc _ _ _
  have hLeft : IsPushout (pushout.inr j'' αJ') pJinJ' iA
      (pushout.inr j'' (prismTop.app J.toFunctor)) := by
    let hcond : pushout.inr j'' αJ' ≫ iA =
        pJinJ' ≫ pushout.inr j'' (prismTop.app J.toFunctor) := hiAright
    let desc : ∀ s : PushoutCocone (pushout.inr j'' αJ') pJinJ', Q ⟶ s.pt := fun s =>
      pushout.desc (pushout.inl j'' αJ' ≫ s.inl) s.inr (by
        calc
          j'' ≫ pushout.inl j'' αJ' ≫ s.inl =
              αJ' ≫ pushout.inr j'' αJ' ≫ s.inl := by
                rw [pushout.condition_assoc]
          _ = αJ' ≫ pJinJ' ≫ s.inr := by
            simpa [Category.assoc] using congrArg (fun f => αJ' ≫ f) s.condition
          _ = prismTop.app J.toFunctor ≫ s.inr := by
            rw [← Category.assoc, ← hTopJ])
    have facA : ∀ s : PushoutCocone (pushout.inr j'' αJ') pJinJ',
        iA ≫ desc s = s.inl := by
      intro s
      apply pushout.hom_ext
      · calc
          pushout.inl j'' αJ' ≫ iA ≫ desc s =
              pushout.inl j'' (prismTop.app J.toFunctor) ≫ desc s := by
                simpa [Category.assoc] using
                  congrArg (fun f => f ≫ desc s) hiAleft
          _ = pushout.inl j'' αJ' ≫ s.inl := by
            dsimp [desc]
            exact pushout.inl_desc _ _ _
      · calc
          pushout.inr j'' αJ' ≫ iA ≫ desc s = pJinJ' ≫ s.inr := by
            calc
              pushout.inr j'' αJ' ≫ iA ≫ desc s =
                  (pJinJ' ≫ pushout.inr j'' (prismTop.app J.toFunctor)) ≫ desc s := by
                    simpa [Category.assoc] using
                      congrArg (fun f => f ≫ desc s) hiAright
              _ = pJinJ' ≫ s.inr := by
                dsimp [desc]
                rw [Category.assoc, pushout.inr_desc]
          _ = pushout.inr j'' αJ' ≫ s.inl := s.condition.symm
    have facP : ∀ s : PushoutCocone (pushout.inr j'' αJ') pJinJ',
        pushout.inr j'' (prismTop.app J.toFunctor) ≫ desc s = s.inr := by
      intro s
      dsimp [desc]
      exact pushout.inr_desc _ _ _
    have uniq : ∀ (s : PushoutCocone (pushout.inr j'' αJ') pJinJ') (m : Q ⟶ s.pt),
        iA ≫ m = s.inl → pushout.inr j'' (prismTop.app J.toFunctor) ≫ m = s.inr →
          m = desc s := by
      intro s m hmA hmP
      apply pushout.hom_ext
      · calc
          pushout.inl j'' (prismTop.app J.toFunctor) ≫ m =
              (pushout.inl j'' αJ' ≫ iA) ≫ m := by
                rw [pushout.inl_desc]
          _ = pushout.inl j'' αJ' ≫ (iA ≫ m) := Category.assoc _ _ _
          _ = pushout.inl j'' αJ' ≫ s.inl := by rw [hmA]
          _ = pushout.inl j'' (prismTop.app J.toFunctor) ≫ desc s :=
            (pushout.inl_desc _ _ _).symm
      · exact hmP.trans (facP s).symm
    refine IsPushout.of_isColimit (c := PushoutCocone.mk iA
      (pushout.inr j'' (prismTop.app J.toFunctor)) hcond)
      (PushoutCocone.IsColimit.mk hcond desc facA facP uniq)

  have hOuter : IsPushout dJ'W' pJinJ' rE rPJ := IsPushout.of_hasPushout dJ'W' pJinJ'
  let q1 : Q ⟶ R := pushout.desc (αW' ≫ rE) rPJ (by
    calc
      j'' ≫ αW' ≫ rE = αJ' ≫ dJ'W' ≫ rE := by
        change (sdLan.map j' ≫ αW') ≫ rE = (αJ' ≫ dJ'W') ≫ rE
        exact congrArg (fun f => f ≫ rE) (sdLanToDprism.naturality j')
      _ = αJ' ≫ pJinJ' ≫ rPJ := by
        simpa [Category.assoc] using congrArg (fun f => αJ' ≫ f) hOuter.w
      _ = prismTop.app J.toFunctor ≫ rPJ := by
        simpa [Category.assoc] using (congrArg (fun f => f ≫ rPJ) hTopJ).symm)
  have hqJleft : pushout.inl j'' αJ' ≫ qJ = αW' := by
    dsimp [qJ]
    exact pushout.inl_desc _ _ _
  have hqJright : pushout.inr j'' αJ' ≫ qJ = dJ'W' := by
    dsimp [qJ, dJ'W']
    exact pushout.inr_desc _ _ _
  have hq1left : pushout.inl j'' (prismTop.app J.toFunctor) ≫ q1 = αW' ≫ rE := by
    dsimp [q1]
    exact pushout.inl_desc _ _ _
  have hq1right : pushout.inr j'' (prismTop.app J.toFunctor) ≫ q1 = rPJ := by
    dsimp [q1]
    exact pushout.inr_desc _ _ _
  have hFirstComm : qJ ≫ rE = iA ≫ q1 := by
    apply pushout.hom_ext
    · calc
        pushout.inl j'' αJ' ≫ qJ ≫ rE = αW' ≫ rE := by
          simpa [Category.assoc] using congrArg (fun f => f ≫ rE) hqJleft
        _ = pushout.inl j'' (prismTop.app J.toFunctor) ≫ q1 := hq1left.symm
        _ = pushout.inl j'' αJ' ≫ iA ≫ q1 := by
          simpa [Category.assoc] using congrArg (fun f => f ≫ q1) hiAleft.symm
    · calc
        pushout.inr j'' αJ' ≫ qJ ≫ rE = dJ'W' ≫ rE := by
          simpa [Category.assoc] using congrArg (fun f => f ≫ rE) hqJright
        _ = pJinJ' ≫ rPJ := hOuter.w
        _ = pushout.inr j'' αJ' ≫ iA ≫ q1 := by
          calc
            pJinJ' ≫ rPJ = pJinJ' ≫
                (pushout.inr j'' (prismTop.app J.toFunctor) ≫ q1) := by rw [hq1right]
            _ = (pJinJ' ≫ pushout.inr j'' (prismTop.app J.toFunctor)) ≫ q1 := by cat_disch
            _ = (pushout.inr j'' αJ' ≫ iA) ≫ q1 := by rw [hiAright]
            _ = pushout.inr j'' αJ' ≫ iA ≫ q1 := by cat_disch
  have hOuter' : IsPushout (pushout.inr j'' αJ' ≫ qJ) pJinJ' rE
      (pushout.inr j'' (prismTop.app J.toFunctor) ≫ q1) := by
    simpa only [hqJright, hq1right] using hOuter
  have hFirst : IsPushout qJ iA rE q1 := hOuter'.of_left hFirstComm hLeft
  have hq1 : anodyne q1 := anodyne_of_isPushout hFirst.flip hqJ

  let B : SemiSSet := pushout j' αJ
  let bW : W' ⟶ B := pushout.inl j' αJ
  let bJ : dprismLan.obj J.toFunctor ⟶ B := pushout.inr j' αJ
  have hPJsq : αJ ≫ pJinJ = τJ' ≫ pJinJ' := by
    dsimp [pJinJ, pJinJ']
    exact pushout.condition
  have hBsq : j' ≫ bW = αJ ≫ bJ := by
    dsimp [bW, bJ]
    exact pushout.condition
  let b : B ⟶ R := pushout.desc (τW' ≫ rE) (pJinJ ≫ rPJ) (by
    change (j' ≫ τW') ≫ rE = (αJ ≫ pJinJ) ≫ rPJ
    calc
      (j' ≫ τW') ≫ rE = (τJ' ≫ dJ'W') ≫ rE :=
        congrArg (fun f => f ≫ rE) (dprismLanTop.naturality j')
      _ = τJ' ≫ (dJ'W' ≫ rE) := Category.assoc _ _ _
      _ = τJ' ≫ (pJinJ' ≫ rPJ) :=
        congrArg (fun f => τJ' ≫ f) hOuter.w
      _ = (τJ' ≫ pJinJ') ≫ rPJ := (Category.assoc _ _ _).symm
      _ = (αJ ≫ pJinJ) ≫ rPJ := congrArg (fun f => f ≫ rPJ) hPJsq.symm)
  have hbW : bW ≫ b = τW' ≫ rE := by
    dsimp [b]
    exact pushout.inl_desc _ _ _
  have hbJ : bJ ≫ b = pJinJ ≫ rPJ := by
    dsimp [b]
    exact pushout.inr_desc _ _ _

  have hRB : IsPushout bW τW' b rE := by
    let hcond : bW ≫ b = τW' ≫ rE := hbW
    let pMapCond (s : PushoutCocone bW τW') :
        αJ ≫ (bJ ≫ s.inl) = τJ' ≫ (dJ'W' ≫ s.inr) := by
      change (αJ ≫ bJ) ≫ s.inl = (τJ' ≫ dJ'W') ≫ s.inr
      calc
        (αJ ≫ bJ) ≫ s.inl = (j' ≫ bW) ≫ s.inl :=
          congrArg (fun f => f ≫ s.inl) hBsq.symm
        _ = j' ≫ (bW ≫ s.inl) := Category.assoc _ _ _
        _ = j' ≫ (τW' ≫ s.inr) := congrArg (fun f => j' ≫ f) s.condition
        _ = (j' ≫ τW') ≫ s.inr := by
          change j' ≫ (τW' ≫ s.inr) = (j' ≫ τW') ≫ s.inr
          exact (Category.assoc j' τW' s.inr).symm
        _ = (τJ' ≫ dJ'W') ≫ s.inr :=
          congrArg (fun f => f ≫ s.inr) (dprismLanTop.naturality j')
    let pMap (s : PushoutCocone bW τW') : pJ ⟶ s.pt :=
      pushout.desc (bJ ≫ s.inl) (dJ'W' ≫ s.inr) (pMapCond s)
    have hpMapL (s : PushoutCocone bW τW') :
        pJinJ ≫ pMap s = bJ ≫ s.inl := by
      dsimp [pMap]
      exact pushout.inl_desc _ _ _
    have hpMapR (s : PushoutCocone bW τW') :
        pJinJ' ≫ pMap s = dJ'W' ≫ s.inr := by
      dsimp [pMap]
      exact pushout.inr_desc _ _ _
    let desc (s : PushoutCocone bW τW') : R ⟶ s.pt :=
      pushout.desc s.inr (pMap s) (by
        change dJ'W' ≫ s.inr = pJinJ' ≫ pMap s
        exact (hpMapR s).symm)
    have hdescE (s : PushoutCocone bW τW') : rE ≫ desc s = s.inr := by
      dsimp [desc]
      exact pushout.inl_desc _ _ _
    have hdescP (s : PushoutCocone bW τW') : rPJ ≫ desc s = pMap s := by
      dsimp [desc]
      exact pushout.inr_desc _ _ _
    have facB (s : PushoutCocone bW τW') : b ≫ desc s = s.inl := by
      apply pushout.hom_ext
      · calc
          bW ≫ b ≫ desc s = (τW' ≫ rE) ≫ desc s :=
            by simpa [Category.assoc] using congrArg (fun f => f ≫ desc s) hbW
          _ = τW' ≫ s.inr := by
            simpa [Category.assoc] using congrArg (fun f => τW' ≫ f) (hdescE s)
          _ = bW ≫ s.inl := s.condition.symm
      · calc
          bJ ≫ b ≫ desc s = (pJinJ ≫ rPJ) ≫ desc s :=
            by simpa [Category.assoc] using congrArg (fun f => f ≫ desc s) hbJ
          _ = pJinJ ≫ pMap s := by
            simpa [Category.assoc] using congrArg (fun f => pJinJ ≫ f) (hdescP s)
          _ = bJ ≫ s.inl := hpMapL s
    have facE (s : PushoutCocone bW τW') : rE ≫ desc s = s.inr := hdescE s
    have uniq : ∀ (s : PushoutCocone bW τW') (m : R ⟶ s.pt),
        b ≫ m = s.inl → rE ≫ m = s.inr → m = desc s := by
      intro s m hmB hmE
      have hmPJ : rPJ ≫ m = pMap s := by
        apply pushout.hom_ext
        · calc
            pJinJ ≫ rPJ ≫ m = bJ ≫ b ≫ m := by
              simpa [Category.assoc] using congrArg (fun f => f ≫ m) hbJ.symm
            _ = bJ ≫ s.inl := congrArg (fun f => bJ ≫ f) hmB
            _ = pJinJ ≫ pMap s := (hpMapL s).symm
        · calc
            pJinJ' ≫ rPJ ≫ m = dJ'W' ≫ rE ≫ m := by
              simpa [Category.assoc] using congrArg (fun f => f ≫ m) hOuter.w.symm
            _ = dJ'W' ≫ s.inr := congrArg (fun f => dJ'W' ≫ f) hmE
            _ = pJinJ' ≫ pMap s := (hpMapR s).symm
      apply pushout.hom_ext
      · calc
          rE ≫ m = s.inr := hmE
          _ = rE ≫ desc s := (hdescE s).symm
      · exact hmPJ.trans (hdescP s).symm
    exact IsPushout.of_isColimit (c := PushoutCocone.mk b rE hcond)
      (PushoutCocone.IsColimit.mk hcond desc facB facE uniq)

  let q2 : B ⟶ dprismLan.obj W :=
    pushout.desc αW (dprismLan.map J.ι) (sdLanToDprism.naturality J.ι)
  have hq2 : anodyne q2 := by
    exact anodyne_dprismLan_rel W J hW
  let pwL : dprismLan.obj W ⟶ prismP.obj W := pushout.inl αW τW'
  let pwR : dprismLan.obj W' ⟶ prismP.obj W := pushout.inr αW τW'
  have hPmapJ : pJinJ ≫ prismP.map J.ι = dprismLan.map J.ι ≫ pwL := by
    change pushout.inl αJ τJ' ≫
      pushout.map αJ τJ' αW τW' (dprismLan.map J.ι)
        (dprismLan.map (sdLan.map J.ι)) (sdLan.map J.ι)
        (sdLanToDprism.naturality J.ι).symm
        (dprismLanTop.naturality (sdLan.map J.ι)).symm =
      dprismLan.map J.ι ≫ pushout.inl αW τW'
    dsimp only [pushout.map]
    rw [pushout.inl_desc]
  have hPmapJ' : pJinJ' ≫ prismP.map J.ι = dJ'W' ≫ pwR := by
    change pushout.inr αJ τJ' ≫
      pushout.map αJ τJ' αW τW' (dprismLan.map J.ι)
        (dprismLan.map (sdLan.map J.ι)) (sdLan.map J.ι)
        (sdLanToDprism.naturality J.ι).symm
        (dprismLanTop.naturality (sdLan.map J.ι)).symm =
      dprismLan.map (sdLan.map J.ι) ≫ pushout.inr αW τW'
    dsimp only [pushout.map]
    rw [pushout.inr_desc]
  let g : R ⟶ prismP.obj W := pushout.desc pwR (prismP.map J.ι) (by
    change dJ'W' ≫ pwR = pJinJ' ≫ prismP.map J.ι
    exact hPmapJ'.symm)
  have hgl : rE ≫ g = pwR := by
    dsimp [g]
    exact pushout.inl_desc _ _ _
  have hgr : rPJ ≫ g = prismP.map J.ι := by
    dsimp [g]
    exact pushout.inr_desc _ _ _
  have hq2left : bW ≫ q2 = αW := by
    dsimp [bW, q2]
    exact pushout.inl_desc _ _ _
  have hq2right : bJ ≫ q2 = dprismLan.map J.ι := by
    dsimp [bJ, q2]
    exact pushout.inr_desc _ _ _
  have hSecondComm : q2 ≫ pwL = b ≫ g := by
    apply pushout.hom_ext
    · calc
        bW ≫ q2 ≫ pwL = αW ≫ pwL := by
          simpa [Category.assoc] using congrArg (fun f => f ≫ pwL) hq2left
        _ = τW' ≫ pwR := pushout.condition
        _ = bW ≫ b ≫ g := by
          calc
            τW' ≫ pwR = τW' ≫ (rE ≫ g) := by rw [hgl]
            _ = (τW' ≫ rE) ≫ g := by cat_disch
            _ = (bW ≫ b) ≫ g := by rw [hbW]
            _ = bW ≫ b ≫ g := by cat_disch
    · calc
        bJ ≫ q2 ≫ pwL = dprismLan.map J.ι ≫ pwL := by
          simpa [Category.assoc] using congrArg (fun f => f ≫ pwL) hq2right
        _ = pJinJ ≫ prismP.map J.ι := hPmapJ.symm
        _ = bJ ≫ b ≫ g := by
          calc
            pJinJ ≫ prismP.map J.ι = pJinJ ≫ (rPJ ≫ g) := by rw [hgr]
            _ = (pJinJ ≫ rPJ) ≫ g := by cat_disch
            _ = (bJ ≫ b) ≫ g := by rw [hbJ]
            _ = bJ ≫ b ≫ g := by cat_disch
  have hPW : IsPushout αW τW' pwL pwR := by
    dsimp [pwL, pwR]
    exact IsPushout.of_hasPushout αW τW'
  have hPWSq : IsPushout (bW ≫ q2) τW' pwL (rE ≫ g) := by
    rw [hq2left, hgl]
    exact hPW
  have hSecond : IsPushout q2 b pwL g := hPWSq.of_left hSecondComm hRB
  have hq : anodyne (q1 ≫ g) :=
    anodyne_comp' hq1 (anodyne_of_isPushout hSecond.flip hq2)
  have hq0left : pushout.inl j'' (prismTop.app J.toFunctor) ≫ q0 = prismTop.app W := by
    dsimp [q0]
    exact pushout.inl_desc _ _ _
  have hq0right : pushout.inr j'' (prismTop.app J.toFunctor) ≫ q0 = prismP.map J.ι := by
    dsimp [q0]
    exact pushout.inr_desc _ _ _
  have hTopW : prismTop.app W = αW' ≫ pwR := by
    rfl
  have hTarget : q0 = q1 ≫ g := by
    apply pushout.hom_ext
    · calc
        pushout.inl j'' (prismTop.app J.toFunctor) ≫ q0 = prismTop.app W := hq0left
        _ = αW' ≫ pwR := hTopW
        _ = αW' ≫ (rE ≫ g) := by rw [hgl]
        _ = (αW' ≫ rE) ≫ g := (Category.assoc _ _ _).symm
        _ = (pushout.inl j'' (prismTop.app J.toFunctor) ≫ q1) ≫ g :=
          congrArg (fun f => f ≫ g) hq1left.symm
        _ = pushout.inl j'' (prismTop.app J.toFunctor) ≫ q1 ≫ g := by cat_disch
    · calc
        pushout.inr j'' (prismTop.app J.toFunctor) ≫ q0 = prismP.map J.ι := hq0right
        _ = rPJ ≫ g := by rw [hgr]
        _ = (pushout.inr j'' (prismTop.app J.toFunctor) ≫ q1) ≫ g :=
          congrArg (fun f => f ≫ g) hq1right.symm
        _ = pushout.inr j'' (prismTop.app J.toFunctor) ≫ q1 ≫ g := by cat_disch
  change anodyne q0
  rw [hTarget]
  exact hq

end HomotopyHypothesis.Approximation.PrismGluing

#print axioms HomotopyHypothesis.Approximation.PrismGluing.isFinite_of_iso_proof
#print axioms HomotopyHypothesis.Approximation.PrismGluing.isSimplicialComplex_of_iso_proof
#print axioms HomotopyHypothesis.Approximation.PrismGluing.colimitMap_mono_of_stableRange
#print axioms HomotopyHypothesis.Approximation.PrismGluing.mono_dprismLanTop_proof
#print axioms HomotopyHypothesis.Approximation.PrismGluing.mono_sdLanToDprism_proof
#print axioms HomotopyHypothesis.Approximation.PrismGluing.isFinite_dprismLan_proof
#print axioms HomotopyHypothesis.Approximation.PrismGluing.anodyne_prismTop_proof
