import Mathlib.CategoryTheory.Subfunctor.OfSection
import Mathlib.Topology.Maps.Basic
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteSubcomplex.FiniteSubfunctor
import HomotopyHypothesis.Approximation.FiniteSubcomplex.PushoutEmbedding
import HomotopyHypothesis.Approximation.FiniteSubcomplex.SemiBoundaryFacts
import HomotopyHypothesis.Approximation.FiniteSubcomplex.SequentialClosedEmbedding
import HomotopyHypothesis.Approximation.FiniteSubcomplex.SequentialCompactSupport
import HomotopyHypothesis.Approximation.FiniteSubcomplex.TransfiniteMono
import HomotopyHypothesis.Realization.Boundary.RealizationGeometry
import HomotopyHypothesis.Simplicial.CycleRealization.BoundaryMono
universe u

open CategoryTheory Limits Opposite Topology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

private local instance semiRealization_preserves_coproducts :
    PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      HomotopyHypothesis.Henry.SemiSSet.realization.{u} :=
  Presheaf.preservesColimitsOfSize_leftKanExtension.{u, 0, u, u, 0, u + 1, u}
    HomotopyHypothesis.Henry.SemiSSet.toTop.{u}

private local instance semiRealization_preserves_sequentialColimits :
    PreservesColimitsOfSize.{0, 0, u, u, u + 1, u + 1}
      HomotopyHypothesis.Henry.SemiSSet.realization.{u} :=
  Presheaf.preservesColimitsOfSize_leftKanExtension.{u, 0, u, 0, 0, u + 1, 0}
    HomotopyHypothesis.Henry.SemiSSet.toTop.{u}

private local instance semiRealization_preserves_wellOrderContinuous :
    PreservesWellOrderContinuousOfShape ℕ
      HomotopyHypothesis.Henry.SemiSSet.realization.{u} where
  preservesColimitsOfShape n hn := by
    simp at hn

namespace HomotopyHypothesis.Approximation.FiniteSubcomplex

private theorem semiObject_eq_mk
    (a : HomotopyHypothesis.Henry.SemiSimplexCategory) :
    a = HomotopyHypothesis.Henry.SemiSimplexCategory.mk a.obj.len := by
  cases a with
  | mk o =>
    cases o with
    | mk n => rfl

def semiSkeleton (X : HomotopyHypothesis.Henry.SemiSSet.{u}) (n : ℕ) :
    Subfunctor X where
  obj U := if U.unop.obj.len < n then Set.univ else ∅
  map := by
    intro U V f x hx
    change x ∈ (if U.unop.obj.len < n then Set.univ else ∅) at hx
    by_cases hU : U.unop.obj.len < n
    · letI : Mono f.unop.hom := f.unop.property
      have hle : V.unop.obj.len ≤ U.unop.obj.len :=
        SimplexCategory.len_le_of_mono f.unop.hom
      have hV : V.unop.obj.len < n := lt_of_le_of_lt hle hU
      change X.map f x ∈ (if V.unop.obj.len < n then Set.univ else ∅)
      simp [hV]
    · simp [hU] at hx

def semiSkeletonOfMono {A X : HomotopyHypothesis.Henry.SemiSSet.{u}}
    (i : A ⟶ X) (n : ℕ) : Subfunctor X :=
  Subfunctor.range i ⊔ semiSkeleton X n

private def semiSimplexCell {X : HomotopyHypothesis.Henry.SemiSSet.{u}}
    {A : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ) :=
  {x : X.obj (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) //
    x ∉ Set.range (i.app _)}

private def semiSimplexCell.section {A X : HomotopyHypothesis.Henry.SemiSSet.{u}}
    (i : A ⟶ X) (n : ℕ) (x : semiSimplexCell i n) :
    X.obj (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) :=
  x.1

private noncomputable def semiSimplexMap
    (X : HomotopyHypothesis.Henry.SemiSSet.{u}) (n : ℕ)
    (x : X.obj (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) :
    (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) ⟶ X :=
  CategoryTheory.uliftYonedaEquiv.symm x

private theorem semiSimplexMap_app_id
    (X : HomotopyHypothesis.Henry.SemiSSet.{u}) (n : ℕ)
    (x : X.obj (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) :
    (semiSimplexMap X n x).app
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
      (ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) = x := by
  simp [semiSimplexMap, HomotopyHypothesis.Henry.SemiSSet.stdSimplex]

private theorem semiSimplexMap_range
    (X : HomotopyHypothesis.Henry.SemiSSet.{u}) (n : ℕ)
    (x : X.obj (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) :
    Subfunctor.range (semiSimplexMap X n x) = Subfunctor.ofSection x := by
  ext U y
  constructor
  · rintro ⟨z, rfl⟩
    rcases z with ⟨f⟩
    exact ⟨f.op, by simp [semiSimplexMap]⟩
  · rintro ⟨f, rfl⟩
    refine ⟨ULift.up f.unop, ?_⟩
    simp [semiSimplexMap]

/-- A simplex map whose generator lies in a subfunctor factors through that subfunctor. -/
theorem semiSimplexMap_factors_through_subfunctor
    {X : HomotopyHypothesis.Henry.SemiSSet.{u}} (Y : Subfunctor X) (n : ℕ)
    (x : X.obj (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)))
    (hx : x ∈ Y.obj (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) :
    ∃ f : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) ⟶ Y.toFunctor,
      f ≫ Y.ι = semiSimplexMap X n x := by
  let g := semiSimplexMap X n x
  have hle : Subfunctor.range g ≤ Y := by
    rw [semiSimplexMap_range]
    rw [Subfunctor.ofSection_le_iff]
    exact hx
  exact ⟨Subfunctor.lift g hle, Subfunctor.lift_ι g hle⟩

theorem semiSkeletonOfMono_succ {A X : HomotopyHypothesis.Henry.SemiSSet.{u}}
    (i : A ⟶ X) (n : ℕ) :
    semiSkeletonOfMono i (n + 1) =
      semiSkeletonOfMono i n ⊔
        ⨆ x : semiSimplexCell i n,
          Subfunctor.ofSection (semiSimplexCell.section i n x) := by
  classical
  ext U y
  cases U with
  | op a =>
    cases a with
    | mk b =>
      cases b with
      | mk m =>
        by_cases hmn : m < n
        · have hmle : m ≤ n := Nat.le_of_lt hmn
          simp [semiSkeletonOfMono, semiSkeleton, hmn, hmle]
        · by_cases hEq : m = n
          · subst m
            simp only [semiSkeletonOfMono, Subfunctor.max_obj, semiSkeleton,
              Subfunctor.iSup_obj, Subfunctor.range_obj, semiSimplexCell,
              semiSimplexCell.section]
            simp only [if_pos (Nat.lt_succ_self n), if_neg (lt_irrefl n),
              Set.mem_univ, Set.mem_empty_iff_false, Set.mem_union,
              Set.mem_iUnion, Set.mem_range, or_true, or_false]
            constructor
            · intro _
              by_cases hy : y ∈ Set.range (i.app _)
              · exact Or.inl (Set.mem_range.mp hy)
              · right
                refine ⟨⟨y, hy⟩, ?_⟩
                exact Subfunctor.mem_ofSection_obj y
            · intro _
              simp
          · have hnm : n < m := by omega
            have hsecEmpty (x : semiSimplexCell i n) :
                (Subfunctor.ofSection x.1).obj
                  (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro z hz
              have hface : ∃ f :
                  op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶
                    op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m),
                  X.map f x.1 = z := by
                simpa [Subfunctor.ofSection_obj] using hz
              obtain ⟨f, _⟩ := hface
              have hle : m ≤ n := by
                letI : Mono f.unop.hom := f.unop.property
                exact SimplexCategory.len_le_of_mono f.unop.hom
              omega
            have hleft : ¬ m < n + 1 := by omega
            simp only [semiSkeletonOfMono, Subfunctor.max_obj, semiSkeleton,
              Subfunctor.iSup_obj, Subfunctor.range_obj, semiSimplexCell,
              semiSimplexCell.section]
            simp only [if_neg hleft, if_neg hmn, Set.mem_empty_iff_false,
              Set.mem_union, Set.mem_iUnion, Set.mem_range, or_false]
            constructor
            · intro hr
              exact Or.inl hr
            · rintro (hr | ⟨x, hx⟩)
              · exact hr
              · rw [hsecEmpty x] at hx
                simp at hx

private theorem semiBoundary_range_le_stage
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ)
    (x : semiSimplexCell i n) :
    Subfunctor.range
      ((HomotopyHypothesis.Henry.SemiSSet.boundary n).ι ≫
        semiSimplexMap X n x.1) ≤ semiSkeletonOfMono i n := by
  intro U y hy
  rcases hy with ⟨b, rfl⟩
  have hdim : U.unop.obj.len < n :=
    semiBoundary_element_dim_lt (x := b.1) b.2
  simp only [semiSkeletonOfMono, Subfunctor.max_obj]
  right
  simp [semiSkeleton, hdim]

private theorem semiSimplex_range_le_stage
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ)
    (x : semiSimplexCell i n) :
    Subfunctor.range (semiSimplexMap X n x.1) ≤ semiSkeletonOfMono i (n + 1) := by
  rw [semiSimplexMap_range]
  rw [semiSkeletonOfMono_succ]
  exact le_trans (le_iSup (fun y : semiSimplexCell i n => Subfunctor.ofSection y.1) x)
    le_sup_right

private noncomputable abbrev semiCellBoundaryCoproduct
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ) :=
  ∐ fun (_ : semiSimplexCell i n) => (HomotopyHypothesis.Henry.SemiSSet.boundary n).toFunctor

private noncomputable abbrev semiCellSimplexCoproduct
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ) :=
  ∐ fun (_ : semiSimplexCell i n) =>
    HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)

private theorem semiCellSimplex_jointly_surjective
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ)
    {U : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ}
    (z : (semiCellSimplexCoproduct i n).obj U) :
    ∃ (x : semiSimplexCell i n)
      (s : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).obj U),
      (Sigma.ι (fun (_ : semiSimplexCell i n) =>
        HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x).app U s = z :=
  Cofan.inj_jointly_surjective_of_isColimit
    (isColimitCofanMkObjOfIsColimit
      ((CategoryTheory.evaluation _ _).obj U) _ _
      (coproductIsCoproduct _)) z

private theorem semiCellBoundary_jointly_surjective
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ)
    {U : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ}
    (z : (semiCellBoundaryCoproduct i n).obj U) :
    ∃ (x : semiSimplexCell i n)
      (s : ((HomotopyHypothesis.Henry.SemiSSet.boundary n).toFunctor).obj U),
      (Sigma.ι (fun (_ : semiSimplexCell i n) =>
        (HomotopyHypothesis.Henry.SemiSSet.boundary n).toFunctor) x).app U s = z :=
  Cofan.inj_jointly_surjective_of_isColimit
    (isColimitCofanMkObjOfIsColimit
      ((CategoryTheory.evaluation _ _).obj U) _ _
      (coproductIsCoproduct _)) z

private noncomputable def semiCellSimplex_app_isColimit
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ)
    (U : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ) :
    IsColimit (Cofan.mk ((semiCellSimplexCoproduct i n).obj U)
      (fun x => (Sigma.ι (fun (_ : semiSimplexCell i n) =>
        HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x).app U)) :=
  isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj U) _ _
    (coproductIsCoproduct _)

private noncomputable def semiCellBoundary_app_isColimit
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ)
    (U : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ) :
    IsColimit (Cofan.mk ((semiCellBoundaryCoproduct i n).obj U)
      (fun x => (Sigma.ι (fun (_ : semiSimplexCell i n) =>
        (HomotopyHypothesis.Henry.SemiSSet.boundary n).toFunctor) x).app U)) :=
  isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj U) _ _
    (coproductIsCoproduct _)

private noncomputable def semiCellCoproductBoundaryMap
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ) :
    semiCellBoundaryCoproduct i n ⟶ semiCellSimplexCoproduct i n :=
  Limits.Sigma.map (fun _ => (HomotopyHypothesis.Henry.SemiSSet.boundary n).ι)

private theorem semiCellCoproductBoundaryMap_ι
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ)
    (x : semiSimplexCell i n) {U : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ}
    (s : ((HomotopyHypothesis.Henry.SemiSSet.boundary n).toFunctor).obj U) :
    (semiCellCoproductBoundaryMap i n).app U
        ((Sigma.ι (fun (_ : semiSimplexCell i n) =>
          (HomotopyHypothesis.Henry.SemiSSet.boundary n).toFunctor) x).app U s) =
      (Sigma.ι (fun (_ : semiSimplexCell i n) =>
        HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x).app U
        ((HomotopyHypothesis.Henry.SemiSSet.boundary n).ι.app U s) := by
  have hcomp :
      (Sigma.ι (fun (_ : semiSimplexCell i n) =>
        (HomotopyHypothesis.Henry.SemiSSet.boundary n).toFunctor) x) ≫
          semiCellCoproductBoundaryMap i n =
        (HomotopyHypothesis.Henry.SemiSSet.boundary n).ι ≫
          Sigma.ι (fun (_ : semiSimplexCell i n) =>
            HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
              (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x := by
    simpa [semiCellCoproductBoundaryMap] using
      (CategoryTheory.Limits.Sigma.ι_comp_map'
        (p := id) (q := fun _ => (HomotopyHypothesis.Henry.SemiSSet.boundary n).ι) x)
  exact congrArg (fun f => f.app U s) hcomp

private theorem semiCellCoproductBoundaryMap_app_bijective_of_full
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ)
    (U : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (hfull : ∀ s : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).obj U,
      s ∈ (HomotopyHypothesis.Henry.SemiSSet.boundary n).obj U) :
    Function.Bijective ((semiCellCoproductBoundaryMap i n).app U) := by
  constructor
  · intro a b hab
    obtain ⟨x, s, ha⟩ := semiCellBoundary_jointly_surjective i n a
    obtain ⟨x', s', hb⟩ := semiCellBoundary_jointly_surjective i n b
    let hc := semiCellSimplex_app_isColimit i n U
    have hsimplex :
        (Sigma.ι (fun (_ : semiSimplexCell i n) =>
          HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
            (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x).app U
          ((HomotopyHypothesis.Henry.SemiSSet.boundary n).ι.app U s) =
        (Sigma.ι (fun (_ : semiSimplexCell i n) =>
          HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
            (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x').app U
          ((HomotopyHypothesis.Henry.SemiSSet.boundary n).ι.app U s') := by
      calc
        _ = ((semiCellCoproductBoundaryMap i n).app U) a := by
          rw [← ha]
          exact (semiCellCoproductBoundaryMap_ι i n x s).symm
        _ = ((semiCellCoproductBoundaryMap i n).app U) b := hab
        _ = _ := by
          rw [← hb]
          exact semiCellCoproductBoundaryMap_ι i n x' s'
    have hcell := Cofan.eq_of_inj_apply_eq_of_isColimit hc _ _ hsimplex
    subst x'
    have hsimplex' :
        (Sigma.ι (fun (_ : semiSimplexCell i n) =>
          HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
            (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x).app U
          ((HomotopyHypothesis.Henry.SemiSSet.boundary n).ι.app U s) =
        (Sigma.ι (fun (_ : semiSimplexCell i n) =>
          HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
            (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x).app U
          ((HomotopyHypothesis.Henry.SemiSSet.boundary n).ι.app U s') := hsimplex
    have hsVal := (Cofan.inj_injective_of_isColimit hc x) hsimplex'
    have hs : s = s' := Subtype.ext hsVal
    calc
      a = (Sigma.ι (fun (_ : semiSimplexCell i n) =>
        (HomotopyHypothesis.Henry.SemiSSet.boundary n).toFunctor) x).app U s := ha.symm
      _ = (Sigma.ι (fun (_ : semiSimplexCell i n) =>
        (HomotopyHypothesis.Henry.SemiSSet.boundary n).toFunctor) x).app U s' :=
          congrArg ((Sigma.ι (fun (_ : semiSimplexCell i n) =>
            (HomotopyHypothesis.Henry.SemiSSet.boundary n).toFunctor) x).app U) hs
      _ = b := hb
  · intro z
    obtain ⟨x, s, hz⟩ := semiCellSimplex_jointly_surjective i n z
    refine ⟨(Sigma.ι (fun (_ : semiSimplexCell i n) =>
      (HomotopyHypothesis.Henry.SemiSSet.boundary n).toFunctor) x).app U
        ⟨s, hfull s⟩, ?_⟩
    rw [semiCellCoproductBoundaryMap_ι]
    simpa using hz

private noncomputable def semiCellCoproductAttachMap
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ) :
    semiCellBoundaryCoproduct i n ⟶ (semiSkeletonOfMono i n).toFunctor :=
  Sigma.desc fun x =>
    Subfunctor.lift
      ((HomotopyHypothesis.Henry.SemiSSet.boundary n).ι ≫ semiSimplexMap X n x.1)
      (semiBoundary_range_le_stage i n x)

private noncomputable def semiCellCoproductGeneratorMap
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ) :
    semiCellSimplexCoproduct i n ⟶ (semiSkeletonOfMono i (n + 1)).toFunctor :=
  Sigma.desc fun x =>
    Subfunctor.lift (semiSimplexMap X n x.1) (semiSimplex_range_le_stage i n x)

private theorem semiCellCoproductGeneratorMap_ι
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ)
    (x : semiSimplexCell i n) :
    (Sigma.ι (fun (_ : semiSimplexCell i n) =>
      HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x) ≫
        semiCellCoproductGeneratorMap i n =
      Subfunctor.lift (semiSimplexMap X n x.1) (semiSimplex_range_le_stage i n x) := by
  simp [semiCellCoproductGeneratorMap]

private noncomputable def semiSkeletonStep
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ) :
    (semiSkeletonOfMono i n).toFunctor ⟶ (semiSkeletonOfMono i (n + 1)).toFunctor :=
  Subfunctor.homOfLe (by
    rw [semiSkeletonOfMono_succ]
    exact le_sup_left)

private theorem semiStdSimplex_obj_subsingleton_at_dim (n : ℕ) :
    Subsingleton ((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).obj
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) := by
  refine ⟨fun x y => ?_⟩
  cases x with
  | up x =>
    cases y with
    | up y =>
      have hx := semiSimplex_endomorphism_eq_id n x
      have hy := semiSimplex_endomorphism_eq_id n y
      have hxy : x = y := hx.trans hy.symm
      cases hxy
      rfl

private theorem semiSkeletonStep_app_injective
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n m : ℕ) :
    Function.Injective ((semiSkeletonStep i n).app
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) ) := by
  intro a b h
  apply Subtype.ext
  simpa [semiSkeletonStep, Subfunctor.homOfLe] using
    congrArg (fun z : (semiSkeletonOfMono i (n + 1)).obj
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) => z.1) h

private theorem semiCellCoproductGeneratorMap_ι_app_val
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ)
    (x : semiSimplexCell i n)
    (s : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).obj
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)))
    (hs : s = ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) :
    ((semiCellCoproductGeneratorMap i n).app
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
      ((Sigma.ι (fun (_ : semiSimplexCell i n) =>
        HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) s)).1 = x.1 := by
  rw [hs]
  have hcomp := semiCellCoproductGeneratorMap_ι i n x
  have happ := congrArg (fun f => f.app
    (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) s) hcomp
  rw [hs, NatTrans.comp_app] at happ
  calc
    _ = (semiSimplexMap X n x.1).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
        (ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) := by
      simpa [Subfunctor.lift] using congrArg Subtype.val happ
    _ = x.1 := semiSimplexMap_app_id X n x.1

private theorem semiCellCoproductGeneratorMap_app_injective_at_dim
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ) :
    Function.Injective ((semiCellCoproductGeneratorMap i n).app
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) := by
  intro a b hab
  obtain ⟨x, s, ha⟩ := semiCellSimplex_jointly_surjective i n a
  obtain ⟨y, t, hb⟩ := semiCellSimplex_jointly_surjective i n b
  have hs : s = ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) :=
    (semiStdSimplex_obj_subsingleton_at_dim n).elim _ _
  have ht : t = ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) :=
    (semiStdSimplex_obj_subsingleton_at_dim n).elim _ _
  have hval := congrArg Subtype.val hab
  rw [← ha, ← hb] at hval
  rw [semiCellCoproductGeneratorMap_ι_app_val i n x s hs,
    semiCellCoproductGeneratorMap_ι_app_val i n y t ht] at hval
  have hxy : x.1 = y.1 := hval
  have hcell : x = y := Subtype.ext hxy
  subst y
  have hst : s = t := (semiStdSimplex_obj_subsingleton_at_dim n).elim _ _
  have hinj := congrArg ((Sigma.ι (fun (_ : semiSimplexCell i n) =>
    HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x).app
    (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) hst
  exact ha.symm.trans (hinj.trans hb)

private theorem semiCellGeneratorMap_not_in_old_stage_at_dim
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ)
    (c : (semiCellSimplexCoproduct i n).obj
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)))
    (a : (semiSkeletonOfMono i n).obj
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)))
    (h : (semiCellCoproductGeneratorMap i n).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) c =
      (semiSkeletonStep i n).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) a) : False := by
  obtain ⟨x, s, hc⟩ := semiCellSimplex_jointly_surjective i n c
  have hs : s = ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) :=
    (semiStdSimplex_obj_subsingleton_at_dim n).elim _ _
  have hval := congrArg Subtype.val h
  rw [← hc] at hval
  rw [semiCellCoproductGeneratorMap_ι_app_val i n x s hs] at hval
  have hstep : ((semiSkeletonStep i n).app
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) a).1 = a.1 := by
    simp [semiSkeletonStep, Subfunctor.homOfLe]
  rw [hstep] at hval
  have ha : a.1 ∈ Set.range (i.app
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) := by
    simpa [semiSkeletonOfMono, semiSkeleton] using a.2
  rcases ha with ⟨y, hy⟩
  exact x.2 ⟨y, hy.trans hval.symm⟩

private theorem topCat_sigma_map_mono {I : Type u}
    {A B : I → TopCat.{u}} (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, Mono (f i)) : Mono (Limits.Sigma.map f) := by
  rw [TopCat.mono_iff_injective]
  intro a b hab
  let U := forget TopCat
  let cA : Cofan (fun i => U.obj (A i)) :=
    Cofan.mk (U.obj (∐ A)) (fun i => U.map (Sigma.ι A i))
  let cB : Cofan (fun i => U.obj (B i)) :=
    Cofan.mk (U.obj (∐ B)) (fun i => U.map (Sigma.ι B i))
  have hcA : IsColimit cA :=
    isColimitCofanMkObjOfIsColimit U A _ (coproductIsCoproduct A)
  have hcB : IsColimit cB :=
    isColimitCofanMkObjOfIsColimit U B _ (coproductIsCoproduct B)
  obtain ⟨i, x, hx⟩ := Cofan.inj_jointly_surjective_of_isColimit hcA a
  obtain ⟨j, y, hy⟩ := Cofan.inj_jointly_surjective_of_isColimit hcA b
  have hcomp (i : I) : U.map (Sigma.ι A i) ≫ U.map (Limits.Sigma.map f) =
      U.map (f i) ≫ U.map (Sigma.ι B i) := by
    calc
      _ = U.map (Sigma.ι A i ≫ Limits.Sigma.map f) := (U.map_comp _ _).symm
      _ = U.map (f i ≫ Sigma.ι B i) := by
        change U.map (Sigma.ι A i ≫ Sigma.map' id f) = _
        rw [Sigma.ι_comp_map']
      _ = _ := U.map_comp _ _
  have himg' : U.map (Limits.Sigma.map f) (U.map (Sigma.ι A i) x) =
      U.map (Limits.Sigma.map f) (U.map (Sigma.ι A j) y) := by
    change U.map (Limits.Sigma.map f) a = U.map (Limits.Sigma.map f) b at hab
    rw [← hx, ← hy] at hab
    exact hab
  have himg : cB.inj i (U.map (f i) x) = cB.inj j (U.map (f j) y) := by
    calc
      _ = U.map (Limits.Sigma.map f) (U.map (Sigma.ι A i) x) := by
        exact (congrArg (fun k => k x) (hcomp i)).symm
      _ = U.map (Limits.Sigma.map f) (U.map (Sigma.ι A j) y) := himg'
      _ = _ := congrArg (fun k => k y) (hcomp j)
  obtain rfl : i = j := Cofan.eq_of_inj_apply_eq_of_isColimit hcB _ _ himg
  have hxy : U.map (f i) x = U.map (f i) y :=
    (Cofan.inj_injective_of_isColimit hcB i) himg
  have hxy' : x = y := (TopCat.mono_iff_injective (f i)).mp (hf i) hxy
  exact hx.symm.trans ((congrArg (cA.inj i) hxy').trans hy)

private theorem semiRealization_sigma_map_mono {I : Type u}
    {A B : I → HomotopyHypothesis.Henry.SemiSSet.{u}}
    (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, Mono (HomotopyHypothesis.Henry.SemiSSet.realization.map (f i))) :
    Mono (HomotopyHypothesis.Henry.SemiSSet.realization.map (Limits.Sigma.map f)) := by
  let R : HomotopyHypothesis.Henry.SemiSSet.{u} ⥤ TopCat.{u} :=
    HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtension
      HomotopyHypothesis.Henry.SemiSSet.toTop.{u}
  letI : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} R := by
    change PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtension
        HomotopyHypothesis.Henry.SemiSSet.toTop.{u})
    exact Presheaf.preservesColimitsOfSize_leftKanExtension.{u, 0, u, u, 0, u + 1, u}
      HomotopyHypothesis.Henry.SemiSSet.toTop.{u}
  let hcolA := isColimitOfHasCoproductOfPreservesColimit R A
  let hcolB := isColimitOfHasCoproductOfPreservesColimit R B
  let eA := hcolA.coconePointUniqueUpToIso (coproductIsCoproduct fun i => R.obj (A i))
  let eB := hcolB.coconePointUniqueUpToIso (coproductIsCoproduct fun i => R.obj (B i))
  let sumMap := Limits.Sigma.map (fun i => R.map (f i))
  have hsum : Mono sumMap := by
    exact topCat_sigma_map_mono _ hf
  have hcomm : eA.hom ≫ sumMap = R.map (Limits.Sigma.map f) ≫ eB.hom := by
    apply hcolA.hom_ext
    intro i
    let i₀ := i.as
    change (R.map (Sigma.ι A i₀) ≫ eA.hom) ≫ sumMap =
      (R.map (Sigma.ι A i₀) ≫ R.map (Limits.Sigma.map f)) ≫ eB.hom
    have hEA : R.map (Sigma.ι A i₀) ≫ eA.hom =
        Sigma.ι (fun j => R.obj (A j)) i₀ := by
      exact IsColimit.comp_coconePointUniqueUpToIso_hom hcolA
        (coproductIsCoproduct fun j => R.obj (A j)) (Discrete.mk i₀)
    have hEB : R.map (Sigma.ι B i₀) ≫ eB.hom =
        Sigma.ι (fun j => R.obj (B j)) i₀ := by
      exact IsColimit.comp_coconePointUniqueUpToIso_hom hcolB
        (coproductIsCoproduct fun j => R.obj (B j)) (Discrete.mk i₀)
    calc
      _ = Sigma.ι (fun j => R.obj (A j)) i₀ ≫ sumMap := by rw [hEA]
      _ = R.map (f i₀) ≫ Sigma.ι (fun j => R.obj (B j)) i₀ := by simp [sumMap]
      _ = R.map (f i₀) ≫ (R.map (Sigma.ι B i₀) ≫ eB.hom) := by rw [hEB]
      _ = R.map (Sigma.ι A i₀) ≫ R.map (Limits.Sigma.map f) ≫ eB.hom := by
        change (R.map (f i₀) ≫ R.map (Sigma.ι B i₀)) ≫ eB.hom =
          (R.map (Sigma.ι A i₀) ≫ R.map (Limits.Sigma.map f)) ≫ eB.hom
        apply (cancel_mono eB.hom).2
        rw [← R.map_comp, ← R.map_comp]
        simpa [Sigma.map] using
          (congrArg R.map
            (Sigma.ι_comp_map' (p := id) (q := f) i₀)).symm
  have hcomp : Mono (R.map (Limits.Sigma.map f) ≫ eB.hom) := by
    rw [← hcomm]
    infer_instance
  letI : Mono (R.map (Limits.Sigma.map f) ≫ eB.hom) := hcomp
  refine ⟨?_⟩
  intro Z g h hgh
  have hgh' : g ≫ R.map (Limits.Sigma.map f) = h ≫ R.map (Limits.Sigma.map f) := by
    exact hgh
  have hgh'' : g ≫ (R.map (Limits.Sigma.map f) ≫ eB.hom) =
      h ≫ (R.map (Limits.Sigma.map f) ≫ eB.hom) := by
    change (g ≫ R.map (Limits.Sigma.map f)) ≫ eB.hom =
      (h ≫ R.map (Limits.Sigma.map f)) ≫ eB.hom
    exact congrArg (fun k => k ≫ eB.hom) hgh'
  exact (cancel_mono (R.map (Limits.Sigma.map f) ≫ eB.hom)).1 hgh''

private theorem semiRealization_sigma_map_closedEmbedding {I : Type u}
    {A B : I → HomotopyHypothesis.Henry.SemiSSet.{u}}
    (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, IsClosedEmbedding
      (HomotopyHypothesis.Henry.SemiSSet.realization.map (f i)).hom) :
    IsClosedEmbedding
      (HomotopyHypothesis.Henry.SemiSSet.realization.map (Limits.Sigma.map f)).hom := by
  let R : HomotopyHypothesis.Henry.SemiSSet.{u} ⥤ TopCat.{u} :=
    HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtension
      HomotopyHypothesis.Henry.SemiSSet.toTop.{u}
  letI : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} R := by
    change PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtension
        HomotopyHypothesis.Henry.SemiSSet.toTop.{u})
    exact Presheaf.preservesColimitsOfSize_leftKanExtension.{u, 0, u, u, 0, u + 1, u}
      HomotopyHypothesis.Henry.SemiSSet.toTop.{u}
  let hcolA := isColimitOfHasCoproductOfPreservesColimit R A
  let hcolB := isColimitOfHasCoproductOfPreservesColimit R B
  let eA := hcolA.coconePointUniqueUpToIso (coproductIsCoproduct fun i => R.obj (A i))
  let eB := hcolB.coconePointUniqueUpToIso (coproductIsCoproduct fun i => R.obj (B i))
  let sumMap := Limits.Sigma.map (fun i => R.map (f i))
  have hsum : IsClosedEmbedding sumMap.hom :=
    topCat_sigma_map_isClosedEmbedding _ hf
  have hcomm : eA.hom ≫ sumMap = R.map (Limits.Sigma.map f) ≫ eB.hom := by
    apply hcolA.hom_ext
    intro i
    let i₀ := i.as
    change (R.map (Sigma.ι A i₀) ≫ eA.hom) ≫ sumMap =
      (R.map (Sigma.ι A i₀) ≫ R.map (Limits.Sigma.map f)) ≫ eB.hom
    have hEA : R.map (Sigma.ι A i₀) ≫ eA.hom =
        Sigma.ι (fun j => R.obj (A j)) i₀ := by
      exact IsColimit.comp_coconePointUniqueUpToIso_hom hcolA
        (coproductIsCoproduct fun j => R.obj (A j)) (Discrete.mk i₀)
    have hEB : R.map (Sigma.ι B i₀) ≫ eB.hom =
        Sigma.ι (fun j => R.obj (B j)) i₀ := by
      exact IsColimit.comp_coconePointUniqueUpToIso_hom hcolB
        (coproductIsCoproduct fun j => R.obj (B j)) (Discrete.mk i₀)
    calc
      _ = Sigma.ι (fun j => R.obj (A j)) i₀ ≫ sumMap := by rw [hEA]
      _ = R.map (f i₀) ≫ Sigma.ι (fun j => R.obj (B j)) i₀ := by simp [sumMap]
      _ = R.map (f i₀) ≫ (R.map (Sigma.ι B i₀) ≫ eB.hom) := by rw [hEB]
      _ = R.map (Sigma.ι A i₀) ≫ R.map (Limits.Sigma.map f) ≫ eB.hom := by
        change (R.map (f i₀) ≫ R.map (Sigma.ι B i₀)) ≫ eB.hom =
          (R.map (Sigma.ι A i₀) ≫ R.map (Limits.Sigma.map f)) ≫ eB.hom
        apply (cancel_mono eB.hom).2
        rw [← R.map_comp, ← R.map_comp]
        simpa [Sigma.map] using
          (congrArg R.map
            (Sigma.ι_comp_map' (p := id) (q := f) i₀)).symm
  have hA : IsClosedEmbedding eA.hom.hom := (TopCat.homeoOfIso eA).isClosedEmbedding
  have hcomp : IsClosedEmbedding (R.map (Limits.Sigma.map f) ≫ eB.hom).hom := by
    rw [← hcomm]
    exact hsum.comp hA
  have hB : IsClosedEmbedding eB.inv.hom :=
    (TopCat.homeoOfIso eB).symm.isClosedEmbedding
  have hfinal : IsClosedEmbedding (R.map (Limits.Sigma.map f) ≫ eB.hom ≫ eB.inv).hom :=
    hB.comp hcomp
  change IsClosedEmbedding (R.map (Limits.Sigma.map f)).hom
  simpa using hfinal

private theorem semiSkeletonStep_square_commutes
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ) :
    semiCellCoproductBoundaryMap i n ≫ semiCellCoproductGeneratorMap i n =
      semiCellCoproductAttachMap i n ≫ semiSkeletonStep i n := by
  apply Limits.Sigma.hom_ext
  intro x
  apply (cancel_mono ((semiSkeletonOfMono i (n + 1)).ι)).1
  simp [semiCellCoproductBoundaryMap, semiCellCoproductGeneratorMap,
    semiCellCoproductAttachMap, semiSkeletonStep, Category.assoc]

private theorem semiSkeletonStep_app_ranges_cover
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n m : ℕ) :
    Set.range ((semiSkeletonStep i n).app
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))) ∪
      Set.range ((semiCellCoproductGeneratorMap i n).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))) = Set.univ := by
  classical
  let U := op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    let y : X.obj U := z.1
    have hz : y ∈ (semiSkeletonOfMono i (n + 1)).obj U := z.2
    rw [semiSkeletonOfMono_succ] at hz
    simp only [Subfunctor.max_obj, Subfunctor.iSup_obj,
      Set.mem_union, Set.mem_iUnion] at hz
    rcases hz with hOld | ⟨x, hx⟩
    · left
      refine ⟨⟨y, hOld⟩, ?_⟩
      apply Subtype.ext
      rfl
    · right
      have hrange : y ∈
          (Subfunctor.range (semiSimplexMap X n x.1)).obj U := by
        rw [semiSimplexMap_range]
        exact hx
      have hrange' : y ∈ Set.range ((semiSimplexMap X n x.1).app U) := by
        simpa only [Subfunctor.range_obj] using hrange
      rcases hrange' with ⟨s, hs⟩
      refine ⟨(Sigma.ι (fun (_ : semiSimplexCell i n) =>
        HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x).app U s, ?_⟩
      apply Subtype.ext
      have hcomp :
          (Sigma.ι (fun (_ : semiSimplexCell i n) =>
            HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
              (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x) ≫
              semiCellCoproductGeneratorMap i n =
            Subfunctor.lift (semiSimplexMap X n x.1)
              (semiSimplex_range_le_stage i n x) := by
        simp [semiCellCoproductGeneratorMap]
      have hval := congrArg (fun f => f.app U s) hcomp
      have hval' : ((semiCellCoproductGeneratorMap i n).app U
          ((Sigma.ι (fun (_ : semiSimplexCell i n) =>
            HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
              (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x).app U s)).val =
          (semiSimplexMap X n x.1).app U s := by
        simpa [Subfunctor.lift] using congrArg Subtype.val hval
      simpa [y] using hval'.trans hs

private theorem semiSkeletonStep_app_isPushout_of_dim_eq
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ) :
    IsPushout
      ((semiCellCoproductBoundaryMap i n).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)))
      ((semiCellCoproductAttachMap i n).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)))
      ((semiCellCoproductGeneratorMap i n).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)))
      ((semiSkeletonStep i n).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) := by
  let U := op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
  have hboundary : IsEmpty
      ((HomotopyHypothesis.Henry.SemiSSet.boundary n).toFunctor.obj U) := by
    refine ⟨fun s => ?_⟩
    have hs : s.1 ∈ (HomotopyHypothesis.Henry.SemiSSet.boundary n).obj U := s.2
    have hbound : (HomotopyHypothesis.Henry.SemiSSet.boundary n).obj U = ∅ := by
      simpa [U] using semiBoundary_obj_eq_empty_of_eq n
    have hs' : s.1 ∈ (∅ : Set _) := hbound ▸ hs
    exact hs'
  have hB : IsEmpty ((semiCellBoundaryCoproduct i n).obj U) := by
    refine ⟨fun z => ?_⟩
    obtain ⟨x, s, _⟩ := semiCellBoundary_jointly_surjective i n z
    exact hboundary.false s
  have hcomm :
      ((semiCellCoproductBoundaryMap i n).app U ≫
        (semiCellCoproductGeneratorMap i n).app U) =
      ((semiCellCoproductAttachMap i n).app U ≫
        (semiSkeletonStep i n).app U) := by
    simpa only [NatTrans.comp_app] using
      congrArg (fun f => f.app U) (semiSkeletonStep_square_commutes i n)
  have hpull : IsPullback
      ((semiCellCoproductBoundaryMap i n).app U)
      ((semiCellCoproductAttachMap i n).app U)
      ((semiCellCoproductGeneratorMap i n).app U)
      ((semiSkeletonStep i n).app U) := by
    rw [CategoryTheory.Limits.Types.isPullback_iff]
    refine ⟨hcomm, ?_, ?_⟩
    · intro a b _
      exact (hB.false a).elim
    · intro c a hca
      exact False.elim (semiCellGeneratorMap_not_in_old_stage_at_dim i n c a hca)
  letI : Mono ((semiCellCoproductGeneratorMap i n).app U) :=
    (mono_iff_injective _).2 (semiCellCoproductGeneratorMap_app_injective_at_dim i n)
  have hcover : Set.range ((semiCellCoproductGeneratorMap i n).app U) ⊔
      Set.range ((semiSkeletonStep i n).app U) = Set.univ := by
    simpa [Set.sup_eq_union, Set.union_comm] using
      semiSkeletonStep_app_ranges_cover i n n
  have hstep : Function.Injective ((semiSkeletonStep i n).app U) :=
    semiSkeletonStep_app_injective i n n
  exact CategoryTheory.Limits.Types.isPushout_of_isPullback_of_mono'
    hpull hcover (fun _ _ _ _ h => hstep h)

private theorem semiSkeletonStep_app_bijective_of_dim_neq
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n m : ℕ)
    (hmn : m < n ∨ n < m) :
    Function.Bijective ((semiSkeletonStep i n).app
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) ) := by
  constructor
  · intro a b h
    apply Subtype.ext
    simpa [semiSkeletonStep, Subfunctor.homOfLe] using
      congrArg (fun z : (semiSkeletonOfMono i (n + 1)).obj
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) => z.1) h
  · intro b
    by_cases hm : m < n
    · refine ⟨⟨b.1, ?_⟩, ?_⟩
      · simp [semiSkeletonOfMono, semiSkeleton, hm]
      · apply Subtype.ext
        rfl
    · have hnm : n < m := by omega
      have hleft : ¬ m < n := by omega
      have hright : ¬ m < n + 1 := by omega
      have hb : (∃ y, (i.app
          (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))) y = b.1) ∨
          m ≤ n := by
        simpa [semiSkeletonOfMono, semiSkeleton, hright] using b.2
      rcases hb with hb | hb
      · refine ⟨⟨b.1, Or.inl hb⟩, ?_⟩
        apply Subtype.ext
        rfl
      · omega

private theorem semiSkeletonStep_app_isPushout_of_dim_neq
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n m : ℕ)
    (hmn : m < n ∨ n < m) :
    IsPushout
      ((semiCellCoproductBoundaryMap i n).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)))
      ((semiCellCoproductAttachMap i n).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)))
      ((semiCellCoproductGeneratorMap i n).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)))
      ((semiSkeletonStep i n).app
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) ) := by
  let U := op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)
  have hfull : ∀ s : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).obj U,
      s ∈ (HomotopyHypothesis.Henry.SemiSSet.boundary n).obj U := by
    intro s
    rcases hmn with hlt | hgt
    · rw [semiBoundary_obj_eq_univ_of_lt n m hlt]
      exact Set.mem_univ _
    · exact False.elim
        ((semiStdSimplex_obj_eq_empty_of_lt n m hgt).false s)
  letI : IsIso ((semiCellCoproductBoundaryMap i n).app U) :=
    (CategoryTheory.isIso_iff_bijective _).2
      (semiCellCoproductBoundaryMap_app_bijective_of_full i n U hfull)
  letI : IsIso ((semiSkeletonStep i n).app U) :=
    (CategoryTheory.isIso_iff_bijective _).2
      (semiSkeletonStep_app_bijective_of_dim_neq i n m hmn)
  have hw := congrArg (fun f => f.app U) (semiSkeletonStep_square_commutes i n)
  exact IsPushout.of_horiz_isIso (CommSq.mk hw)

private theorem semiSkeletonStep_isPushout
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) (n : ℕ) :
    IsPushout (semiCellCoproductBoundaryMap i n)
      (semiCellCoproductAttachMap i n) (semiCellCoproductGeneratorMap i n)
      (semiSkeletonStep i n) := by
  apply IsPushout.of_forall_isPushout_app
  intro U
  cases U with
  | op a =>
    cases a with
    | mk b =>
      cases b with
      | mk m =>
        by_cases hmn : m < n
        · exact semiSkeletonStep_app_isPushout_of_dim_neq i n m (Or.inl hmn)
        · by_cases heq : m = n
          · subst m
            exact semiSkeletonStep_app_isPushout_of_dim_eq i n
          · have hgt : n < m := by omega
            exact semiSkeletonStep_app_isPushout_of_dim_neq i n m (Or.inr hgt)

private theorem semiSkeletonStep_realization_mono
    {X : HomotopyHypothesis.Henry.SemiSSet.{u}} (Y : Subfunctor X) (n : ℕ) :
    Mono (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
      (semiSkeletonStep Y.ι n)) := by
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  have hboundaryMono : Mono (R.map (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι) :=
    HomotopyHypothesis.Simplicial.CycleRealization.realization_boundary_mono n
  have htop : Mono (R.map (semiCellCoproductBoundaryMap Y.ι n)) := by
    simpa [semiCellCoproductBoundaryMap] using
      semiRealization_sigma_map_mono
        (fun _ : semiSimplexCell Y.ι n =>
          (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι)
        (fun _ => hboundaryMono)
  have hpush : IsPushout
      (R.map (semiCellCoproductBoundaryMap Y.ι n))
      (R.map (semiCellCoproductAttachMap Y.ι n))
      (R.map (semiCellCoproductGeneratorMap Y.ι n))
      (R.map (semiSkeletonStep Y.ι n)) :=
    Functor.map_isPushout R (semiSkeletonStep_isPushout Y.ι n)
  exact pushout_mono_of_mono hpush

private theorem semiSkeleton_le_of_le
    {X : HomotopyHypothesis.Henry.SemiSSet.{u}} {n m : ℕ} (hnm : n ≤ m) :
    semiSkeleton X n ≤ semiSkeleton X m := by
  intro U x hx
  change x ∈ (if U.unop.obj.len < n then Set.univ else ∅) at hx
  change x ∈ (if U.unop.obj.len < m then Set.univ else ∅)
  by_cases h : U.unop.obj.len < n
  · have hm : U.unop.obj.len < m := lt_of_lt_of_le h hnm
    simp [h, hm]
  · simp [h] at hx

private theorem semiSkeletonOfMono_le
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X)
    {n m : ℕ} (hnm : n ≤ m) : semiSkeletonOfMono i n ≤ semiSkeletonOfMono i m := by
  intro U x hx
  simp only [semiSkeletonOfMono, Subfunctor.max_obj, Set.mem_union] at hx ⊢
  rcases hx with hrange | hskeleton
  · exact Or.inl hrange
  · exact Or.inr (semiSkeleton_le_of_le hnm U hskeleton)

private def semiSkeletonFiltration
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) :
    ℕ ⥤ HomotopyHypothesis.Henry.SemiSSet.{u} where
  obj n := (semiSkeletonOfMono i n).toFunctor
  map {n m} f := Subfunctor.homOfLe (semiSkeletonOfMono_le i f.le)
  map_id n := by
    ext U x
    apply Subtype.ext
    rfl
  map_comp f g := by
    ext U x
    apply Subtype.ext
    rfl

private noncomputable def semiSkeletonFiltrationCocone
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) :
    Cocone (semiSkeletonFiltration i) where
  pt := X
  ι := {
    app n := (semiSkeletonOfMono i n).ι
    naturality := by
      intro n m f
      simp [semiSkeletonFiltration] }

private noncomputable def semiSkeletonFiltration_isColimit
    {A X : HomotopyHypothesis.Henry.SemiSSet.{u}} (i : A ⟶ X) :
    IsColimit (semiSkeletonFiltrationCocone i) := by
  refine evaluationJointlyReflectsColimits (semiSkeletonFiltrationCocone i) ?_
  intro U
  let F := semiSkeletonFiltration i ⋙ (evaluation _ _).obj U
  let c := ((evaluation _ _).obj U).mapCocone (semiSkeletonFiltrationCocone i)
  change IsColimit c
  refine Types.FilteredColimit.isColimitOf' (F := F) c ?_ ?_
  · intro x
    let n := U.unop.obj.len + 1
    refine ⟨n, ⟨x, ?_⟩, ?_⟩
    · change x ∈ Set.range (i.app U) ∪
        (if U.unop.obj.len < n then Set.univ else ∅)
      right
      have hn : U.unop.obj.len < n := by simp [n]
      rw [if_pos hn]
      exact Set.mem_univ _
    · rfl
  · intro n x y hxy
    refine ⟨n, 𝟙 n, ?_⟩
    apply Subtype.ext
    change x.1 = y.1 at hxy
    simpa [semiSkeletonFiltration] using hxy

private noncomputable def semiSkeletonFiltrationTFC
    {X : HomotopyHypothesis.Henry.SemiSSet.{u}} (Y : Subfunctor X) :
    CategoryTheory.TransfiniteCompositionOfShape ℕ Y.ι := by
  have h0 : semiSkeletonOfMono Y.ι 0 = Y := by
    ext U x
    simp [semiSkeletonOfMono, semiSkeleton, Subfunctor.range_ι]
  let hIso : (semiSkeletonOfMono Y.ι 0).toFunctor ≅ Y.toFunctor := {
    hom := Subfunctor.homOfLe h0.le
    inv := Subfunctor.homOfLe h0.symm.le
    hom_inv_id := by
      ext U x
      apply Subtype.ext
      rfl
    inv_hom_id := by
      ext U x
      apply Subtype.ext
      rfl }
  refine {
    F := semiSkeletonFiltration Y.ι
    isoBot := by simpa [semiSkeletonFiltration] using hIso
    incl := (semiSkeletonFiltrationCocone Y.ι).ι
    isColimit := semiSkeletonFiltration_isColimit Y.ι
    fac := ?_ }
  simpa [hIso, semiSkeletonFiltration, semiSkeletonFiltrationCocone] using
    (Subfunctor.homOfLe_ι h0.symm.le)

theorem realization_map_subfunctor_injective
    (X : HomotopyHypothesis.Henry.SemiSSet.{u}) (Y : Subfunctor X) :
    Function.Injective (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map Y.ι).hom := by
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  let c₀ := semiSkeletonFiltrationTFC Y
  let c := c₀.map R
  have hstep : ∀ j : ℕ, ¬ IsMax j →
      Mono (c.F.map (homOfLE (Order.le_succ j))) := by
    intro j hj
    have hmap : c₀.F.map (homOfLE (Order.le_succ j)) = semiSkeletonStep Y.ι j := by
      dsimp [c₀, semiSkeletonFiltrationTFC, semiSkeletonFiltration]
      ext U x
      apply Subtype.ext
      rfl
    change Mono (R.map (c₀.F.map (homOfLE (Order.le_succ j))))
    rw [hmap]
    exact semiSkeletonStep_realization_mono Y j
  have hincl : Mono (c.incl.app ⊥) :=
    (transfiniteComposition_stage_monomorphisms_of_mono
      (J := ℕ) (f := R.map Y.ι) c hstep) ⊥
  have hmap : Mono (R.map Y.ι) := by
    have hcomp : Mono (c.isoBot.inv ≫ c.incl.app ⊥) := by infer_instance
    rw [c.fac] at hcomp
    exact hcomp
  exact (TopCat.mono_iff_injective (R.map Y.ι)).mp hmap

noncomputable def semiRealizationStdSimplexIso :
    HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u} ⋙
      HomotopyHypothesis.Henry.SemiSSet.realization.{u} ≅
    HomotopyHypothesis.Henry.SemiSSet.toTop.{u} :=
  Presheaf.isExtensionAlongULiftYoneda.{u}
    HomotopyHypothesis.Henry.SemiSSet.toTop.{u}

noncomputable def semiRealizationStdSimplexHomeomorph (n : ℕ) :
    HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
        (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) ≃ₜ
      ULift (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  TopCat.homeoOfIso (semiRealizationStdSimplexIso.app
    (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))

theorem realization_boundary_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding
      (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
        (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι).hom := by
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  let f := R.map (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι
  have hinj : Function.Injective f.hom :=
    HomotopyHypothesis.Simplicial.CycleRealization.realization_boundary_injective n
  letI : CompactSpace (R.obj (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).toFunctor) :=
    HomotopyHypothesis.Realization.Boundary.compactSpace_realization_boundary n
  letI : T2Space (Convexity.StdSimplex ℝ (Fin (n + 1))) := by
    exact (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
      (Fin (n + 1))).t2Space
  letI : T2Space (ULift (Convexity.StdSimplex ℝ (Fin (n + 1)))) := inferInstance
  letI : T2Space (R.obj (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) :=
    (semiRealizationStdSimplexHomeomorph n).symm.t2Space
  have hClosedMap : IsClosedMap f.hom := by
    intro S hS
    have hcompact : IsCompact S :=
      (isCompact_univ : IsCompact (Set.univ : Set
        (R.obj (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).toFunctor))).of_isClosed_subset
          hS (Set.subset_univ _)
    exact (hcompact.image f.hom.continuous).isClosed
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap
    f.hom.continuous hinj hClosedMap

private theorem semiRealization_stdSimplex_t1 (n : ℕ) :
    T1Space (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) := by
  letI : T2Space (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
      (Fin (n + 1))).t2Space
  letI : T1Space (ULift (Convexity.StdSimplex ℝ (Fin (n + 1)))) := inferInstance
  exact (semiRealizationStdSimplexHomeomorph n).symm.t1Space

private theorem semiRealization_coproduct_t1 {I : Type u}
    (A : I → HomotopyHypothesis.Henry.SemiSSet.{u})
    (hA : ∀ i, T1Space
      (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj (A i))) :
    T1Space (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj (∐ A)) := by
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  let B : I → TopCat.{u} := fun i => R.obj (A i)
  letI : T1Space (TopCat.of (Σ i, (B i : Type u))) := topCat_sigma_t1Space B hA
  let hcol := isColimitOfHasCoproductOfPreservesColimit R A
  let e := hcol.coconePointUniqueUpToIso (coproductIsCoproduct B)
  let eSigma := TopCat.sigmaIsoSigma B
  exact (TopCat.homeoOfIso (e.trans eSigma)).symm.t1Space

private noncomputable def semiRealization_coproduct_sigmaIso {I : Type u}
    (A : I → HomotopyHypothesis.Henry.SemiSSet.{u}) :
    HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj (∐ A) ≅
      TopCat.of (Σ i, (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
        (A i) : Type u)) := by
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  let hcol := isColimitOfHasCoproductOfPreservesColimit R A
  exact (hcol.coconePointUniqueUpToIso (coproductIsCoproduct
    (fun i => R.obj (A i)))).trans (TopCat.sigmaIsoSigma
      (fun i => R.obj (A i)))

private theorem semiRealization_coproduct_sigmaIso_ι {I : Type u}
    (A : I → HomotopyHypothesis.Henry.SemiSSet.{u}) (i : I) :
    HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map (Sigma.ι A i) ≫
      (semiRealization_coproduct_sigmaIso A).hom =
      TopCat.sigmaι (fun i => HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
        (A i)) i := by
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  let hcol := isColimitOfHasCoproductOfPreservesColimit R A
  let hc := coproductIsCoproduct (fun i => R.obj (A i))
  let e₀ := hcol.coconePointUniqueUpToIso hc
  have h₁ : R.map (Sigma.ι A i) ≫ e₀.hom =
      Sigma.ι (fun i => R.obj (A i)) i := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom hcol hc (Discrete.mk i)
  change R.map (Sigma.ι A i) ≫ e₀.hom ≫
      (TopCat.sigmaIsoSigma (fun i => R.obj (A i))).hom = _
  calc
    _ = (R.map (Sigma.ι A i) ≫ e₀.hom) ≫
        (TopCat.sigmaIsoSigma (fun i => R.obj (A i))).hom :=
      (Category.assoc _ _ _).symm
    _ = Sigma.ι (fun i => R.obj (A i)) i ≫
        (TopCat.sigmaIsoSigma (fun i => R.obj (A i))).hom :=
      congrArg (fun q => q ≫ (TopCat.sigmaIsoSigma
        (fun i => R.obj (A i))).hom) h₁
    _ = _ := TopCat.sigmaIsoSigma_hom_ι (fun i => R.obj (A i)) i

theorem realization_semiSkeletonOfMono_t1
    (X : HomotopyHypothesis.Henry.SemiSSet.{u}) (n : ℕ) :
    T1Space (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
      (semiSkeletonOfMono ((⊥ : Subfunctor X).ι) n).toFunctor) := by
  let Y : Subfunctor X := ⊥
  let i : Y.toFunctor ⟶ X := Y.ι
  have hbase : semiSkeletonOfMono i 0 = Y := by
    change Subfunctor.range i ⊔ semiSkeleton X 0 = Y
    have hrange : Subfunctor.range i = Y := by simpa [i] using Subfunctor.range_ι Y
    have hsk : semiSkeleton X 0 = ⊥ := by
      ext U x
      simp [semiSkeleton]
    rw [hrange, hsk]
    simp
  have hYinit : IsInitial Y.toFunctor := by
    apply CategoryTheory.Functor.isInitial
    intro U
    have hEmpty : IsEmpty (Y.toFunctor.obj U) := by
      change IsEmpty {x : X.obj U // x ∈ Y.obj U}
      have hobj : Y.obj U = ∅ := by simp [Y]
      rw [hobj]
      exact Set.isEmpty_coe_sort.mpr rfl
    exact Classical.choice (Types.initial_iff_empty _ |>.2 hEmpty)
  have hRinit : IsInitial (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj Y.toFunctor) :=
    hYinit.isInitialObj HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  letI : T1Space (⊥_ TopCat.{u}) := by
    have hEmpty : IsEmpty ((⊥_ TopCat.{u}) : Type u) := by
      refine ⟨fun x => ?_⟩
      rcases (TopCat.homeoOfIso TopCat.initialIsoPEmpty) x with ⟨z⟩
    refine ⟨fun x => ?_⟩
    exact (hEmpty.false x).elim
  let eY : (⊥_ TopCat.{u}) ≅
      HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj Y.toFunctor :=
    initialIsInitial.uniqueUpToIso hRinit
  have hbaseT1 : T1Space (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
      (semiSkeletonOfMono i 0).toFunctor) := by
    rw [hbase]
    exact (TopCat.homeoOfIso eY).t1Space
  induction n with
  | zero => exact hbaseT1
  | succ n ih =>
      let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
      have htop : IsClosedEmbedding (R.map (semiCellCoproductBoundaryMap i n)).hom := by
        simpa [semiCellCoproductBoundaryMap] using
          semiRealization_sigma_map_closedEmbedding
            (fun _ : semiSimplexCell i n =>
              (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι)
            (fun _ => realization_boundary_isClosedEmbedding n)
      have hpush : IsPushout
          (R.map (semiCellCoproductBoundaryMap i n))
          (R.map (semiCellCoproductAttachMap i n))
          (R.map (semiCellCoproductGeneratorMap i n))
          (R.map (semiSkeletonStep i n)) :=
        Functor.map_isPushout R (semiSkeletonStep_isPushout i n)
      letI : T1Space (R.obj (semiCellSimplexCoproduct i n)) :=
        semiRealization_coproduct_t1
          (fun _ : semiSimplexCell i n =>
            HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
              (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
          (fun _ => semiRealization_stdSimplex_t1 n)
      letI : T1Space (R.obj (semiSkeletonOfMono i n).toFunctor) := ih
      exact pushout_t1Space hpush htop

theorem realization_semiSkeletonStep_isClosedEmbedding
    {X : HomotopyHypothesis.Henry.SemiSSet.{u}} (Y : Subfunctor X) (n : ℕ) :
    IsClosedEmbedding
      (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
        (semiSkeletonStep Y.ι n)).hom := by
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  have htop : IsClosedEmbedding (R.map (semiCellCoproductBoundaryMap Y.ι n)).hom := by
    simpa [semiCellCoproductBoundaryMap] using
      semiRealization_sigma_map_closedEmbedding
        (fun _ : semiSimplexCell Y.ι n =>
          (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι)
        (fun _ => realization_boundary_isClosedEmbedding n)
  have hpush : IsPushout
      (R.map (semiCellCoproductBoundaryMap Y.ι n))
      (R.map (semiCellCoproductAttachMap Y.ι n))
      (R.map (semiCellCoproductGeneratorMap Y.ι n))
      (R.map (semiSkeletonStep Y.ι n)) :=
    Functor.map_isPushout R (semiSkeletonStep_isPushout Y.ι n)
  exact pushout_isClosedEmbedding hpush htop

private noncomputable def semiRealizationCellCoproductInclusion
    {X : HomotopyHypothesis.Henry.SemiSSet.{u}} (Y : Subfunctor X) (n : ℕ) :
    TopCat.of (Σ x : semiSimplexCell Y.ι n,
      (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
        (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) : Type u)) ⟶
      HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
        (semiSkeletonOfMono Y.ι (n + 1)).toFunctor :=
  (semiRealization_coproduct_sigmaIso
    (fun _ : semiSimplexCell Y.ι n =>
      HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))).inv ≫
    HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
      (semiCellCoproductGeneratorMap Y.ι n)

private theorem semiRealizationCellCoproductInclusion_ι
    {X : HomotopyHypothesis.Henry.SemiSSet.{u}} (Y : Subfunctor X) (n : ℕ)
    (x : semiSimplexCell Y.ι n) :
    TopCat.sigmaι
        (fun _ : semiSimplexCell Y.ι n =>
          HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
            (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
              (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) x ≫
      semiRealizationCellCoproductInclusion Y n =
    HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
      (Subfunctor.lift (semiSimplexMap X n x.1)
        (semiSimplex_range_le_stage Y.ι n x)) := by
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  let B : semiSimplexCell Y.ι n → HomotopyHypothesis.Henry.SemiSSet.{u} :=
    fun _ => HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
  let eB := semiRealization_coproduct_sigmaIso B
  have hBι : R.map (Sigma.ι B x) ≫ eB.hom =
      TopCat.sigmaι (fun x => R.obj (B x)) x :=
    semiRealization_coproduct_sigmaIso_ι B x
  have hSigInv : TopCat.sigmaι (fun x => R.obj (B x)) x ≫ eB.inv =
      R.map (Sigma.ι B x) := by
    calc
      _ = (R.map (Sigma.ι B x) ≫ eB.hom) ≫ eB.inv := by rw [hBι]
      _ = _ := by simp [Category.assoc]
  change TopCat.sigmaι (fun x => R.obj (B x)) x ≫
      (eB.inv ≫ R.map (semiCellCoproductGeneratorMap Y.ι n)) = _
  calc
    _ = R.map (Sigma.ι B x) ≫ R.map (semiCellCoproductGeneratorMap Y.ι n) := by
      rw [← Category.assoc, hSigInv]
    _ = R.map (Sigma.ι B x ≫ semiCellCoproductGeneratorMap Y.ι n) := by
      rw [← R.map_comp]
    _ = R.map (Subfunctor.lift (semiSimplexMap X n x.1)
        (semiSimplex_range_le_stage Y.ι n x)) := by
      rw [semiCellCoproductGeneratorMap_ι]

/-- Compact maps into one realized skeletal attachment meet only finitely many new simplex
interiors. -/
theorem compact_map_hits_finitely_many_realized_cells
    {X : HomotopyHypothesis.Henry.SemiSSet.{u}} (Y : Subfunctor X) (n : ℕ)
    {K : TopCat.{u}} [CompactSpace K]
    (g : K ⟶ HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
      (semiSkeletonOfMono Y.ι (n + 1)).toFunctor) :
    (Finite {x : semiSimplexCell Y.ι n //
      ∃ k : K, ∃ z : HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
          (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
            (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)),
        z ∉ Set.range (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
          (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι).hom ∧
        (semiRealizationCellCoproductInclusion Y n).hom ⟨x, z⟩ = g.hom k}) ∧
      ∀ k : K,
        g.hom k ∈ Set.range
            (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
              (semiSkeletonStep Y.ι n)).hom ∨
          ∃ x : semiSimplexCell Y.ι n,
            ∃ z : HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
              (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
                (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)),
              z ∉ Set.range (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
                (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι).hom ∧
              (semiRealizationCellCoproductInclusion Y n).hom ⟨x, z⟩ = g.hom k := by
  classical
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  let Cell := semiSimplexCell Y.ι n
  let A : Cell → HomotopyHypothesis.Henry.SemiSSet.{u} :=
    fun _ => (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).toFunctor
  let B : Cell → HomotopyHypothesis.Henry.SemiSSet.{u} :=
    fun _ => HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
  let D : Cell → TopCat.{u} := fun x => R.obj (B x)
  let bnd : R.obj ((HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).toFunctor) ⟶
      R.obj (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) :=
    R.map (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι
  let eA := semiRealization_coproduct_sigmaIso A
  let eB := semiRealization_coproduct_sigmaIso B
  let fSig : TopCat.of (Σ x : Cell, (R.obj (A x) : Type u)) ⟶
      TopCat.of (Σ x : Cell, (R.obj (B x) : Type u)) :=
    TopCat.ofHom ⟨Sigma.map (fun x : Cell => x) (fun _ => bnd.hom),
      continuous_sigma_map.2 (fun _ => bnd.hom.continuous)⟩
  let f₀ := R.map (semiCellCoproductBoundaryMap Y.ι n)
  let g₀ := R.map (semiCellCoproductAttachMap Y.ι n)
  let i₀ := R.map (semiCellCoproductGeneratorMap Y.ι n)
  let j₀ := R.map (semiSkeletonStep Y.ι n)
  let gSig := eA.inv ≫ g₀
  let iSig := eB.inv ≫ i₀
  have hAι (x : Cell) :
      R.map (Sigma.ι A x) ≫ eA.hom =
        TopCat.sigmaι (fun x => R.obj (A x)) x :=
    semiRealization_coproduct_sigmaIso_ι A x
  have hBι (x : Cell) :
      R.map (Sigma.ι B x) ≫ eB.hom =
        TopCat.sigmaι (fun x => R.obj (B x)) x :=
    semiRealization_coproduct_sigmaIso_ι B x
  have hSigι (x : Cell) :
      TopCat.sigmaι (fun x => R.obj (A x)) x ≫ fSig =
        bnd ≫ TopCat.sigmaι (fun x => R.obj (B x)) x := by
    apply TopCat.hom_ext
    ext z
    · rfl
    · exact HEq.rfl
  have hcomm : f₀ ≫ eB.hom = eA.hom ≫ fSig := by
    let hcolA := isColimitOfHasCoproductOfPreservesColimit R A
    apply hcolA.hom_ext
    intro x
    let x₀ := x.as
    have hfac : Sigma.ι A x₀ ≫ semiCellCoproductBoundaryMap Y.ι n =
        (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι ≫ Sigma.ι B x₀ := by
      exact Sigma.ι_map
        (fun _ => (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι) x₀
    calc
      R.map (Sigma.ι A x₀) ≫ f₀ ≫ eB.hom =
          (R.map (Sigma.ι A x₀) ≫ f₀) ≫ eB.hom := by rw [Category.assoc]
      _ = R.map (Sigma.ι A x₀ ≫ semiCellCoproductBoundaryMap Y.ι n) ≫ eB.hom := by
        rw [← R.map_comp]
      _ = R.map ((HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι ≫
          Sigma.ι B x₀) ≫ eB.hom := by rw [hfac]
      _ = bnd ≫ R.map (Sigma.ι B x₀) ≫ eB.hom := by
        rw [R.map_comp]
        rfl
      _ = bnd ≫ TopCat.sigmaι (fun x => R.obj (B x)) x₀ := by rw [hBι]
      _ = TopCat.sigmaι (fun x => R.obj (A x)) x₀ ≫ fSig := hSigι x₀
      _ = R.map (Sigma.ι A x₀) ≫ eA.hom ≫ fSig := by
        exact (congrArg (fun q => q ≫ fSig) (hAι x₀)).symm
  have hOld : IsPushout f₀ g₀ i₀ j₀ :=
    Functor.map_isPushout R (semiSkeletonStep_isPushout Y.ι n)
  have hNew : IsPushout fSig gSig iSig j₀ :=
    hOld.of_iso eA eB (Iso.refl _) (Iso.refl _)
      hcomm (by simp [gSig]) (by simp [iSig]) (by simp)
  have hf : IsClosedEmbedding fSig.hom :=
    sigma_map_isClosedEmbedding (fun _ => bnd.hom)
      (fun _ => realization_boundary_isClosedEmbedding n)
  let Hit : Type u := {x : Cell //
    ∃ k : K, ∃ z : R.obj
        (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)),
      z ∉ Set.range bnd.hom ∧
        iSig.hom (⟨x, z⟩ : Σ x : Cell, (R.obj (B x) : Type u)) = g.hom k}
  let chosenPoint (x : Hit) : R.obj (B x.1) :=
    Classical.choose (Classical.choose_spec x.2)
  have hchosen (x : Hit) :
      chosenPoint x ∉ Set.range bnd.hom ∧
        iSig.hom (⟨x.1, chosenPoint x⟩ : Σ y : Cell, (R.obj (B y) : Type u)) =
          g.hom (Classical.choose x.2) :=
    Classical.choose_spec (Classical.choose_spec x.2)
  let p : Hit → Σ x : Cell, (D x : Type u) :=
    fun x => ⟨x.1, chosenPoint x⟩
  have hp : Function.Injective (fun x : Hit => (p x).1) := by
    intro x y hxy
    exact Subtype.ext hxy
  have hAway : ∀ x : Hit, p x ∉ Set.range fSig.hom := by
    intro x
    rintro ⟨a, ha⟩
    change (⟨a.1, bnd.hom a.2⟩ :
      Σ y : Cell, (R.obj (B y) : Type u)) = ⟨x.1, chosenPoint x⟩ at ha
    have hparts := Sigma.mk.inj_iff.mp ha
    have hval : bnd.hom a.2 = chosenPoint x := by
      exact eq_of_heq (by simpa [B] using hparts.2)
    exact hchosen x |>.1 ⟨a.2, hval⟩
  have hHit : ∀ x : Hit, iSig.hom (p x) ∈ Set.range g.hom := by
    intro x
    exact ⟨Classical.choose x.2, (hchosen x).2.symm⟩
  have hT1 : ∀ x : Cell, T1Space (D x) := fun _ => semiRealization_stdSimplex_t1 n
  have hfinite := compact_map_meets_finitely_many_pushoutSummands D hNew hf.injective
    p hp hT1 hAway g hHit
  refine ⟨hfinite, ?_⟩
  let c : PushoutCocone fSig gSig := PushoutCocone.mk iSig j₀ hNew.w
  let cT := (forget TopCat).mapCocone c
  have hcT : IsColimit cT := isColimitOfPreserves (forget TopCat) hNew.isColimit
  have hzero : cT.ι.app WalkingSpan.zero =
      (forget TopCat).map (gSig ≫ j₀) := by
    change (forget TopCat).map (fSig ≫ iSig) =
      (forget TopCat).map (gSig ≫ j₀)
    rw [hNew.w]
  intro k
  obtain ⟨w, z, hz⟩ :=
    CategoryTheory.Limits.Types.jointly_surjective_of_isColimit hcT (g.hom k)
  cases w with
  | none =>
      rw [hzero] at hz
      exact Or.inl ⟨gSig.hom z, hz⟩
  | some o =>
      cases o with
      | right =>
          change j₀.hom z = g.hom k at hz
          exact Or.inl ⟨z, hz⟩
      | left =>
          change iSig.hom z = g.hom k at hz
          rcases z with ⟨x, z⟩
          by_cases hzbd : z ∈ Set.range bnd.hom
          · obtain ⟨a, rfl⟩ := hzbd
            have hsq := congrArg
              (fun q : _ => q.hom (⟨x, a⟩ : Σ y : Cell, (R.obj (A y) : Type u)))
              hNew.w
            have hcell : iSig.hom
                (⟨x, bnd.hom a⟩ : Σ y : Cell, (R.obj (B y) : Type u)) =
                j₀.hom (gSig.hom ⟨x, a⟩) := by
              calc
                iSig.hom ⟨x, bnd.hom a⟩ =
                    iSig.hom (fSig.hom ⟨x, a⟩) := by rfl
                _ = j₀.hom (gSig.hom ⟨x, a⟩) := hsq
            exact Or.inl ⟨gSig.hom ⟨x, a⟩, hcell.symm.trans hz⟩
          · exact Or.inr ⟨x, z, hzbd, by
              simpa [semiRealizationCellCoproductInclusion, iSig, B] using hz⟩

private theorem realization_map_subfunctor_isClosedEmbedding_aux
    (X : HomotopyHypothesis.Henry.SemiSSet.{u}) (Y : Subfunctor X) :
    IsClosedEmbedding
      (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map Y.ι).hom := by
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  let c₀ := semiSkeletonFiltrationTFC Y
  let c := c₀.map R
  have hstepClosed (n : ℕ) : IsClosedEmbedding
      (c.F.map (homOfLE (Nat.le_succ n))).hom := by
    have hmap : c₀.F.map (homOfLE (Nat.le_succ n)) = semiSkeletonStep Y.ι n := by
      dsimp [c₀, semiSkeletonFiltrationTFC, semiSkeletonFiltration]
      ext U x
      apply Subtype.ext
      rfl
    change IsClosedEmbedding (R.map (c₀.F.map (homOfLE (Nat.le_succ n)))).hom
    rw [hmap]
    exact realization_semiSkeletonStep_isClosedEmbedding Y n
  have hstepMono : ∀ n : ℕ, Mono (c.F.map (homOfLE (Nat.le_succ n))) := by
    intro n
    exact (TopCat.mono_iff_injective _).2 (hstepClosed n).injective
  have hstageMono :=
    transfiniteComposition_stage_monomorphisms_of_mono (J := ℕ) c
      (fun n _ => hstepMono n)
  have hinj (n : ℕ) : Function.Injective (c.incl.app n).hom :=
    (TopCat.mono_iff_injective (c.incl.app n)).mp (hstageMono n)
  have hmapClosed {m n : ℕ} (f : m ⟶ n) : IsClosedEmbedding (c.F.map f).hom :=
    sequential_map_closedEmbedding hstepClosed f
  have hEmb := sequential_colimit_stage_closedEmbedding c.isColimit hmapClosed hinj
  have hIso : IsClosedEmbedding c.isoBot.inv.hom :=
    (TopCat.homeoOfIso c.isoBot).symm.isClosedEmbedding
  have hcomp : IsClosedEmbedding (c.isoBot.inv ≫ c.incl.app ⊥).hom :=
    (hEmb ⊥).comp hIso
  rw [c.fac] at hcomp
  exact hcomp

/-- A compact map into a finite-dimensional semi-simplicial realization factors through a finite
subfunctor. -/
theorem compact_map_factors_through_finite_subfunctor_skeletalStage
    (X : HomotopyHypothesis.Henry.SemiSSet.{u}) (n : ℕ)
    {K : TopCat.{u}} [CompactSpace K]
    (g : K ⟶ HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
      (semiSkeletonOfMono ((⊥ : Subfunctor X).ι) n).toFunctor) :
    ∃ Z : Subfunctor X,
      (∀ m : ℕ, (Z.obj
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))).Finite) ∧
      (∃ N : ℕ, ∀ m : ℕ, N < m →
        Z.obj (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) = ∅) ∧
      ∃ hZ : Z ≤ semiSkeletonOfMono ((⊥ : Subfunctor X).ι) n,
        ∃ g' : K ⟶ HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj Z.toFunctor,
          g' ≫ HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
            (Subfunctor.homOfLe hZ) = g := by
  classical
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  let i : (⊥ : Subfunctor X).toFunctor ⟶ X := (⊥ : Subfunctor X).ι
  induction n generalizing K with
  | zero =>
      let T0 := semiSkeletonOfMono i 0
      have hbase : T0 = ⊥ := by
        change Subfunctor.range i ⊔ semiSkeleton X 0 = ⊥
        have hrange : Subfunctor.range i = ⊥ := by
          simpa [i] using (Subfunctor.range_ι (⊥ : Subfunctor X))
        have hsk : semiSkeleton X 0 = ⊥ := by
          ext U x
          simp [semiSkeleton]
        rw [hrange, hsk]
        simp
      have hfin (m : ℕ) :
          (T0.obj (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))).Finite := by
        rw [hbase]
        simp
      have hbound :
          ∃ N : ℕ, ∀ m : ℕ, N < m →
            T0.obj (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) = ∅ := by
        refine ⟨0, fun m hm => ?_⟩
        rw [hbase]
        simp
      refine ⟨T0, hfin, hbound, le_rfl, g, ?_⟩
      have hId : Subfunctor.homOfLe (le_rfl : T0 ≤ T0) = 𝟙 T0.toFunctor := by
        ext U x
        rfl
      rw [hId]
      simp
  | succ n ih =>
      let Tn := semiSkeletonOfMono i n
      let Tsucc := semiSkeletonOfMono i (n + 1)
      have hTstep : Tn ≤ Tsucc := semiSkeletonOfMono_le i (Nat.le_succ n)
      let step : Tn.toFunctor ⟶ Tsucc.toFunctor := Subfunctor.homOfLe hTstep
      have hstepEq : step = semiSkeletonStep i n := by
        ext U x
        apply Subtype.ext
        rfl
      have hstepClosed : IsClosedEmbedding (R.map step).hom := by
        rw [hstepEq]
        exact realization_semiSkeletonStep_isClosedEmbedding (X := X) (Y := ⊥) n
      let Kold : Set K := g.hom ⁻¹' Set.range (R.map step).hom
      have hKoldClosed : IsClosed Kold :=
        (hstepClosed.isClosedMap.isClosed_range).preimage g.hom.continuous
      have hKoldCompact : IsCompact Kold :=
        isCompact_univ.of_isClosed_subset hKoldClosed (Set.subset_univ _)
      letI : CompactSpace Kold := isCompact_iff_compactSpace.mp hKoldCompact
      let eOld : R.obj Tn.toFunctor ≃ₜ Set.range (R.map step).hom :=
        hstepClosed.toIsEmbedding.toHomeomorph
      let gOld : TopCat.of Kold ⟶ R.obj Tn.toFunctor := TopCat.ofHom
        ⟨fun k => eOld.symm ⟨g.hom k.1, k.2⟩,
          eOld.continuous_symm.comp
            (Continuous.subtype_mk (g.hom.continuous.comp continuous_subtype_val)
              (fun k => k.2))⟩
      have hgOld (k : Kold) : (R.map step).hom (gOld.hom k) = g.hom k.1 := by
        have hx := eOld.apply_symm_apply ⟨g.hom k.1, k.2⟩
        exact congrArg Subtype.val hx
      obtain ⟨Zold, hfinOld, hboundOld, hZold, qOld, hqOld⟩ := ih gOld
      have hCells := compact_map_hits_finitely_many_realized_cells
        (X := X) (Y := ⊥) n g
      let Hit : Type u := {x : semiSimplexCell i n //
        ∃ k : K, ∃ z : R.obj
            (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
              (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)),
          z ∉ Set.range (R.map
            (HomotopyHypothesis.Henry.SemiSSet.boundary.{u} n).ι).hom ∧
          (semiRealizationCellCoproductInclusion (⊥ : Subfunctor X) n).hom
            ⟨x, z⟩ = g.hom k}
      have hHitFinite : Finite Hit := by
        simpa [Hit, i] using hCells.1
      letI : Finite Hit := hHitFinite
      letI : Fintype Hit := Fintype.ofFinite Hit
      let S : Finset (Σ m : ℕ, X.obj
          (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))) :=
        Finset.univ.image fun h : Hit => (⟨n, h.1.1⟩)
      obtain ⟨Znew, hfinNew, hboundNew, hgenNew, hleastNew⟩ :=
        finiteSubfunctor_generated_by_finset X S
      have hgenStage : ∀ a ∈ S, a.2 ∈ Tsucc.obj
          (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk a.1)) := by
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨h, -, hEq⟩
        rcases a with ⟨m, x⟩
        change (⟨n, h.1.1⟩ : Σ m : ℕ, X.obj
          (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))) =
          ⟨m, x⟩ at hEq
        have hparts := Sigma.mk.inj_iff.mp hEq
        have hm : n = m := hparts.1
        subst m
        have hx : h.1.1 = x := eq_of_heq hparts.2
        subst x
        simp [Tsucc, semiSkeletonOfMono, semiSkeleton]
      have hZnew : Znew ≤ Tsucc := hleastNew Tsucc hgenStage
      let Z : Subfunctor X := Zold ⊔ Znew
      have hZoldSucc : Zold ≤ Tsucc := le_trans hZold hTstep
      have hZ : Z ≤ Tsucc := sup_le hZoldSucc hZnew
      have hfin (m : ℕ) :
          (Z.obj (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))).Finite := by
        simp only [Z, Subfunctor.max_obj]
        exact (hfinOld m).union (hfinNew m)
      rcases hboundOld with ⟨Nold, hNold⟩
      rcases hboundNew with ⟨Nnew, hNnew⟩
      have hbound :
          ∃ N : ℕ, ∀ m : ℕ, N < m →
            Z.obj (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) = ∅ := by
        refine ⟨max Nold Nnew, fun m hm => ?_⟩
        have hmold : Nold < m := lt_of_le_of_lt (Nat.le_max_left _ _) hm
        have hmnew : Nnew < m := lt_of_le_of_lt (Nat.le_max_right _ _) hm
        simp only [Z, Subfunctor.max_obj]
        rw [hNold m hmold, hNnew m hmnew]
        simp
      let hZoldZ : Zold ≤ Z := le_sup_left
      have hZoldSucc' : Zold ≤ Tsucc := hZoldSucc
      have hroute : R.map (Subfunctor.homOfLe hZoldZ) ≫
          R.map (Subfunctor.homOfLe hZ) =
          R.map (Subfunctor.homOfLe hZoldSucc') := by
        rw [← R.map_comp]
        congr 1
      have hrouteOld : R.map (Subfunctor.homOfLe hZold) ≫ R.map step =
          R.map (Subfunctor.homOfLe hZoldSucc') := by
        rw [← R.map_comp]
        congr 1
      have hRange : Set.range g.hom ⊆ Set.range
          (R.map (Subfunctor.homOfLe hZ)).hom := by
        intro z hz
        rcases hz with ⟨k, rfl⟩
        by_cases hk : k ∈ Kold
        · let k₀ : Kold := ⟨k, hk⟩
          have hqEval :
              (R.map (Subfunctor.homOfLe hZold)).hom (qOld.hom k₀) =
                gOld.hom k₀ := by
            have := congrArg (fun q : TopCat.of Kold ⟶ R.obj Tn.toFunctor =>
              q.hom k₀) hqOld
            simpa using this
          refine ⟨(R.map (Subfunctor.homOfLe hZoldZ)).hom (qOld.hom k₀), ?_⟩
          calc
            (R.map (Subfunctor.homOfLe hZ)).hom
                ((R.map (Subfunctor.homOfLe hZoldZ)).hom (qOld.hom k₀)) =
              (R.map (Subfunctor.homOfLe hZoldSucc')).hom (qOld.hom k₀) := by
                have hroute' := congrArg (fun f => f.hom (qOld.hom k₀)) hroute
                simpa using hroute'
            _ = (R.map step).hom
                ((R.map (Subfunctor.homOfLe hZold)).hom (qOld.hom k₀)) := by
                  have hroute' := congrArg (fun f => f.hom (qOld.hom k₀)) hrouteOld
                  simpa using hroute'.symm
            _ = (R.map step).hom (gOld.hom k₀) := by rw [hqEval]
            _ = g.hom k := hgOld k₀
        · rcases (hCells.2 k) with hold | ⟨x, z', hz', hcell⟩
          · have hkold : k ∈ Kold := by
              change g.hom k ∈ Set.range (R.map step).hom
              rw [hstepEq]
              exact hold
            exact False.elim (hk hkold)
          · let hsel : Hit := ⟨x, ⟨k, z', hz', hcell⟩⟩
            have ha : (⟨n, x.1⟩ : Σ m : ℕ, X.obj
                (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))) ∈ S :=
              Finset.mem_image.mpr ⟨hsel, Finset.mem_univ _, rfl⟩
            have hxnew : x.1 ∈ Znew.obj
                (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) := hgenNew _ ha
            have hZnewZ : Znew ≤ Z := le_sup_right
            have hxZ : x.1 ∈ Z.obj
                (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) :=
              (hZnewZ _ hxnew)
            obtain ⟨fZ, hfactZ⟩ :=
              semiSimplexMap_factors_through_subfunctor Z n x.1 hxZ
            have hliftEq :
                fZ ≫ Subfunctor.homOfLe hZ =
                  Subfunctor.lift (semiSimplexMap X n x.1)
                    (semiSimplex_range_le_stage i n x) := by
              apply (cancel_mono Tsucc.ι).1
              rw [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.lift_ι]
              exact hfactZ
            have hcellEval :
                (semiRealizationCellCoproductInclusion (⊥ : Subfunctor X) n).hom
                    ⟨x, z'⟩ =
                  (R.map (Subfunctor.lift (semiSimplexMap X n x.1)
                    (semiSimplex_range_le_stage i n x))).hom z' := by
              have := congrArg (fun q => q.hom z')
                (semiRealizationCellCoproductInclusion_ι (⊥ : Subfunctor X) n x)
              simpa using this
            refine ⟨(R.map fZ).hom z', ?_⟩
            calc
              (R.map (Subfunctor.homOfLe hZ)).hom ((R.map fZ).hom z') =
                  (R.map (fZ ≫ Subfunctor.homOfLe hZ)).hom z' := by
                    simpa using congrArg (fun q => q.hom z')
                      (R.map_comp fZ (Subfunctor.homOfLe hZ))
              _ = (R.map (Subfunctor.lift (semiSimplexMap X n x.1)
                  (semiSimplex_range_le_stage i n x))).hom z' := by
                    rw [hliftEq]
              _ = (semiRealizationCellCoproductInclusion
                  (⊥ : Subfunctor X) n).hom ⟨x, z'⟩ := hcellEval.symm
              _ = g.hom k := hcell
      let gX := g ≫ R.map Tsucc.ι
      have hZinc : R.map (Subfunctor.homOfLe hZ) ≫ R.map Tsucc.ι =
          R.map Z.ι := by
        rw [← R.map_comp, Subfunctor.homOfLe_ι]
      have hRangeX : Set.range gX.hom ⊆ Set.range (R.map Z.ι).hom := by
        rintro y ⟨k, rfl⟩
        obtain ⟨w, hw⟩ := hRange ⟨k, rfl⟩
        refine ⟨w, ?_⟩
        calc
          (R.map Z.ι).hom w = (R.map Tsucc.ι).hom
              ((R.map (Subfunctor.homOfLe hZ)).hom w) := by
                have h := congrArg (fun q => q.hom w) hZinc
                simpa using h.symm
          _ = (R.map Tsucc.ι).hom (g.hom k) := by rw [hw]
          _ = gX.hom k := rfl
      obtain ⟨gZ, hgZ⟩ :=
        TopCat.factor_through_embedding_of_range_subset
          (realization_map_subfunctor_isClosedEmbedding_aux X Z).toIsEmbedding hRangeX
      have hmono : Mono (R.map Tsucc.ι) := by
        exact (TopCat.mono_iff_injective _).2 (realization_map_subfunctor_injective X Tsucc)
      have hcancel :
          (gZ ≫ R.map (Subfunctor.homOfLe hZ)) ≫ R.map Tsucc.ι =
            g ≫ R.map Tsucc.ι := by
        calc
          (gZ ≫ R.map (Subfunctor.homOfLe hZ)) ≫ R.map Tsucc.ι =
              gZ ≫ R.map Z.ι := by rw [Category.assoc, hZinc]
          _ = gX := hgZ
          _ = g ≫ R.map Tsucc.ι := rfl
      have hfactor : gZ ≫ R.map (Subfunctor.homOfLe hZ) = g :=
        (cancel_mono (R.map Tsucc.ι)).1 hcancel
      exact ⟨Z, hfin, hbound, hZ, gZ, hfactor⟩

theorem compact_map_factors_through_realized_skeletalStage
    (X : HomotopyHypothesis.Henry.SemiSSet.{u})
    {K : TopCat.{u}} [CompactSpace K]
    (g : K ⟶ HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj X) :
    ∃ n, ∃ g' : K ⟶ HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
        (semiSkeletonOfMono ((⊥ : Subfunctor X).ι) n).toFunctor,
      g' ≫ HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
        (semiSkeletonOfMono ((⊥ : Subfunctor X).ι) n).ι = g := by
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  let Y : Subfunctor X := ⊥
  let i : Y.toFunctor ⟶ X := Y.ι
  let c₀ := semiSkeletonFiltrationTFC Y
  let c := c₀.map R
  have hstepClosed (n : ℕ) : IsClosedEmbedding
      (c.F.map (homOfLE (Nat.le_succ n))).hom := by
    have hmap : c₀.F.map (homOfLE (Nat.le_succ n)) = semiSkeletonStep i n := by
      dsimp [c₀, semiSkeletonFiltrationTFC, semiSkeletonFiltration, Y]
      ext U x
      apply Subtype.ext
      rfl
    change IsClosedEmbedding (R.map (c₀.F.map (homOfLE (Nat.le_succ n)))).hom
    rw [hmap]
    exact realization_semiSkeletonStep_isClosedEmbedding (X := X) (Y := ⊥) n
  have hstepMono : ∀ n : ℕ, Mono (c.F.map (homOfLE (Nat.le_succ n))) := by
    intro n
    exact (TopCat.mono_iff_injective _).2 (hstepClosed n).injective
  have hstageMono :=
    transfiniteComposition_stage_monomorphisms_of_mono (J := ℕ) c
      (fun n _ => hstepMono n)
  have hinj (n : ℕ) : Function.Injective (c.incl.app n).hom :=
    (TopCat.mono_iff_injective (c.incl.app n)).mp (hstageMono n)
  have hmapClosed {m n : ℕ} (f : m ⟶ n) : IsClosedEmbedding (c.F.map f).hom :=
    sequential_map_closedEmbedding hstepClosed f
  have hEmb := sequential_colimit_stage_closedEmbedding c.isColimit hmapClosed hinj
  have hT1 (n : ℕ) : T1Space (c.F.obj n) := by
    change T1Space (R.obj (semiSkeletonOfMono i n).toFunctor)
    simpa [i, Y] using realization_semiSkeletonOfMono_t1 X n
  obtain ⟨n, g', hfac⟩ := compact_map_factors_through_stage c.isColimit g hT1
    (fun n => (hEmb n).toIsEmbedding)
  refine ⟨n, g', ?_⟩
  change g' ≫ R.map (semiSkeletonOfMono i n).ι = g
  simpa [Y, i, c, c₀, semiSkeletonFiltrationTFC, semiSkeletonFiltrationCocone,
    semiSkeletonFiltration] using hfac

theorem realization_map_subfunctor_isClosedEmbedding
    (X : HomotopyHypothesis.Henry.SemiSSet.{u}) (Y : Subfunctor X) :
    IsClosedEmbedding
      (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map Y.ι).hom := by
  let R := HomotopyHypothesis.Henry.SemiSSet.realization.{u}
  let c₀ := semiSkeletonFiltrationTFC Y
  let c := c₀.map R
  have hstepClosed (n : ℕ) : IsClosedEmbedding
      (c.F.map (homOfLE (Nat.le_succ n))).hom := by
    have hmap : c₀.F.map (homOfLE (Nat.le_succ n)) = semiSkeletonStep Y.ι n := by
      dsimp [c₀, semiSkeletonFiltrationTFC, semiSkeletonFiltration]
      ext U x
      apply Subtype.ext
      rfl
    change IsClosedEmbedding (R.map (c₀.F.map (homOfLE (Nat.le_succ n)))).hom
    rw [hmap]
    exact realization_semiSkeletonStep_isClosedEmbedding Y n
  have hstepMono : ∀ n : ℕ, Mono (c.F.map (homOfLE (Nat.le_succ n))) := by
    intro n
    exact (TopCat.mono_iff_injective _).2 (hstepClosed n).injective
  have hstageMono :=
    transfiniteComposition_stage_monomorphisms_of_mono (J := ℕ) c
      (fun n _ => hstepMono n)
  have hinj (n : ℕ) : Function.Injective (c.incl.app n).hom :=
    (TopCat.mono_iff_injective (c.incl.app n)).mp (hstageMono n)
  have hmapClosed {m n : ℕ} (f : m ⟶ n) : IsClosedEmbedding (c.F.map f).hom :=
    sequential_map_closedEmbedding hstepClosed f
  have hEmb := sequential_colimit_stage_closedEmbedding c.isColimit hmapClosed hinj
  have hIso : IsClosedEmbedding c.isoBot.inv.hom :=
    (TopCat.homeoOfIso c.isoBot).symm.isClosedEmbedding
  have hcomp : IsClosedEmbedding (c.isoBot.inv ≫ c.incl.app ⊥).hom :=
    (hEmb ⊥).comp hIso
  rw [c.fac] at hcomp
  exact hcomp

end HomotopyHypothesis.Approximation.FiniteSubcomplex

namespace HomotopyHypothesis.Henry.Packages

theorem realization_exists_finite_subcomplex_proof
    (X : HomotopyHypothesis.Henry.SemiSSet.{u}) :
    (∀ Y : Subfunctor X, Function.Injective
      (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map Y.ι).hom) ∧
    ∀ (K : TopCat.{u}) [CompactSpace K]
      (g : K ⟶ HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj X),
      ∃ Y : Subfunctor X,
        (∀ n : ℕ, (Y.obj
          (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))).Finite) ∧
        (∃ N : ℕ, ∀ n : ℕ, N < n →
          Y.obj (Opposite.op
            (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) = ∅) ∧
        ∃ g' : K ⟶ HomotopyHypothesis.Henry.SemiSSet.realization.{u}.obj
          Y.toFunctor,
          g' ≫ HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map Y.ι = g := by
  constructor
  · intro Y
    exact HomotopyHypothesis.Approximation.FiniteSubcomplex.realization_map_subfunctor_injective X Y
  · intro K hK g
    obtain ⟨n, gStage, hStage⟩ :=
      HomotopyHypothesis.Approximation.FiniteSubcomplex.compact_map_factors_through_realized_skeletalStage X g
    obtain ⟨Z, hfinite, hbounded, hZ, gZ, hfactor⟩ :=
      HomotopyHypothesis.Approximation.FiniteSubcomplex.compact_map_factors_through_finite_subfunctor_skeletalStage
        X n gStage
    let Tn := HomotopyHypothesis.Approximation.FiniteSubcomplex.semiSkeletonOfMono
      ((⊥ : Subfunctor X).ι) n
    have hcomp : HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
        (Subfunctor.homOfLe hZ) ≫
          HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map Tn.ι =
        HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map Z.ι := by
      rw [← Subfunctor.homOfLe_ι hZ, Functor.map_comp]
    have hfinal : gZ ≫
        HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map Z.ι = g := by
      calc
        gZ ≫ HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map Z.ι =
            gZ ≫ (HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
              (Subfunctor.homOfLe hZ) ≫
              HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map Tn.ι) := by
                rw [hcomp]
        _ = (gZ ≫ HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map
              (Subfunctor.homOfLe hZ)) ≫
              HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map Tn.ι := by
                rw [Category.assoc]
        _ = g := by rw [hfactor, hStage]
    exact ⟨Z, hfinite, hbounded, gZ, hfinal⟩

#print axioms realization_exists_finite_subcomplex_proof

end HomotopyHypothesis.Henry.Packages
