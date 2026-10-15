import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismRelative.BoundarySupport
import HomotopyHypothesis.Approximation.DerivedPrismRelative.CellAttachment
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism
/-!
# Relative stages of the derived cylinder

The derived end stays fixed while cylinders over simplices are attached.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismRelative

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological

noncomputable abbrev relativeStage {W : SemiSSet.{u}} (A : Subfunctor W) : SemiSSet.{u} :=
  pushout (sdLan.map A.ι) (sdLanToDprism.app A.toFunctor)

noncomputable def relativeStageMap {W : SemiSSet.{u}} {A B : Subfunctor W} (h : A ≤ B) :
    relativeStage A ⟶ relativeStage B :=
  pushout.desc (pushout.inl _ _)
    (dprismLan.map (Subfunctor.homOfLe h) ≫ pushout.inr _ _) (by
      calc
        sdLan.map A.ι ≫ pushout.inl _ _ =
            sdLan.map (Subfunctor.homOfLe h) ≫ sdLan.map B.ι ≫ pushout.inl _ _ := by
          rw [← Category.assoc, ← Functor.map_comp, Subfunctor.homOfLe_ι]
        _ = sdLan.map (Subfunctor.homOfLe h) ≫
            sdLanToDprism.app B.toFunctor ≫ pushout.inr _ _ := by
          rw [pushout.condition]
        _ = sdLanToDprism.app A.toFunctor ≫
            dprismLan.map (Subfunctor.homOfLe h) ≫ pushout.inr _ _ := by
          rw [← Category.assoc, sdLanToDprism.naturality, Category.assoc])

@[reassoc (attr := simp)]
theorem relativeStageMap_inl {W : SemiSSet.{u}} {A B : Subfunctor W} (h : A ≤ B) :
    pushout.inl _ _ ≫ relativeStageMap h =
      (pushout.inl _ _ : sdLan.obj W ⟶ relativeStage B) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem relativeStageMap_inr {W : SemiSSet.{u}} {A B : Subfunctor W} (h : A ≤ B) :
    pushout.inr _ _ ≫ relativeStageMap h =
      dprismLan.map (Subfunctor.homOfLe h) ≫
        (pushout.inr _ _ : dprismLan.obj B.toFunctor ⟶ relativeStage B) :=
  pushout.inr_desc _ _ _

noncomputable def relativeMap {K L : SemiSSet.{u}} (f : K ⟶ L) :
    pushout (sdLan.map f) (sdLanToDprism.app K) ⟶ dprismLan.obj L :=
  pushout.desc (sdLanToDprism.app L) (dprismLan.map f)
    (sdLanToDprism.naturality f)

section Attachment

variable {W K L : SemiSSet.{u}} {A B : Subfunctor W}
  (h : A ≤ B) (a : K ⟶ A.toFunctor) (f : K ⟶ L) (b : L ⟶ B.toFunctor)
  (sq : IsPushout a f (Subfunctor.homOfLe h) b)

include h sq in
private theorem attachment_to_ambient : a ≫ A.ι = f ≫ b ≫ B.ι := by
  rw [← Subfunctor.homOfLe_ι h, ← Category.assoc, sq.w, Category.assoc]

include h sq in
noncomputable def relativeCellToStage :
    pushout (sdLan.map f) (sdLanToDprism.app K) ⟶ relativeStage A :=
  pushout.desc (sdLan.map (b ≫ B.ι) ≫ pushout.inl _ _)
    (dprismLan.map a ≫ pushout.inr _ _) (by
      calc
        sdLan.map f ≫ (sdLan.map (b ≫ B.ι) ≫ pushout.inl _ _) =
            sdLan.map (a ≫ A.ι) ≫ pushout.inl _ _ := by
          rw [← Category.assoc, ← Functor.map_comp, ← attachment_to_ambient h a f b sq]
        _ = sdLan.map a ≫ (sdLan.map A.ι ≫ pushout.inl _ _) := by
          rw [Functor.map_comp, Category.assoc]
        _ = sdLan.map a ≫ (sdLanToDprism.app A.toFunctor ≫ pushout.inr _ _) := by
          rw [pushout.condition]
        _ = sdLanToDprism.app K ≫ (dprismLan.map a ≫ pushout.inr _ _) := by
          rw [← Category.assoc, sdLanToDprism.naturality, Category.assoc])

private theorem relativeCell_comm :
    relativeCellToStage h a f b sq ≫ relativeStageMap h =
      relativeMap f ≫ dprismLan.map b ≫ pushout.inr _ _ := by
  apply pushout.hom_ext
  · simp only [relativeCellToStage, pushout.inl_desc_assoc,
      relativeStageMap_inl, relativeMap, pushout.inl_desc_assoc, Category.assoc]
    rw [Functor.map_comp, Category.assoc, pushout.condition,
      ← Category.assoc, sdLanToDprism.naturality, Category.assoc]
  · simp only [relativeCellToStage, pushout.inr_desc_assoc,
      relativeStageMap_inr, relativeMap, pushout.inr_desc_assoc, Category.assoc]
    simp only [← Category.assoc]
    rw [← Functor.map_comp, sq.w, Functor.map_comp]

theorem relativeStageMap_isPushout :
    IsPushout (relativeCellToStage h a f b sq) (relativeMap f)
      (relativeStageMap h) (dprismLan.map b ≫ pushout.inr _ _) := by
  let fsq := sdLan_map_isPushout sq
  let gsq := dprismLan_map_isPushout sq
  let condition := relativeCell_comm h a f b sq
  let coc := PushoutCocone.mk (relativeStageMap h)
    (dprismLan.map b ≫ pushout.inr _ _) condition
  have compatibleG (s : PushoutCocone (relativeCellToStage h a f b sq) (relativeMap f)) :
      dprismLan.map a ≫ (pushout.inr _ _ ≫ s.inl) = dprismLan.map f ≫ s.inr := by
    have hc := congrArg (fun t => pushout.inr (sdLan.map f)
      (sdLanToDprism.app K) ≫ t) s.condition
    simpa only [relativeCellToStage, relativeMap, pushout.inr_desc_assoc,
      pushout.inr_desc, Category.assoc] using hc
  let dg := fun s : PushoutCocone (relativeCellToStage h a f b sq) (relativeMap f) =>
    gsq.desc (pushout.inr _ _ ≫ s.inl) s.inr (compatibleG s)
  have compatibleF (s : PushoutCocone (relativeCellToStage h a f b sq) (relativeMap f)) :
      sdLan.map B.ι ≫ (pushout.inl _ _ ≫ s.inl) =
        sdLanToDprism.app B.toFunctor ≫ dg s := by
    apply fsq.hom_ext
    · dsimp only [dg]
      rw [← Functor.map_comp_assoc, Subfunctor.homOfLe_ι,
        sdLanToDprism.naturality_assoc, gsq.inl_desc, pushout.condition_assoc]
    · have hc := congrArg (fun t => pushout.inl (sdLan.map f)
        (sdLanToDprism.app K) ≫ t) s.condition
      have hc' : sdLan.map (b ≫ B.ι) ≫ (pushout.inl _ _ ≫ s.inl) =
          sdLanToDprism.app L ≫ s.inr := by
        simpa only [relativeCellToStage, relativeMap, pushout.inl_desc_assoc,
          pushout.inl_desc, Category.assoc] using hc
      dsimp only [dg]
      rw [← Functor.map_comp_assoc,
        sdLanToDprism.naturality_assoc, gsq.inr_desc]
      exact hc'
  let desc := fun s : PushoutCocone (relativeCellToStage h a f b sq) (relativeMap f) =>
    pushout.desc (pushout.inl _ _ ≫ s.inl) (dg s) (compatibleF s)
  refine IsPushout.of_isColimit (c := coc)
    (PushoutCocone.IsColimit.mk condition desc ?_ ?_ ?_)
  · intro s
    apply pushout.hom_ext
    · simp [desc, pushout.inl_desc, pushout.inr_desc, Category.assoc]
    · simp [desc, dg, pushout.inl_desc, pushout.inr_desc, Category.assoc]
  · intro s
    simp [desc, dg, pushout.inl_desc, pushout.inr_desc, Category.assoc]
  · intro s m hm₁ hm₂
    apply pushout.hom_ext
    · have hm := congrArg (fun t => pushout.inl (sdLan.map A.ι)
        (sdLanToDprism.app A.toFunctor) ≫ t) hm₁
      simpa [desc, pushout.inl_desc, pushout.inr_desc, Category.assoc] using hm
    · dsimp only [desc]
      rw [pushout.inr_desc]
      apply gsq.hom_ext
      · have hm := congrArg (fun t => pushout.inr (sdLan.map A.ι)
          (sdLanToDprism.app A.toFunctor) ≫ t) hm₁
        simpa [dg, Category.assoc] using hm
      · simpa [dg, Category.assoc] using hm₂

end Attachment

#print axioms relativeStageMap_isPushout

end HomotopyHypothesis.Approximation.DerivedPrismRelative
