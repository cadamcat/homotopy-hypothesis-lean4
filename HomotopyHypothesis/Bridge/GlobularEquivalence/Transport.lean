import HomotopyHypothesis.Blueprint.Bridge.FaceOfOAI
import HomotopyHypothesis.Blueprint.Bridge.FaceToOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeOfOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeOfOAICompGlobeToOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeToOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeToOAICompGlobeOfOAI
import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge
noncomputable section

namespace HomotopyHypothesis.Bridge.GlobularEquivalence

open CategoryTheory CategoryTheory.Limits

universe u

def globeEquiv : HomotopyHypothesis.Grothendieck.Globe ≌ OAI.Grothendieck.Globe where
  functor := HomotopyHypothesis.Blueprint.globeToOAI
  inverse := HomotopyHypothesis.Blueprint.globeOfOAI
  unitIso := eqToIso HomotopyHypothesis.Blueprint.globeToOAI_comp_globeOfOAI.symm
  counitIso := eqToIso HomotopyHypothesis.Blueprint.globeOfOAI_comp_globeToOAI
  functor_unitIso_comp _ := by cat_disch

instance : Functor.IsEquivalence HomotopyHypothesis.Blueprint.globeToOAI.op :=
  (globeEquiv.op).isEquivalence_functor

noncomputable def globularPresheafEquiv :
    OAI.Grothendieck.GlobularPresheaf.{u} ≌
      HomotopyHypothesis.Grothendieck.GlobularPresheaf.{u} :=
  (globeEquiv.op).congrLeft.symm

noncomputable def globularPresheafEquivBack :
    HomotopyHypothesis.Grothendieck.GlobularPresheaf.{u} ≌
      OAI.Grothendieck.GlobularPresheaf.{u} := by
  exact globularPresheafEquiv.symm

abbrev globularPresheafReindex := globularPresheafEquiv.functor
abbrev globularPresheafReindexBack := globularPresheafEquiv.inverse

def faceEquiv {m n : ℕ} : OAI.Grothendieck.Globe.Face m n ≃
    HomotopyHypothesis.Grothendieck.Globe.Face m n where
  toFun f := HomotopyHypothesis.Blueprint.faceOfOAI f
  invFun f := HomotopyHypothesis.Blueprint.faceToOAI f
  left_inv f := by cases f <;> rfl
  right_inv f := by cases f <;> rfl

theorem faceEquiv_comp {m n k : ℕ} (f : OAI.Grothendieck.Globe.Face m n)
    (g : OAI.Grothendieck.Globe.Face n k) :
    faceEquiv (OAI.Grothendieck.Globe.Face.comp f g) =
      HomotopyHypothesis.Grothendieck.Globe.Face.comp (faceEquiv f) (faceEquiv g) := by
  cases f <;> cases g <;> rfl

theorem globeEquiv_map_faceEquiv {m n : ℕ} (f : OAI.Grothendieck.Globe.Face m n) :
    globeEquiv.functor.map (faceEquiv f) = f := by
  cases f <;> rfl

theorem faceEquiv_globeEquiv_map {m n : ℕ}
    (f : HomotopyHypothesis.Grothendieck.Globe.Face m n) :
    faceEquiv (globeEquiv.functor.map f) = f := by
  cases f <;> rfl

theorem faceEquiv_globeToOAI_map {m n : ℕ}
    (f : HomotopyHypothesis.Grothendieck.Globe.Face m n) :
    faceEquiv (HomotopyHypothesis.Blueprint.globeToOAI.map f) = f := by
  cases f <;> rfl

def homUpEquiv (X : HomotopyHypothesis.Grothendieck.Globe) (n : ℕ) :
    ULift.{u} (globeEquiv.functor.obj X ⟶
      globeEquiv.functor.obj (HomotopyHypothesis.Grothendieck.Globe.mk n)) ≃
      ULift.{u} (X ⟶ HomotopyHypothesis.Grothendieck.Globe.mk n) where
  toFun z := ULift.up (globeEquiv.functor.preimage z.down)
  invFun z := ULift.up (globeEquiv.functor.map z.down)
  left_inv z := by cases z <;> simp
  right_inv z := by cases z <;> simp

theorem homUpEquiv_precomp (X Y : HomotopyHypothesis.Grothendieck.Globe) {n : ℕ}
    (f : Y ⟶ X)
    (z : ULift.{u} (globeEquiv.functor.obj X ⟶
      globeEquiv.functor.obj (HomotopyHypothesis.Grothendieck.Globe.mk n))) :
    homUpEquiv Y n (ULift.up (globeEquiv.functor.map f ≫ z.down)) =
      ULift.up (f ≫ (homUpEquiv X n z).down) := by
  cases z with
  | up z =>
    apply ULift.ext
    simp [homUpEquiv, Functor.preimage_comp, Functor.preimage_map]

theorem homUpEquiv_postcomp (X : HomotopyHypothesis.Grothendieck.Globe) {m n : ℕ}
    (f : OAI.Grothendieck.Globe.Face m n)
    (z : ULift.{u} (globeEquiv.functor.obj X ⟶
      globeEquiv.functor.obj (HomotopyHypothesis.Grothendieck.Globe.mk m))) :
    homUpEquiv X n (ULift.up (z.down ≫ f)) =
      ULift.up ((homUpEquiv X m z).down ≫ faceEquiv f) := by
  cases z with
  | up z =>
    dsimp [homUpEquiv]
    let fHom : globeEquiv.functor.obj (HomotopyHypothesis.Grothendieck.Globe.mk m) ⟶
        globeEquiv.functor.obj (HomotopyHypothesis.Grothendieck.Globe.mk n) := f
    let fCopy : HomotopyHypothesis.Grothendieck.Globe.mk m ⟶
        HomotopyHypothesis.Grothendieck.Globe.mk n := faceEquiv f
    have hMap : globeEquiv.functor.map fCopy = fHom := by
      simpa [fCopy, fHom] using globeEquiv_map_faceEquiv f
    have hPre : globeEquiv.functor.preimage fHom = fCopy := by
      rw [← hMap]
      simp
    change ULift.up (globeEquiv.functor.preimage (z ≫ fHom)) =
      ULift.up (globeEquiv.functor.preimage z ≫ fCopy)
    apply congrArg ULift.up
    rw [Functor.preimage_comp, hPre]

noncomputable def diskIso (n : ℕ) :
    globularPresheafReindex.obj (OAI.Grothendieck.GlobularPresheaf.disk.{u} n) ≅
      HomotopyHypothesis.Grothendieck.GlobularPresheaf.disk.{u} n := by
  refine NatIso.ofComponents (fun X => Equiv.toIso (homUpEquiv X.unop n)) ?_
  intro X Y f
  ext z
  cases z with
  | up z =>
    dsimp [globularPresheafReindex, globularPresheafEquiv, globeEquiv, homUpEquiv,
      HomotopyHypothesis.Blueprint.globeToOAI,
      OAI.Grothendieck.GlobularPresheaf.disk,
      HomotopyHypothesis.Grothendieck.GlobularPresheaf.disk, Equiv.toIso, Equiv.trans,
      Equivalence.congrLeft, Equivalence.op, Functor.whiskeringLeft, Functor.op_map]
    change globeEquiv.functor.obj X.unop ⟶
      globeEquiv.functor.obj (HomotopyHypothesis.Grothendieck.Globe.mk n) at z
    let hF : Functor.FullyFaithful globeEquiv.functor :=
      Functor.FullyFaithful.ofFullyFaithful globeEquiv.functor
    change ULift.up (hF.preimage (globeEquiv.functor.map f.unop ≫ z)) =
      ULift.up (f.unop ≫ hF.preimage z)
    congr 1
    change globeEquiv.functor.preimage (globeEquiv.functor.map f.unop ≫ z) =
      f.unop ≫ globeEquiv.functor.preimage z
    apply hF.map_injective
    change globeEquiv.functor.map (hF.preimage (globeEquiv.functor.map f.unop ≫ z)) =
      globeEquiv.functor.map (f.unop ≫ hF.preimage z)
    simp [Functor.map_comp, hF.map_preimage]

def pushoutIsoOfIso {C : Type*} [Category C] {A B D A' B' D' : C}
    {f : A ⟶ B} {g : A ⟶ D} {f' : A' ⟶ B'} {g' : A' ⟶ D'}
    (iA : A ≅ A') (iB : B ≅ B') (iD : D ≅ D')
    [HasPushout f g] [HasPushout f' g']
    (hf : f ≫ iB.hom = iA.hom ≫ f') (hg : g ≫ iD.hom = iA.hom ≫ g') :
    pushout f g ≅ pushout f' g' := by
  have hf' : f' ≫ iB.inv = iA.inv ≫ f := by
    calc
      f' ≫ iB.inv = iA.inv ≫ ((iA.hom ≫ f') ≫ iB.inv) := by simp [Category.assoc]
      _ = iA.inv ≫ ((f ≫ iB.hom) ≫ iB.inv) := by rw [← hf]
      _ = iA.inv ≫ f := by simp [Category.assoc]
  have hg' : g' ≫ iD.inv = iA.inv ≫ g := by
    calc
      g' ≫ iD.inv = iA.inv ≫ ((iA.hom ≫ g') ≫ iD.inv) := by simp [Category.assoc]
      _ = iA.inv ≫ ((g ≫ iD.hom) ≫ iD.inv) := by rw [← hg]
      _ = iA.inv ≫ g := by simp [Category.assoc]
  refine
    { hom := pushout.desc (iB.hom ≫ pushout.inl f' g') (iD.hom ≫ pushout.inr f' g') ?_
      inv := pushout.desc (iB.inv ≫ pushout.inl f g) (iD.inv ≫ pushout.inr f g) ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · calc
      f ≫ (iB.hom ≫ pushout.inl f' g') = (f ≫ iB.hom) ≫ pushout.inl f' g' := by
        simp [Category.assoc]
      _ = (iA.hom ≫ f') ≫ pushout.inl f' g' := by rw [hf]
      _ = iA.hom ≫ (f' ≫ pushout.inl f' g') := by simp [Category.assoc]
      _ = iA.hom ≫ (g' ≫ pushout.inr f' g') := by rw [pushout.condition]
      _ = (iA.hom ≫ g') ≫ pushout.inr f' g' := by simp [Category.assoc]
      _ = (g ≫ iD.hom) ≫ pushout.inr f' g' := by rw [← hg]
      _ = g ≫ (iD.hom ≫ pushout.inr f' g') := by simp [Category.assoc]
  · calc
      f' ≫ (iB.inv ≫ pushout.inl f g) = (f' ≫ iB.inv) ≫ pushout.inl f g := by
        simp [Category.assoc]
      _ = (iA.inv ≫ f) ≫ pushout.inl f g := by rw [hf']
      _ = iA.inv ≫ (f ≫ pushout.inl f g) := by simp [Category.assoc]
      _ = iA.inv ≫ (g ≫ pushout.inr f g) := by rw [pushout.condition]
      _ = (iA.inv ≫ g) ≫ pushout.inr f g := by simp [Category.assoc]
      _ = (g' ≫ iD.inv) ≫ pushout.inr f g := by rw [← hg']
      _ = g' ≫ (iD.inv ≫ pushout.inr f g) := by simp [Category.assoc]
  · apply pushout.hom_ext
    · rw [← Category.assoc, pushout.inl_desc, Category.assoc, pushout.inl_desc]
      simp
    · rw [← Category.assoc, pushout.inr_desc, Category.assoc, pushout.inr_desc]
      simp
  · apply pushout.hom_ext
    · rw [← Category.assoc, pushout.inl_desc, Category.assoc, pushout.inl_desc]
      simp
    · rw [← Category.assoc, pushout.inr_desc, Category.assoc, pushout.inr_desc]
      simp

end HomotopyHypothesis.Bridge.GlobularEquivalence
