import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.FinCellIsCylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.IsCellularRealizationFinCellIota
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeFiniteCellComplexHomotopyExtension
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Homotopy.RelativeLifting.HomotopyEquivalence.Part1
/-!
# Relative homotopies of finite cell complexes

Relative homotopies of finite cell complexes can be represented by maps out of relative
cylinders, including when the target space is not itself a finite cell complex.
-/

universe v u

open CategoryTheory Limits HomotopicalAlgebra TopCat HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Homotopy.RelativeLifting

private theorem relativeCylinderEndpointProperties {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B : C} {i : A ⟶ B} (hi : cofibrations C i)
    (cyl : RelativeCylinder i) :
    (cofibrations C (cyl.j₀ ≫ cyl.c) ∧ weakEquivalences C (cyl.j₀ ≫ cyl.c)) ∧
    (cofibrations C (cyl.j₁ ≫ cyl.c) ∧ weakEquivalences C (cyl.j₁ ≫ cyl.c)) := by
  have hcof₀ := (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
    cyl.isPushout hi
  have hcof₀' := (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem
    cyl.j₀ cyl.c hcof₀ cyl.c_mem
  have hcof₁ := (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
    cyl.isPushout.flip hi
  have hcof₁' := (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem
    cyl.j₁ cyl.c hcof₁ cyl.c_mem
  have hid : weakEquivalences C (𝟙 B) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 B)
      (MorphismProperty.isomorphisms.infer_property (𝟙 B))
  have hw₀ := IsCylinderCategory.twoOutOfSix (C := C) (cyl.j₀ ≫ cyl.c) cyl.p (𝟙 B)
    (by simpa [Category.assoc, cyl.j₀_c_p] using hid) (by simpa using cyl.p_mem)
  have hw₁ := IsCylinderCategory.twoOutOfSix (C := C) (cyl.j₁ ≫ cyl.c) cyl.p (𝟙 B)
    (by simpa [Category.assoc, cyl.j₁_c_p] using hid) (by simpa using cyl.p_mem)
  exact ⟨⟨hcof₀', hw₀.1⟩, ⟨hcof₁', hw₁.1⟩⟩

private theorem brownFactorization {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B : C} (f : A ⟶ B) :
    ∃ (M : C) (i : A ⟶ M) (p : M ⟶ B),
      cofibrations C i ∧ weakEquivalences C p ∧ i ≫ p = f := by
  classical
  obtain ⟨O, hO_nonempty⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hO : IsInitial O := Classical.choice hO_nonempty
  have hA0 : cofibrations C (hO.to A) :=
    IsCofibrationCategory.initial_cofibration hO A
  have hB0 : cofibrations C (hO.to B) :=
    IsCofibrationCategory.initial_cofibration hO B
  let cyl := Classical.choice (IsCylinderCategory.exists_cylinder (C := C) hO A)
  have hPAB : HasPushout (hO.to A) (hO.to B) :=
    IsCofibrationCategory.hasPushout (C := C) (hO.to A) (hO.to B) hA0
  letI := hPAB
  let PAB := pushout (hO.to A) (hO.to B)
  let a : A ⟶ PAB := pushout.inl (hO.to A) (hO.to B)
  let b : B ⟶ PAB := pushout.inr (hO.to A) (hO.to B)
  let hAB : IsPushout (hO.to A) (hO.to B) a b :=
    IsPushout.of_hasPushout (hO.to A) (hO.to B)
  have hP0 : HasPushout (hO.to A) (hO.to A) := cyl.isPushout.hasPushout
  letI := hP0
  have hdcond : (hO.to A) ≫ a = (hO.to A) ≫ (f ≫ b) := hO.hom_ext _ _
  let d : cyl.P ⟶ PAB := cyl.isPushout.desc a (f ≫ b) hdcond
  have hM : HasPushout cyl.c d :=
    IsCofibrationCategory.hasPushout (C := C) cyl.c d cyl.c_mem
  letI := hM
  let M := pushout cyl.c d
  let mI : cyl.I ⟶ M := pushout.inl cyl.c d
  let mAB : PAB ⟶ M := pushout.inr cyl.c d
  have hMpo : IsPushout cyl.c d mI mAB := IsPushout.of_hasPushout cyl.c d
  let qAB : PAB ⟶ B := hAB.desc f (𝟙 B) (by apply hO.hom_ext)
  have hqABa : a ≫ qAB = f := by simp [qAB, hAB]
  have hqABb : b ≫ qAB = 𝟙 B := by simp [qAB, hAB]
  have hcomm : cyl.c ≫ (cyl.p ≫ f) = d ≫ qAB := by
    apply cyl.isPushout.hom_ext
    · calc
        cyl.j₀ ≫ cyl.c ≫ cyl.p ≫ f = (cyl.j₀ ≫ cyl.c ≫ cyl.p) ≫ f := by simp [Category.assoc]
        _ = f := by rw [cyl.j₀_c_p]; simp
        _ = cyl.j₀ ≫ d ≫ qAB := by simp [d, qAB]
    · calc
        cyl.j₁ ≫ cyl.c ≫ cyl.p ≫ f = (cyl.j₁ ≫ cyl.c ≫ cyl.p) ≫ f := by simp [Category.assoc]
        _ = f := by rw [cyl.j₁_c_p]; simp
        _ = cyl.j₁ ≫ d ≫ qAB := by simp [d, qAB]
  let qM : M ⟶ B := hMpo.desc (cyl.p ≫ f) qAB hcomm
  have hqMAB : mAB ≫ qM = qAB := by simp [qM, hMpo]
  have hinc : IsPushout (cyl.j₁ ≫ cyl.c) f mI (b ≫ mAB) := by
    let e₀ : A ⟶ cyl.I := cyl.j₀ ≫ cyl.c
    let e₁ : A ⟶ cyl.I := cyl.j₁ ≫ cyl.c
    have hsq : e₁ ≫ mI = f ≫ (b ≫ mAB) := by
      calc
        e₁ ≫ mI = cyl.j₁ ≫ (cyl.c ≫ mI) := by simp [e₁, Category.assoc]
        _ = cyl.j₁ ≫ (d ≫ mAB) := by rw [hMpo.w]
        _ = (cyl.j₁ ≫ d) ≫ mAB := by simp [Category.assoc]
        _ = f ≫ (b ≫ mAB) := by simp [d, Category.assoc]
    let t : PushoutCocone e₁ f := PushoutCocone.mk mI (b ≫ mAB) hsq
    have ht : IsColimit t := by
      apply PushoutCocone.isColimitAux' t
      intro s
      have hinit : (hO.to A) ≫ (e₀ ≫ s.inl) = (hO.to B) ≫ s.inr := hO.hom_ext _ _
      let q : PAB ⟶ s.pt := hAB.desc (e₀ ≫ s.inl) s.inr hinit
      have hcompat : d ≫ q = cyl.c ≫ s.inl := by
        apply cyl.isPushout.hom_ext
        · simp [q, d, hAB, e₀]
        · calc
            cyl.j₁ ≫ d ≫ q = f ≫ b ≫ q := by simp [d, Category.assoc]
            _ = f ≫ s.inr := by simp [q]
            _ = e₁ ≫ s.inl := s.condition.symm
            _ = cyl.j₁ ≫ cyl.c ≫ s.inl := by simpa [e₁]
      let m := hMpo.desc s.inl q hcompat.symm
      have hmI : mI ≫ m = s.inl := by
        dsimp [m]
        exact hMpo.inl_desc s.inl q hcompat.symm
      have hmAB : mAB ≫ m = q := by
        dsimp [m]
        exact hMpo.inr_desc s.inl q hcompat.symm
      refine ⟨m, hmI, ?_, ?_⟩
      · calc
          (b ≫ mAB) ≫ m = b ≫ (mAB ≫ m) := by simp [Category.assoc]
          _ = b ≫ q := by rw [hmAB]
          _ = s.inr := by simp [q]
      · intro m' hm'I hm'B
        change M ⟶ s.pt at m'
        change mI ≫ m' = s.inl at hm'I
        have hmAB' : mAB ≫ m' = q := by
          apply hAB.hom_ext
          · calc
              a ≫ mAB ≫ m' = cyl.j₀ ≫ d ≫ mAB ≫ m' := by simp [d, Category.assoc]
              _ = cyl.j₀ ≫ (d ≫ mAB) ≫ m' := by simp [Category.assoc]
              _ = cyl.j₀ ≫ (cyl.c ≫ mI) ≫ m' := by rw [← hMpo.w]
              _ = cyl.j₀ ≫ cyl.c ≫ s.inl := by simp [Category.assoc, hm'I]
              _ = a ≫ q := by simp [q, e₀]
          · calc
              b ≫ mAB ≫ m' = (b ≫ mAB) ≫ m' := by simp [Category.assoc]
              _ = s.inr := hm'B
              _ = b ≫ q := by simp [q]
        apply hMpo.hom_ext
        · calc
            mI ≫ m' = s.inl := hm'I
            _ = mI ≫ m := hmI.symm
        · exact hmAB'.trans hmAB.symm
    exact IsPushout.of_isColimit ht
  have hend := relativeCylinderEndpointProperties hA0 cyl
  have hincW : weakEquivalences C (b ≫ mAB) :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      (cyl.j₁ ≫ cyl.c) f mI (b ≫ mAB) hinc hend.2.1 hend.2.2
  have hid : weakEquivalences C (𝟙 B) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 B)
      (MorphismProperty.isomorphisms.infer_property (𝟙 B))
  have hsqW : weakEquivalences C ((b ≫ mAB) ≫ qM) := by
    rw [Category.assoc, hqMAB, hqABb]
    exact hid
  have hqW := IsCylinderCategory.twoOutOfSix (C := C) (𝟙 B) (b ≫ mAB) qM
    (by simpa using hincW) hsqW
  have hiW : weakEquivalences C qM := hqW.2.2.1
  have hia : cofibrations C (a ≫ mAB) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem a mAB
      ((IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hAB hB0)
      ((IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hMpo.flip cyl.c_mem)
  refine ⟨M, a ≫ mAB, qM, hia, hiW, ?_⟩
  calc
    (a ≫ mAB) ≫ qM = a ≫ (mAB ≫ qM) := by simp [Category.assoc]
    _ = a ≫ qAB := by rw [hqMAB]
    _ = f := hqABa

private theorem existsRelativeCylinder {A B : HomotopyHypothesis.Henry.FinCell.{u}}
    (i : A ⟶ B) (hi : cofibrations HomotopyHypothesis.Henry.FinCell.{u} i) :
    Nonempty (RelativeCylinder i) := by
  classical
  letI : IsCylinderCategory HomotopyHypothesis.Henry.FinCell.{u} :=
    HomotopyHypothesis.Henry.Packages.finCell_isCylinderCategory
  letI : HasPushout i i :=
    IsCofibrationCategory.hasPushout (C := HomotopyHypothesis.Henry.FinCell.{u}) i i hi
  let P := pushout i i
  let j₀ : B ⟶ P := pushout.inl i i
  let j₁ : B ⟶ P := pushout.inr i i
  let hP : IsPushout i i j₀ j₁ := IsPushout.of_hasPushout i i
  let fold : P ⟶ B := hP.desc (𝟙 B) (𝟙 B) (by simp)
  obtain ⟨I, c, p, hc, hp, hcp⟩ := brownFactorization fold
  refine ⟨⟨P, j₀, j₁, hP, I, c, p, hc, hp, ?_, ?_⟩⟩
  · calc
      j₀ ≫ c ≫ p = j₀ ≫ (c ≫ p) := by simp [Category.assoc]
      _ = j₀ ≫ fold := by rw [hcp]
      _ = 𝟙 B := by simp [fold]
  · calc
      j₁ ≫ c ≫ p = j₁ ≫ (c ≫ p) := by simp [Category.assoc]
      _ = j₁ ≫ fold := by rw [hcp]
      _ = 𝟙 B := by simp [fold]

private def constantPathFamily {B Y : TopCat.{u}} (f : B ⟶ Y) :
    B ⟶ TopCat.of C(unitInterval, Y) :=
  TopCat.ofHom <| ContinuousMap.curry (f.hom.comp ContinuousMap.fst)

private def homotopyPathFamily {B Y : TopCat.{u}} {f g : B ⟶ Y}
    (H : f.hom.Homotopy g.hom) : B ⟶ TopCat.of C(unitInterval, Y) :=
  TopCat.ofHom <| ContinuousMap.curry (H.toContinuousMap.comp ContinuousMap.prodSwap)

/-- A relative homotopy of maps from a finite cell pair can be represented by a relative cylinder.
The same holds for maps into arbitrary spaces. -/
theorem finCell_homotopicRel_iff_proof {A B : FinCell.{u}} (i : A ⟶ B)
    (hi : cofibrations FinCell.{u} i) {Y : TopCat.{u}} (f g : B.obj ⟶ Y) :
    f.hom.HomotopicRel g.hom (Set.range i.hom.hom) ↔
      ∃ (cyl : RelativeCylinder i) (h : cyl.I.obj ⟶ Y),
        (cyl.j₀ ≫ cyl.c).hom ≫ h = f ∧ (cyl.j₁ ≫ cyl.c).hom ≫ h = g := by
  letI : IsCylinderCategory FinCell.{u} := Packages.finCell_isCylinderCategory
  let incl : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι Top.IsFiniteCellComplex
  let iT : A.obj ⟶ B.obj := incl.map i
  have hiT : Top.relativeFiniteCellComplexes iT := hi
  constructor
  · intro hrel
    rcases hrel with ⟨H⟩
    obtain ⟨cyl⟩ := existsRelativeCylinder i hi
    let j₀T : B.obj ⟶ cyl.P.obj := incl.map cyl.j₀
    let j₁T : B.obj ⟶ cyl.P.obj := incl.map cyl.j₁
    let cT : cyl.P.obj ⟶ cyl.I.obj := incl.map cyl.c
    let pT : cyl.I.obj ⟶ B.obj := incl.map cyl.p
    have hfg : iT ≫ f = iT ≫ g := by
      apply TopCat.hom_ext
      ext a
      have ha : iT.hom a ∈ Set.range i.hom.hom := by
        exact ⟨a, by rfl⟩
      calc
        f.hom (iT.hom a) = H.toHomotopy (1, iT.hom a) := (H.prop' 1 _ ha).symm
        _ = g.hom (iT.hom a) := H.toHomotopy.map_one_left _
    have hP : IsPushout iT iT j₀T j₁T :=
      Packages.isCellularRealization_finCellι.map_isPushout
        i i cyl.j₀ cyl.j₁ cyl.isPushout hi
    let d : cyl.P.obj ⟶ Y := hP.desc f g hfg
    have hd₀ : j₀T ≫ d = f := hP.inl_desc f g hfg
    have hd₁ : j₁T ≫ d = g := hP.inr_desc f g hfg
    have hj₀cp : j₀T ≫ cT ≫ pT = 𝟙 B.obj := by
      simpa [incl, j₀T, cT, pT, ← Functor.map_comp] using congrArg incl.map cyl.j₀_c_p
    have hj₁cp : j₁T ≫ cT ≫ pT = 𝟙 B.obj := by
      simpa [incl, j₁T, cT, pT, ← Functor.map_comp] using congrArg incl.map cyl.j₁_c_p
    let leftPath := constantPathFamily f
    let rightPath := homotopyPathFamily H.toHomotopy
    have hcompat : iT ≫ leftPath = iT ≫ rightPath := by
      apply TopCat.hom_ext
      ext a t
      change f.hom (iT.hom a) = H.toHomotopy (t, iT.hom a)
      have ha : iT.hom a ∈ Set.range i.hom.hom := by
        exact ⟨a, by rfl⟩
      exact (H.prop' t _ ha).symm
    let q : cyl.P.obj ⟶ TopCat.of C(unitInterval, Y) :=
      hP.desc leftPath rightPath hcompat
    have hq₀ : (j₀T ≫ q).hom = leftPath.hom :=
      congrArg Hom.hom (hP.inl_desc leftPath rightPath hcompat)
    have hq₁ : (j₁T ≫ q).hom = rightPath.hom :=
      congrArg Hom.hom (hP.inr_desc leftPath rightPath hcompat)
    let z₀ : C(cyl.P.obj, Y) := q.hom.uncurry.comp
      (ContinuousMap.prodMk (ContinuousMap.id cyl.P.obj) (ContinuousMap.const cyl.P.obj 0))
    let z₁ : C(cyl.P.obj, Y) := q.hom.uncurry.comp
      (ContinuousMap.prodMk (ContinuousMap.id cyl.P.obj) (ContinuousMap.const cyl.P.obj 1))
    let k : C(unitInterval × cyl.P.obj, Y) := q.hom.uncurry.comp ContinuousMap.prodSwap
    let K : z₀.Homotopy z₁ := {
      toFun := k
      continuous_toFun := k.continuous
      map_zero_left := by intro x; rfl
      map_one_left := by intro x; rfl }
    have hz₀₀ : j₀T ≫ TopCat.ofHom z₀ = j₀T ≫ cT ≫ pT ≫ f := by
      apply TopCat.hom_ext
      ext b
      change q.hom.uncurry (j₀T.hom b, 0) = (j₀T ≫ cT ≫ pT ≫ f).hom b
      calc
        q.hom.uncurry (j₀T.hom b, 0) = (q.hom (j₀T.hom b)) 0 := rfl
        _ = (leftPath.hom b) 0 := by
          exact congrArg (fun m : C(unitInterval, Y) => m 0)
            (ContinuousMap.congr_fun hq₀ b)
        _ = f.hom b := by simp [leftPath, constantPathFamily, ContinuousMap.curry_apply]
        _ = (j₀T ≫ cT ≫ pT ≫ f).hom b := by
          have hcomp : j₀T ≫ cT ≫ pT ≫ f = f := by
            calc
              j₀T ≫ cT ≫ pT ≫ f = (j₀T ≫ cT ≫ pT) ≫ f := by simp [Category.assoc]
              _ = 𝟙 B.obj ≫ f := by rw [hj₀cp]
              _ = f := by simp
          exact (ContinuousMap.congr_fun (congrArg Hom.hom hcomp) b).symm
    have hz₀₁ : j₁T ≫ TopCat.ofHom z₀ = j₁T ≫ cT ≫ pT ≫ f := by
      apply TopCat.hom_ext
      ext b
      change q.hom.uncurry (j₁T.hom b, 0) = (j₁T ≫ cT ≫ pT ≫ f).hom b
      calc
        q.hom.uncurry (j₁T.hom b, 0) = (q.hom (j₁T.hom b)) 0 := rfl
        _ = (rightPath.hom b) 0 := by
          exact congrArg (fun m : C(unitInterval, Y) => m 0)
            (ContinuousMap.congr_fun hq₁ b)
        _ = f.hom b := by
          simp [rightPath, homotopyPathFamily, ContinuousMap.curry_apply]
        _ = (j₁T ≫ cT ≫ pT ≫ f).hom b := by
          have hcomp : j₁T ≫ cT ≫ pT ≫ f = f := by
            calc
              j₁T ≫ cT ≫ pT ≫ f = (j₁T ≫ cT ≫ pT) ≫ f := by simp [Category.assoc]
              _ = 𝟙 B.obj ≫ f := by rw [hj₁cp]
              _ = f := by simp
          exact (ContinuousMap.congr_fun (congrArg Hom.hom hcomp) b).symm
    have hz₀ : TopCat.ofHom z₀ = cT ≫ pT ≫ f := by
      apply hP.hom_ext
      · exact hz₀₀
      · exact hz₀₁
    have hz₁₀ : j₀T ≫ TopCat.ofHom z₁ = j₀T ≫ d := by
      apply TopCat.hom_ext
      ext b
      change q.hom.uncurry (j₀T.hom b, 1) = (j₀T ≫ d).hom b
      calc
        q.hom.uncurry (j₀T.hom b, 1) = (q.hom (j₀T.hom b)) 1 := rfl
        _ = (leftPath.hom b) 1 := by
          exact congrArg (fun m : C(unitInterval, Y) => m 1)
            (ContinuousMap.congr_fun hq₀ b)
        _ = f.hom b := by simp [leftPath, constantPathFamily, ContinuousMap.curry_apply]
        _ = (j₀T ≫ d).hom b := by rw [hd₀]
    have hz₁₁ : j₁T ≫ TopCat.ofHom z₁ = j₁T ≫ d := by
      apply TopCat.hom_ext
      ext b
      change q.hom.uncurry (j₁T.hom b, 1) = (j₁T ≫ d).hom b
      calc
        q.hom.uncurry (j₁T.hom b, 1) = (q.hom (j₁T.hom b)) 1 := rfl
        _ = (rightPath.hom b) 1 := by
          exact congrArg (fun m : C(unitInterval, Y) => m 1)
            (ContinuousMap.congr_fun hq₁ b)
        _ = g.hom b := by
          simp [rightPath, homotopyPathFamily, ContinuousMap.curry_apply]
        _ = (j₁T ≫ d).hom b := by rw [hd₁]
    have hz₁ : TopCat.ofHom z₁ = d := by
      apply hP.hom_ext
      · exact hz₁₀
      · exact hz₁₁
    let K' := K.cast (by
      simpa [TopCat.hom_comp, Category.assoc] using congrArg Hom.hom hz₀)
      (congrArg Hom.hom hz₁)
    have hcT : Top.relativeFiniteCellComplexes cT := cyl.c_mem
    obtain ⟨l, E, hE⟩ :=
      Packages.relativeFiniteCellComplex_homotopyExtension cT hcT (pT ≫ f).hom d.hom K'
    have h₀ : l.comp (j₀T ≫ cT).hom = f.hom := by
      ext b
      calc
        l ((j₀T ≫ cT).hom b) = E (1, cT.hom (j₀T.hom b)) := by
          rw [E.apply_one]
          rfl
        _ = K' (1, j₀T.hom b) := hE 1 (j₀T.hom b)
        _ = d.hom (j₀T.hom b) := K'.apply_one _
        _ = f.hom b := by
          have h := congrArg Hom.hom hd₀
          exact (ContinuousMap.congr_fun (by simpa [TopCat.hom_comp] using h) b)
    have h₁ : l.comp (j₁T ≫ cT).hom = g.hom := by
      ext b
      calc
        l ((j₁T ≫ cT).hom b) = E (1, cT.hom (j₁T.hom b)) := by
          rw [E.apply_one]
          rfl
        _ = K' (1, j₁T.hom b) := hE 1 (j₁T.hom b)
        _ = d.hom (j₁T.hom b) := K'.apply_one _
        _ = g.hom b := by
          have h := congrArg Hom.hom hd₁
          exact (ContinuousMap.congr_fun (by simpa [TopCat.hom_comp] using h) b)
    refine ⟨cyl, TopCat.ofHom l, ?_, ?_⟩
    · apply TopCat.hom_ext
      ext b
      exact ContinuousMap.congr_fun h₀ b
    · apply TopCat.hom_ext
      ext b
      exact ContinuousMap.congr_fun h₁ b
  · rintro ⟨cyl, h, h₀, h₁⟩
    let incl : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι Top.IsFiniteCellComplex
    let iT : A.obj ⟶ B.obj := incl.map i
    let j₀T : B.obj ⟶ cyl.P.obj := incl.map cyl.j₀
    let j₁T : B.obj ⟶ cyl.P.obj := incl.map cyl.j₁
    let cT : cyl.P.obj ⟶ cyl.I.obj := incl.map cyl.c
    let pT : cyl.I.obj ⟶ B.obj := incl.map cyl.p
    have hiT : Top.relativeFiniteCellComplexes iT := hi
    have hpT : Top.homotopyEquivalences pT := cyl.p_mem
    have hpush : iT ≫ j₀T = iT ≫ j₁T := by
      simpa [incl, iT, j₀T, j₁T, ← Functor.map_comp] using
        congrArg incl.map cyl.isPushout.w
    have hbound : iT ≫ (j₀T ≫ cT) = iT ≫ (j₁T ≫ cT) := by
      calc
        iT ≫ (j₀T ≫ cT) = (iT ≫ j₀T) ≫ cT := by simp [Category.assoc]
        _ = (iT ≫ j₁T) ≫ cT := by rw [hpush]
        _ = iT ≫ (j₁T ≫ cT) := by simp [Category.assoc]
    have hs₀ : j₀T ≫ cT ≫ pT = 𝟙 B.obj := by
      simpa [incl, j₀T, cT, pT, ← Functor.map_comp] using congrArg incl.map cyl.j₀_c_p
    have hs₁ : j₁T ≫ cT ≫ pT = 𝟙 B.obj := by
      simpa [incl, j₁T, cT, pT, ← Functor.map_comp] using congrArg incl.map cyl.j₁_c_p
    have hpost : ((j₀T ≫ cT) ≫ pT).hom.HomotopicRel
        ((j₁T ≫ cT) ≫ pT).hom (Set.range iT.hom) := by
      rw [show (j₀T ≫ cT) ≫ pT = 𝟙 B.obj by simpa [Category.assoc] using hs₀,
        show (j₁T ≫ cT) ≫ pT = 𝟙 B.obj by simpa [Category.assoc] using hs₁]
      exact ContinuousMap.HomotopicRel.refl (ContinuousMap.id B.obj)
    have hrel := (relativeLift_of_homotopyEquivalence_proof iT hiT pT hpT).2
      (j₀T ≫ cT) (j₁T ≫ cT) hbound hpost
    rcases hrel.comp_continuousMap h.hom with ⟨Hrel'⟩
    have hend₀ : h.hom.comp (j₀T ≫ cT).hom = f.hom := by
      have hh := congrArg Hom.hom h₀
      simpa [incl, j₀T, cT, TopCat.hom_comp] using hh
    have hend₁ : h.hom.comp (j₁T ≫ cT).hom = g.hom := by
      have hh := congrArg Hom.hom h₁
      simpa [incl, j₁T, cT, TopCat.hom_comp] using hh
    exact ⟨Hrel'.cast hend₀ hend₁⟩

#print axioms finCell_homotopicRel_iff_proof

end HomotopyHypothesis.Homotopy.RelativeLifting
