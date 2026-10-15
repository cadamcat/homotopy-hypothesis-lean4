import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderCells.AnodyneCylSubMapCell
import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSub
import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSubMap
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
/-!
# Finite cell filtrations of glued cylinders

The glued cylinders over finite semi-simplicial sets placeholder finite filtrations by their simplices.
-/

universe u v

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Cylinder.AnodyneCells

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological

/-- The simplices of `A'` which are not in `A`, with dimension recorded. -/
def missing (W : SemiSSet.{u}) (A A' : Subfunctor W) :
    Set (Σ n : ℕ, W.obj (op (Henry.SemiSimplexCategory.mk n))) :=
  {p | p.2 ∈ A'.obj (op (Henry.SemiSimplexCategory.mk p.1)) ∧
    p.2 ∉ A.obj (op (Henry.SemiSimplexCategory.mk p.1))}

theorem missing_finite {W : SemiSSet.{u}} (hW : W.IsFinite)
    (A A' : Subfunctor W) : (missing W A A').Finite := by
  classical
  obtain ⟨N, hN⟩ := hW.2
  letI : ∀ n : ℕ, Finite (W.obj (op (Henry.SemiSimplexCategory.mk n))) := hW.1
  letI : ∀ n : Fin (N + 1), Finite (W.obj (op (Henry.SemiSimplexCategory.mk n.val))) :=
    fun n => hW.1 n.val
  haveI : Finite (Σ n : Fin (N + 1), W.obj (op (Henry.SemiSimplexCategory.mk n.val))) := inferInstance
  apply Finite.of_injective (fun p : missing W A A' =>
    (⟨⟨p.1.1, by
      have hle : p.1.1 ≤ N := by
        by_contra h
        have hlt : N < p.1.1 := Nat.lt_of_not_ge h
        exact (hN p.1.1 hlt).false p.1.2
      exact Nat.lt_succ_of_le hle⟩,
      p.1.2⟩ : Σ n : Fin (N + 1), W.obj (op (Henry.SemiSimplexCategory.mk n.val))))
  intro p q hpq
  have hpq' := Sigma.mk.inj_iff.mp hpq
  apply Subtype.ext
  apply Sigma.ext
  · exact congrArg Fin.val hpq'.1
  · exact hpq'.2

theorem CylDatum.incl_restrictMap
    {I I' : Type u} [Category.{0} I] [Category.{0} I']
    {X : SemiSSet.{u}} (D : CylDatum X I) (E : I' ⥤ I) :
    (D.restrict E).incl ≫ D.restrictMap E = colimit.pre D.DC E ≫ D.incl := by
  unfold CylDatum.incl CylDatum.restrictMap pushout.map
  exact pushout.inr_desc _ _ _

theorem CylDatum.restrictMap_comp
    {I I' I'' : Type u} [Category.{0} I] [Category.{0} I'] [Category.{0} I'']
    {X : SemiSSet.{u}} (D : CylDatum X I) (E : I' ⥤ I) (F : I'' ⥤ I') :
    (D.restrict E).restrictMap F ≫ D.restrictMap E = D.restrictMap (F ⋙ E) := by
  apply pushout.hom_ext
  · calc
      _ = ((D.restrict E).restrict F).base ≫
          (D.restrict E).restrictMap F ≫ D.restrictMap E := rfl
      _ = (D.restrict E).base ≫ D.restrictMap E := by
        rw [← Category.assoc, (D.restrict E).base_restrictMap F]
      _ = D.base := D.base_restrictMap E
      _ = (D.restrict (F ⋙ E)).base ≫ D.restrictMap (F ⋙ E) :=
        (D.base_restrictMap (F ⋙ E)).symm
  · apply colimit.hom_ext
    intro i
    change
      (colimit.ι ((D.restrict E).restrict F).DC i ≫
        ((D.restrict E).restrict F).incl) ≫
          ((D.restrict E).restrictMap F ≫ D.restrictMap E) =
      (colimit.ι (D.restrict (F ⋙ E)).DC i ≫ (D.restrict (F ⋙ E)).incl) ≫
        D.restrictMap (F ⋙ E)
    have hleft :
        (colimit.ι ((D.restrict E).restrict F).DC i ≫
          ((D.restrict E).restrict F).incl) ≫
            ((D.restrict E).restrictMap F ≫ D.restrictMap E) =
          colimit.ι D.DC (E.obj (F.obj i)) ≫ D.incl := by
      calc
        _ = (colimit.ι ((D.restrict E).restrict F).DC i ≫
            (((D.restrict E).restrict F).incl ≫ (D.restrict E).restrictMap F)) ≫
              D.restrictMap E := by simp [Category.assoc]
        _ = (colimit.ι ((D.restrict E).restrict F).DC i ≫
            (colimit.pre (E ⋙ D.DC) F ≫ (D.restrict E).incl)) ≫
              D.restrictMap E := by
                rw [CylDatum.incl_restrictMap (D := D.restrict E) (E := F)]
        _ = (colimit.ι ((D.restrict E).restrict F).DC i ≫
            colimit.pre (E ⋙ D.DC) F) ≫
              ((D.restrict E).incl ≫ D.restrictMap E) := by simp [Category.assoc]
        _ = (colimit.ι ((D.restrict E).restrict F).DC i ≫
            colimit.pre (E ⋙ D.DC) F) ≫
              (colimit.pre D.DC E ≫ D.incl) := by
                rw [CylDatum.incl_restrictMap (D := D) (E := E)]
        _ = (colimit.ι (E ⋙ D.DC) (F.obj i) ≫ colimit.pre D.DC E) ≫ D.incl := by
              rw [← Category.assoc, colimit.ι_pre]
        _ = colimit.ι D.DC (E.obj (F.obj i)) ≫ D.incl := by
              rw [colimit.ι_pre]
    have hright :
        (colimit.ι (D.restrict (F ⋙ E)).DC i ≫ (D.restrict (F ⋙ E)).incl) ≫
          D.restrictMap (F ⋙ E) =
        colimit.ι D.DC ((F ⋙ E).obj i) ≫ D.incl := by
      calc
        _ = colimit.ι (D.restrict (F ⋙ E)).DC i ≫
            ((D.restrict (F ⋙ E)).incl ≫ D.restrictMap (F ⋙ E)) := by
              simp [Category.assoc]
        _ = colimit.ι (D.restrict (F ⋙ E)).DC i ≫
            (colimit.pre D.DC (F ⋙ E) ≫ D.incl) := by
              rw [CylDatum.incl_restrictMap (D := D) (E := F ⋙ E)]
        _ = colimit.ι D.DC ((F ⋙ E).obj i) ≫ D.incl := by
              rw [← Category.assoc, colimit.ι_pre]
    calc
      _ = colimit.ι D.DC (E.obj (F.obj i)) ≫ D.incl := hleft
      _ = colimit.ι D.DC ((F ⋙ E).obj i) ≫ D.incl := rfl
      _ = _ := hright.symm

theorem elMap_comp {J J' J'' W : SemiSSet.{u}} (f : J ⟶ J') (g : J' ⟶ J'') :
    elMap (f ≫ g) = elMap f ⋙ elMap g := by
  exact CategoryTheory.Functor.ext (fun x => rfl) (fun x y h => by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    rfl)

theorem cylSubMap_comp {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)
    {A A' A'' : Subfunctor W} (h : A ≤ A') (k : A' ≤ A'') :
    cylSubMap φ h ≫ cylSubMap φ k = cylSubMap φ (le_trans h k) := by
  change ((cylSub φ A'').restrict (elMap (Subfunctor.homOfLe k))).restrictMap
      (elMap (Subfunctor.homOfLe h)) ≫
    (cylSub φ A'').restrictMap (elMap (Subfunctor.homOfLe k)) =
      (cylSub φ A'').restrictMap (elMap (Subfunctor.homOfLe (le_trans h k)))
  have hhom : Subfunctor.homOfLe h ≫ Subfunctor.homOfLe k =
      Subfunctor.homOfLe (le_trans h k) := by
    ext i x
    rfl
  have hfun : elMap (Subfunctor.homOfLe h) ⋙ elMap (Subfunctor.homOfLe k) =
      elMap (Subfunctor.homOfLe (le_trans h k)) :=
    (elMap_comp (W := W) (Subfunctor.homOfLe h) (Subfunctor.homOfLe k)).symm.trans
      (congrArg elMap hhom)
  rw [CylDatum.restrictMap_comp]
  cases hfun
  rfl

theorem CylDatum.restrictMap_isIso_of_final
    {I I' : Type u} [Category.{0} I] [Category.{0} I']
    {X : SemiSSet.{u}} (D : CylDatum X I) (E : I' ⥤ I) [Functor.Final E] :
    IsIso (D.restrictMap E) := by
  haveI : IsIso (colimit.pre D.DC E) := by
    apply Functor.Final.colimit_pre_isIso
  haveI : IsIso (colimit.pre D.B E) := by
    apply Functor.Final.colimit_pre_isIso
  unfold CylDatum.restrictMap
  exact pushout.map_isIso _ _ _ _ (𝟙 X) (colimit.pre D.DC E) (colimit.pre D.B E) _ _

theorem final_of_isEquivalence {C D : Type u} [Category.{0} C] [Category.{0} D]
    (E : C ⥤ D) [E.IsEquivalence] : Functor.Final E := by
  letI : Functor.Final (E ⋙ E.inv) := Functor.final_of_natIso E.asEquivalence.unitIso
  exact Functor.final_of_comp_full_faithful E E.inv

theorem elementsMap_isEquivalence {C : Type v} [Category.{0} C]
    {F G : Cᵒᵖ ⥤ Type u} (e : F ≅ G) :
    Functor.IsEquivalence (e.hom.mapElements) := by
  let η : 𝟭 F.Elements ≅ e.hom.mapElements ⋙ e.inv.mapElements :=
    NatIso.ofComponents
      (fun x => Functor.Elements.isoMk (Iso.refl x.obj) (by simp))
      (by
        intro x y f
        apply Functor.Elements.hom_ext
        simp [Functor.Elements.isoMk, NatTrans.mapElements])
  let ε : e.inv.mapElements ⋙ e.hom.mapElements ≅ 𝟭 G.Elements :=
    NatIso.ofComponents
      (fun x => Functor.Elements.isoMk (Iso.refl x.obj) (by simp))
      (by
        intro x y f
        apply Functor.Elements.hom_ext
        simp [Functor.Elements.isoMk, NatTrans.mapElements])
  exact Functor.IsEquivalence.mk' e.inv.mapElements η ε

theorem anodyne_cylSubMap_finite {X W : SemiSSet.{u}} (hW : W.IsFinite)
    (φ : W ⟶ sharp X) {A A' : Subfunctor W} (hAA' : A ≤ A') :
    anodyne (cylSubMap φ hAA') := by
  classical
  let Q : MorphismProperty SemiSSet.{u} :=
    hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}
  have hmain : ∀ m : ℕ, ∀ B : Subfunctor W, (hBA' : B ≤ A') →
      (missing W B A').ncard = m → anodyne (cylSubMap φ hBA') := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro A hAA' hm
      by_cases hnon : (missing W A A').Nonempty
      · let P : ℕ → Prop := fun n =>
          ∃ y : W.obj (op (Henry.SemiSimplexCategory.mk n)),
            y ∈ A'.obj (op (Henry.SemiSimplexCategory.mk n)) ∧
            y ∉ A.obj (op (Henry.SemiSimplexCategory.mk n))
        have hex : ∃ n, P n := by
          rcases hnon with ⟨⟨n, y⟩, hy⟩
          exact ⟨n, y, hy.1, hy.2⟩
        let n := Nat.find hex
        have hn : P n := Nat.find_spec hex
        have hmin : ∀ k < n, ¬ P k := fun k hk => Nat.find_min hex hk
        obtain ⟨y, hyA', hyA⟩ := hn
        have hfaces : ∀ (k : ℕ)
            (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n),
            k ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)) := by
          intro k θ hkn
          have hle : k ≤ n := by
            simpa only [SimplexCategory.len_mk] using
              (@SimplexCategory.len_le_of_mono _ _ θ.1 θ.2)
          have hlt : k < n := lt_of_le_of_ne hle hkn
          have hA'face : W.map θ.op y ∈ A'.obj (op (Henry.SemiSimplexCategory.mk k)) :=
            A'.map θ.op hyA'
          by_contra hnot
          exact hmin k hlt ⟨W.map θ.op y, hA'face, hnot⟩
        let A₁ : Subfunctor W := A ⊔ Subfunctor.ofSection y
        have hAA₁ : A ≤ A₁ := le_sup_left
        have hA₁A' : A₁ ≤ A' :=
          sup_le hAA' ((Subfunctor.ofSection_le_iff y A').2 hyA')
        have hyA₁ : y ∈ A₁.obj (op (Henry.SemiSimplexCategory.mk n)) := by
          change y ∈ A.obj _ ∪ (Subfunctor.ofSection y).obj _
          exact Or.inr (Subfunctor.mem_ofSection_obj y)
        have hA₁spec : ∀ (k : ℕ)
            (z : W.obj (op (Henry.SemiSimplexCategory.mk k))),
            z ∈ A₁.obj (op (Henry.SemiSimplexCategory.mk k)) →
              z ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)) ∨
                ∃ hk : k = n, hk ▸ z = y := by
          intro k z hz
          change z ∈ A.obj _ ∪ (Subfunctor.ofSection y).obj _ at hz
          rcases hz with hzA | hzSec
          · exact Or.inl hzA
          · change ∃ f : op (Henry.SemiSimplexCategory.mk n) ⟶
                op (Henry.SemiSimplexCategory.mk k), W.map f y = z at hzSec
            obtain ⟨f, hf⟩ := hzSec
            let θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n := f.unop
            have hle : k ≤ n := by
              simpa only [SimplexCategory.len_mk] using
                (@SimplexCategory.len_le_of_mono _ _ θ.1 θ.2)
            by_cases hkn : k = n
            · subst k
              have hθ : θ = 𝟙 _ := by
                have hfun :=
                  (SemiSimplexCategory.strictMono θ).eq_id
                have hOrd : θ.1.toOrderHom = OrderHom.id _ :=
                  OrderHom.ext _ _ (by simpa using hfun)
                apply WideSubcategory.hom_ext
                apply SimplexCategory.Hom.ext
                exact hOrd
              have hfId : f = 𝟙 _ := Quiver.Hom.unop_inj hθ
              rw [hfId] at hf
              change W.map (𝟙 (op (Henry.SemiSimplexCategory.mk n))) y = z at hf
              have hmapid : W.map (𝟙 (op (Henry.SemiSimplexCategory.mk n))) = 𝟙 _ :=
                W.map_id _
              rw [hmapid] at hf
              have hyz : y = z := by simpa using hf
              exact Or.inr ⟨rfl, hyz.symm⟩
            · have hlt : k < n := lt_of_le_of_ne hle hkn
              have hface := hfaces k θ hkn
              have hf' : W.map θ.op y = z := by simpa [θ] using hf
              exact Or.inl (by simpa only [← hf'] using hface)
        have hsub : missing W A₁ A' ⊆ missing W A A' := by
          intro p hp
          exact ⟨hp.1, fun hpA => hp.2 (hAA₁ _ hpA)⟩
        have hne : missing W A₁ A' ≠ missing W A A' := by
          intro heq
          have hyOld : (⟨n, y⟩ : Σ k, W.obj (op (Henry.SemiSimplexCategory.mk k))) ∈
              missing W A A' := ⟨hyA', hyA⟩
          have hyNew := heq.symm ▸ hyOld
          exact hyNew.2 hyA₁
        have hstrict : missing W A₁ A' ⊂ missing W A A' :=
          Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
        have hdec : (missing W A₁ A').ncard < m := by
          rw [← hm]
          exact Set.ncard_lt_ncard hstrict (missing_finite hW A A')
        have hcell : anodyne (cylSubMap φ hAA₁) :=
          anodyne_cylSubMap_cell φ hAA₁ n y hyA hyA₁ hfaces hA₁spec
        have hrec : anodyne (cylSubMap φ hA₁A') :=
          ih _ hdec A₁ hA₁A' rfl
        have hcell' : Q.multiplicativeClosure (cylSubMap φ hAA₁) := hcell
        have hrec' : Q.multiplicativeClosure (cylSubMap φ hA₁A') := hrec
        have hcomp' : Q.multiplicativeClosure
            (cylSubMap φ hAA₁ ≫ cylSubMap φ hA₁A') :=
          (MorphismProperty.multiplicativeClosure Q).comp_mem _ _ hcell' hrec'
        have hmap : cylSubMap φ hAA₁ ≫ cylSubMap φ hA₁A' =
            cylSubMap φ hAA' := by
          simpa using cylSubMap_comp φ hAA₁ hA₁A'
        change Q.multiplicativeClosure (cylSubMap φ hAA')
        exact hmap ▸ hcomp'
      · have hno : ∀ p, p ∉ missing W A A' := fun p hp => hnon ⟨p, hp⟩
        have hEq : A = A' := by
          apply le_antisymm hAA'
          intro i z hz
          cases i with
          | op j =>
            cases j with
            | mk obj =>
              cases obj with
              | mk n =>
                by_contra hnot
                exact hno ⟨n, z⟩ ⟨hz, hnot⟩
        subst A'
        have hId : Subfunctor.homOfLe (le_rfl : A ≤ A) = 𝟙 A.toFunctor := by
          ext i x
          rfl
        have hIso : IsIso (cylSubMap φ (le_rfl : A ≤ A)) := by
          change IsIso ((cylSub φ A).restrictMap
            (elMap (Subfunctor.homOfLe (le_rfl : A ≤ A))))
          rw [hId]
          let hEquiv : Functor.IsEquivalence (NatTrans.mapElements (𝟙 A.toFunctor)) := by
            let e : A.toFunctor ≅ A.toFunctor := Iso.refl _
            exact elementsMap_isEquivalence e
          letI : Functor.IsEquivalence (NatTrans.mapElements (𝟙 A.toFunctor)) := hEquiv
          letI : Functor.IsEquivalence ((NatTrans.mapElements (𝟙 A.toFunctor)).op) := inferInstance
          haveI : Functor.Final ((NatTrans.mapElements (𝟙 A.toFunctor)).op) :=
            final_of_isEquivalence _
          exact CylDatum.restrictMap_isIso_of_final (cylSub φ A) _
        change Q.multiplicativeClosure (cylSubMap φ (le_rfl : A ≤ A))
        exact MorphismProperty.le_multiplicativeClosure _ _
          (Or.inr (MorphismProperty.isomorphisms.infer_property _))
  exact hmain _ A hAA' rfl

noncomputable def rangeIso {J W : SemiSSet.{u}} (j : J ⟶ W) [Mono j] :
    J ≅ (Subfunctor.range j).toFunctor := by
  let f := Subfunctor.toRange j
  haveI : IsIso f := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro i
    rw [isIso_iff_bijective]
    constructor
    · intro x y hxy
      have hmono : Mono (j.app i) := by
        have hall : ∀ k, Mono (j.app k) := by
          rw [← NatTrans.mono_iff_mono_app]
          infer_instance
        exact hall i
      exact (mono_iff_injective (j.app i)).1 hmono (congrArg Subtype.val hxy)
    · intro y
      rcases y.2 with ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  exact asIso f

set_option maxHeartbeats 600000 in
theorem anodyne_cyl_restrictMap_proof {X W J : SemiSSet.{u}} (hW : W.IsFinite)
    (j : J ⟶ W) [Mono j] (φ : W ⟶ sharp X) :
    anodyne ((cylDatum φ).restrictMap (elMap j)) := by
  classical
  let Q : MorphismProperty SemiSSet.{u} :=
    hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}
  let R : Subfunctor W := Subfunctor.range j
  let e : J ≅ R.toFunctor := rangeIso j
  let topIncl : (⊤ : Subfunctor W).toFunctor ⟶ W := (⊤ : Subfunctor W).ι
  haveI : IsIso topIncl := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro i
    rw [isIso_iff_bijective]
    constructor
    · intro x y hxy
      exact Subtype.ext hxy
    · intro x
      exact ⟨⟨x, Set.mem_univ _⟩, rfl⟩
  let eTop : (⊤ : Subfunctor W).toFunctor ≅ W := asIso topIncl
  let ETop : (⊤ : Subfunctor W).toFunctor.Elementsᵒᵖ ⥤ W.Elementsᵒᵖ := elMap topIncl
  let ERange : R.toFunctor.Elementsᵒᵖ ⥤ W.Elementsᵒᵖ := elMap R.ι
  let EFromRange : J.Elementsᵒᵖ ⥤ R.toFunctor.Elementsᵒᵖ := elMap e.hom
  let ERangeTop : R.toFunctor.Elementsᵒᵖ ⥤ (⊤ : Subfunctor W).toFunctor.Elementsᵒᵖ :=
    elMap (Subfunctor.homOfLe (le_top : R ≤ ⊤))
  have hRangeFactor : ERangeTop ⋙ ETop = ERange := by
    have hι : Subfunctor.homOfLe (le_top : R ≤ ⊤) ≫ topIncl = R.ι := by
      simpa [topIncl] using Subfunctor.homOfLe_ι (le_top : R ≤ ⊤)
    exact (elMap_comp (W := W) _ _).symm.trans (congrArg elMap hι)
  have hJFactor : EFromRange ⋙ ERange = elMap j := by
    have hj : e.hom ≫ R.ι = j := by
      dsimp [e, rangeIso, R]
    exact (elMap_comp (W := W) _ _).symm.trans (congrArg elMap hj)
  have hEFromRange : Functor.IsEquivalence EFromRange := by
    change Functor.IsEquivalence (NatTrans.mapElements e.hom).op
    letI : Functor.IsEquivalence (NatTrans.mapElements e.hom) := elementsMap_isEquivalence e
    infer_instance
  haveI : Functor.Final EFromRange := final_of_isEquivalence EFromRange
  let D := cylDatum φ
  let fIso := (D.restrict ERange).restrictMap EFromRange
  have hfIso : IsIso fIso := CylDatum.restrictMap_isIso_of_final (D.restrict ERange) EFromRange
  have hCell : anodyne (cylSubMap φ (le_top : R ≤ ⊤)) :=
    anodyne_cylSubMap_finite hW φ (le_top : R ≤ ⊤)
  have hTopEquiv : Functor.IsEquivalence (elMap topIncl) := by
    change Functor.IsEquivalence (NatTrans.mapElements eTop.hom).op
    letI : Functor.IsEquivalence (NatTrans.mapElements eTop.hom) := elementsMap_isEquivalence eTop
    infer_instance
  haveI : Functor.Final (elMap topIncl) := final_of_isEquivalence (elMap topIncl)
  have hTop : IsIso (D.restrictMap (elMap topIncl)) :=
    CylDatum.restrictMap_isIso_of_final D (elMap topIncl)
  have hCellTop : cylSubMap φ (le_top : R ≤ ⊤) ≫ D.restrictMap (elMap topIncl) =
      D.restrictMap ERange := by
    change ((cylDatum φ).restrict ETop).restrictMap ERangeTop ≫
      (cylDatum φ).restrictMap ETop = (cylDatum φ).restrictMap ERange
    cases hRangeFactor
    exact CylDatum.restrictMap_comp (cylDatum φ) ETop ERangeTop
  have hMapRange : fIso ≫ D.restrictMap ERange = D.restrictMap (elMap j) := by
    change (D.restrict ERange).restrictMap EFromRange ≫ D.restrictMap ERange =
      D.restrictMap (elMap j)
    cases hJFactor
    exact CylDatum.restrictMap_comp D ERange EFromRange
  have hFactor : fIso ≫ cylSubMap φ (le_top : R ≤ ⊤) ≫
      D.restrictMap (elMap topIncl) = D.restrictMap (elMap j) := by
    change fIso ≫ (cylSubMap φ (le_top : R ≤ ⊤) ≫ D.restrictMap (elMap topIncl)) =
      D.restrictMap (elMap j)
    rw [hCellTop]
    exact hMapRange
  have hIsoClosure : Q.multiplicativeClosure fIso :=
    MorphismProperty.le_multiplicativeClosure _ _
      (Or.inr (MorphismProperty.isomorphisms.infer_property fIso))
  have hCellClosure : Q.multiplicativeClosure (cylSubMap φ (le_top : R ≤ ⊤)) := by
    change Q.multiplicativeClosure (cylSubMap φ (le_top : R ≤ ⊤))
    exact hCell
  have hTopClosure : Q.multiplicativeClosure (D.restrictMap (elMap topIncl)) := by
    exact MorphismProperty.le_multiplicativeClosure _ _
      (Or.inr (MorphismProperty.isomorphisms.infer_property (D.restrictMap (elMap topIncl))))
  have hcomp₁ : Q.multiplicativeClosure
      (fIso ≫ cylSubMap φ (le_top : R ≤ ⊤)) :=
    (MorphismProperty.multiplicativeClosure Q).comp_mem fIso
      (cylSubMap φ (le_top : R ≤ ⊤)) hIsoClosure hCellClosure
  have hcomp₂ : Q.multiplicativeClosure
      ((fIso ≫ cylSubMap φ (le_top : R ≤ ⊤)) ≫ D.restrictMap (elMap topIncl)) :=
    (MorphismProperty.multiplicativeClosure Q).comp_mem
      (fIso ≫ cylSubMap φ (le_top : R ≤ ⊤)) (D.restrictMap (elMap topIncl))
      hcomp₁ hTopClosure
  have hcomp : Q.multiplicativeClosure
      (fIso ≫ cylSubMap φ (le_top : R ≤ ⊤) ≫ D.restrictMap (elMap topIncl)) := by
    simpa only [Category.assoc] using hcomp₂
  change Q.multiplicativeClosure (D.restrictMap (elMap j))
  exact hFactor ▸ hcomp

#print axioms anodyne_cyl_restrictMap_proof

noncomputable def colimit_isInitial_of_isEmpty_index {I : Type u} [Category.{0} I]
    [IsEmpty I] (F : I ⥤ SemiSSet.{u}) : IsInitial (colimit F) := by
  refine IsInitial.ofUniqueHom (fun Y => ?_) (fun Y f => ?_)
  · let α : F ⟶ (Functor.const I).obj Y :=
      { app := fun i => False.elim (IsEmpty.false i)
        naturality := by intro i j g; exact False.elim (IsEmpty.false i) }
    exact colimit.desc F (Cocone.mk Y α)
  · apply colimit.hom_ext
    intro i
    exact False.elim (IsEmpty.false i)

theorem base_isIso_of_empty_index
    {I : Type u} [Category.{0} I] [IsEmpty I] {X : SemiSSet.{u}}
    (D : CylDatum X I) : IsIso D.base := by
  have hB : IsInitial (colimit D.B) := colimit_isInitial_of_isEmpty_index D.B
  have hDC : IsInitial (colimit D.DC) := colimit_isInitial_of_isEmpty_index D.DC
  have hmap : IsIso (colimMap D.botN) := by
    let e := hB.uniqueUpToIso hDC
    have heq : colimMap D.botN = e.hom := by
      apply hB.hom_ext
    rw [heq]
    infer_instance
  change IsIso (pushout.inl (colimit.desc D.B (Cocone.mk X D.xN)) (colimMap D.botN))
  exact (IsPushout.of_isColimit (pushoutIsPushout _ _)).isIso_inl_of_isIso

set_option maxHeartbeats 600000 in
theorem anodyne_cylJ_base_proof {X W J : SemiSSet.{u}} (hW : W.IsFinite)
    (j : J ⟶ W) [Mono j] (φ : W ⟶ sharp X) : anodyne (cylJ j φ).base := by
  classical
  let Q : MorphismProperty SemiSSet.{u} :=
    hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}
  let R : Subfunctor W := Subfunctor.range j
  let A₀ : Subfunctor W := ⊥
  have h₀R : A₀ ≤ R := bot_le
  have hEmptyObj (i : Henry.SemiSimplexCategoryᵒᵖ) : IsEmpty (A₀.toFunctor.obj i) := by
    change IsEmpty (↥(A₀.obj i))
    rw [Set.isEmpty_coe_sort]
    simp [A₀]
  haveI : IsEmpty A₀.toFunctor.Elementsᵒᵖ :=
    ⟨fun e => (hEmptyObj e.unop.obj).false e.unop.val⟩
  have hBase₀Iso : IsIso (cylSub φ A₀).base :=
    base_isIso_of_empty_index (cylSub φ A₀)
  have hCell : anodyne (cylSubMap φ h₀R) :=
    anodyne_cylSubMap_finite hW φ h₀R
  have hBaseFactor :
      (cylSub φ A₀).base ≫ cylSubMap φ h₀R = (cylSub φ R).base := by
    have hidx : elMap (Subfunctor.homOfLe h₀R) ⋙ elMap R.ι = elMap A₀.ι := by
      exact (elMap_comp (W := W) _ _).symm.trans
        (congrArg elMap (Subfunctor.homOfLe_ι h₀R))
    cases hidx
    exact CylDatum.base_restrictMap (cylSub φ R) (elMap (Subfunctor.homOfLe h₀R))
  have hBase₀Closure : Q.multiplicativeClosure (cylSub φ A₀).base :=
    MorphismProperty.le_multiplicativeClosure _ _
      (Or.inr (MorphismProperty.isomorphisms.infer_property (cylSub φ A₀).base))
  have hCellClosure : Q.multiplicativeClosure (cylSubMap φ h₀R) := by
    change Q.multiplicativeClosure (cylSubMap φ h₀R)
    exact hCell
  have hBaseRClosure : Q.multiplicativeClosure (cylSub φ R).base := by
    have hc : Q.multiplicativeClosure ((cylSub φ A₀).base ≫ cylSubMap φ h₀R) :=
      (MorphismProperty.multiplicativeClosure Q).comp_mem _ _ hBase₀Closure hCellClosure
    rw [hBaseFactor] at hc
    exact hc
  let e : J ≅ R.toFunctor := rangeIso j
  let ERange : R.toFunctor.Elementsᵒᵖ ⥤ W.Elementsᵒᵖ := elMap R.ι
  let EFromRange : J.Elementsᵒᵖ ⥤ R.toFunctor.Elementsᵒᵖ := elMap e.hom
  have hJFactor : EFromRange ⋙ ERange = elMap j := by
    have hj : e.hom ≫ R.ι = j := by
      dsimp [e, rangeIso, R]
    exact (elMap_comp (W := W) _ _).symm.trans (congrArg elMap hj)
  have hEFromRange : Functor.IsEquivalence EFromRange := by
    change Functor.IsEquivalence (NatTrans.mapElements e.hom).op
    letI : Functor.IsEquivalence (NatTrans.mapElements e.hom) := elementsMap_isEquivalence e
    infer_instance
  haveI : Functor.Final EFromRange := final_of_isEquivalence EFromRange
  let fIso := (cylSub φ R).restrictMap EFromRange
  have hfIso : IsIso fIso := CylDatum.restrictMap_isIso_of_final (cylSub φ R) EFromRange
  letI : IsIso fIso := hfIso
  have hBaseJFactor : (cylJ j φ).base ≫ fIso = (cylSub φ R).base := by
    cases hJFactor
    exact CylDatum.base_restrictMap (cylSub φ R) EFromRange
  have hBaseJEq : (cylJ j φ).base = (cylSub φ R).base ≫ inv fIso := by
    apply (cancel_mono fIso).mp
    calc
      (cylJ j φ).base ≫ fIso = (cylSub φ R).base := hBaseJFactor
      _ = ((cylSub φ R).base ≫ inv fIso) ≫ fIso := by simp [Category.assoc]
  have hInvClosure : Q.multiplicativeClosure (inv fIso) :=
    MorphismProperty.le_multiplicativeClosure _ _
      (Or.inr (MorphismProperty.isomorphisms.infer_property (inv fIso)))
  have hBaseJClosure : Q.multiplicativeClosure
      ((cylSub φ R).base ≫ inv fIso) :=
    (MorphismProperty.multiplicativeClosure Q).comp_mem _ _ hBaseRClosure hInvClosure
  change Q.multiplicativeClosure (cylJ j φ).base
  rw [hBaseJEq]
  exact hBaseJClosure

#print axioms anodyne_cylJ_base_proof
