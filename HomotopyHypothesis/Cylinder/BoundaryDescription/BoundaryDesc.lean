import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderCellProof.Part1
import HomotopyHypothesis.Approximation.Topological.CylinderCells.BotBdry
import HomotopyHypothesis.Approximation.Topological.CylinderCells.CylSub
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElFaceHom
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElOf
import HomotopyHypothesis.Approximation.Topological.CylinderCells.FaceBdry
import HomotopyHypothesis.Approximation.Topological.CylinderCells.FaceBdryGen
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylD
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBot
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundary
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryIota
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.DerivedCylinderMap
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
import HomotopyHypothesis.Approximation.Topological.NormalForm.NF
import HomotopyHypothesis.Approximation.Topological.NormalForm.SemiSimplexHomExtOfSurjective
universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Cylinder.BoundaryDescription

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological

theorem simplexMap_compHom {V V' : Type} [LinearOrder V] [LinearOrder V']
    {K : Complex V} {K' : Complex V'} {k : ℕ}
    (f : K.Hom K') (w : Fin (k + 1) → V) (hw : StrictMono w)
    (hS : K.S (Finset.univ.image w)) :
    K.simplexMap w hw hS ≫ f.toSemiSSet =
      K'.simplexMap (f.f ∘ w) (by
        intro i j hij
        apply f.strictMonoOn _ hS
        · exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
        · exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
        · exact hw hij)
        (by simpa [Finset.image_image] using f.map_S _ hS) := by
  apply uliftYonedaEquiv.injective
  simp only [Complex.simplexMap, uliftYonedaEquiv_comp, Complex.Hom.toSemiSSet]
  apply congrArg ULift.up
  apply Subtype.ext
  rfl

theorem simplexMap_precomp {V : Type} [LinearOrder V] {K : Complex V} {k l : ℕ}
    (α : Henry.SemiSimplexCategory.mk l ⟶ Henry.SemiSimplexCategory.mk k)
    (w : Fin (k + 1) → V) (hw : StrictMono w)
    (hS : K.S (Finset.univ.image w)) :
    Henry.SemiSSet.stdSimplex.map α ≫ K.simplexMap w hw hS =
      K.simplexMap (w ∘ α.1.toOrderHom) (hw.comp (SemiSimplexCategory.strictMono α))
        (K.down (by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply] at hx ⊢
          obtain ⟨i, rfl⟩ := hx
          exact ⟨α.1.toOrderHom i, rfl⟩) hS) := by
  simp only [Complex.simplexMap]
  have hx : K.toSemiSSet.map α.op (ULift.up (⟨w, hw, hS⟩ : K.Simplex k)) =
      ULift.up ⟨w ∘ α.1.toOrderHom, hw.comp (SemiSimplexCategory.strictMono α),
        K.down (by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply] at hx ⊢
          obtain ⟨i, rfl⟩ := hx
          exact ⟨α.1.toOrderHom i, rfl⟩) hS⟩ := by
    rfl
  rw [← hx]
  exact (uliftYonedaEquiv_symm_map (F := K.toSemiSSet) (f := α.op)
    (ULift.up (⟨w, hw, hS⟩ : K.Simplex k))).symm

theorem simplexMap_congr {V : Type} [LinearOrder V] {K : Complex V} {k : ℕ}
    {w w' : Fin (k + 1) → V} (h : w = w')
    (hw : StrictMono w) (hS : K.S (Finset.univ.image w))
    (hw' : StrictMono w') (hS' : K.S (Finset.univ.image w')) :
    K.simplexMap w hw hS = K.simplexMap w' hw' hS' := by
  cases h
  rfl

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

def dcylCarrier {n m : ℕ} (S : Finset (DV n m)) : Finset (Fin (n + 1)) :=
  S.biUnion fun a =>
    match a with
    | .top i => {i}
    | .mid T => T
    | .bot _ => ∅

theorem mem_dcylCarrier_top {n m : ℕ} {S : Finset (DV n m)} {i : Fin (n + 1)}
    (hi : DV.top i ∈ S) : i ∈ dcylCarrier S := by
  simp only [dcylCarrier, Finset.mem_biUnion]
  exact ⟨DV.top i, hi, by simp⟩

theorem subset_dcylCarrier_mid {n m : ℕ} {S : Finset (DV n m)} {T : Finset (Fin (n + 1))}
    (hT : DV.mid T ∈ S) : T ⊆ dcylCarrier S := by
  intro i hi
  simp only [dcylCarrier, Finset.mem_biUnion]
  exact ⟨DV.mid T, hT, hi⟩

theorem dcylCarrier_mono {n m : ℕ} {S S' : Finset (DV n m)} (h : S ⊆ S') :
    dcylCarrier S ⊆ dcylCarrier S' := by
  intro i hi
  simp only [dcylCarrier, Finset.mem_biUnion] at hi ⊢
  obtain ⟨a, ha, hia⟩ := hi
  exact ⟨a, h ha, hia⟩

theorem dcylCarrier_subset_compl_of_boundary {n m : ℕ}
    {S : Finset (DV n m)} {i : Fin (n + 1)}
    (hiTop : DV.top i ∉ S)
    (hiMid : ∀ T, DV.mid T ∈ S → i ∉ T) : dcylCarrier S ⊆ {i}ᶜ := by
  intro j hj
  simp only [dcylCarrier, Finset.mem_biUnion] at hj
  obtain ⟨a, ha, hja⟩ := hj
  simp only [Finset.mem_compl, Finset.mem_singleton]
  intro hji
  subst j
  cases a with
  | top k =>
      simp only [Finset.mem_singleton] at hja
      subst k
      exact hiTop ha
  | mid T => exact (hiMid T ha) hja
  | bot c => simp at hja

theorem dcylCarrier_card_le_of_boundary {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    {S : Finset (DV n m)} (hS : (dcylDBoundaryComplex v).S S)
    (hnot : ¬ ∀ a ∈ S, ∃ c, a = DV.bot c) : (dcylCarrier S).card ≤ n := by
  rcases hS.2 with hbot | ⟨i, hiTop, hiMid⟩
  · exact (hnot hbot).elim
  · have hsub := dcylCarrier_subset_compl_of_boundary hiTop hiMid
    calc
      (dcylCarrier S).card ≤ ({i}ᶜ : Finset (Fin (n + 1))).card := Finset.card_le_card hsub
      _ = n := by simp [Finset.card_compl]

theorem dcylCarrier_nonempty_of_not_bottom {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    {S : Finset (DV n m)} (hS : (dcylDComplex v).S S)
    (hnot : ¬ ∀ a ∈ S, ∃ c, a = DV.bot c) : (dcylCarrier S).Nonempty := by
  by_contra hne
  have hzero : dcylCarrier S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  apply hnot
  intro a ha
  cases a with
  | top i =>
      have hi := mem_dcylCarrier_top ha
      rw [hzero] at hi
      simp at hi
  | mid T =>
      have hT := hS.1 T ha
      obtain ⟨i, hi⟩ := hT
      have hi' := subset_dcylCarrier_mid ha hi
      rw [hzero] at hi'
      simp at hi'
  | bot c => exact ⟨c, rfl⟩

def faceDim {n : ℕ} (F : Finset (Fin (n + 1))) : ℕ := F.card - 1

noncomputable def faceEmb {n : ℕ} (F : Finset (Fin (n + 1))) (hF : F.Nonempty) :
    Fin (faceDim F + 1) ↪o Fin (n + 1) :=
  F.orderEmbOfFin (by
    have hp : 0 < F.card := Finset.card_pos.mpr hF
    dsimp [faceDim]
    omega)

theorem faceEmb_image {n : ℕ} (F : Finset (Fin (n + 1))) (hF : F.Nonempty) :
    Finset.univ.image (faceEmb F hF) = F := by
  have hp : 0 < F.card := Finset.card_pos.mpr hF
  simpa [faceEmb] using
    (Finset.image_orderEmbOfFin_univ F (k := faceDim F + 1) (by
      dsimp [faceDim]
      omega))

noncomputable def faceHom {n : ℕ} (F : Finset (Fin (n + 1))) (hF : F.Nonempty) :
    Henry.SemiSimplexCategory.mk (faceDim F) ⟶ Henry.SemiSimplexCategory.mk n :=
  vhom (faceEmb F hF) (faceEmb F hF).strictMono

theorem faceHom_ne {n : ℕ} (F : Finset (Fin (n + 1))) (hF : F.Nonempty)
    (hFcard : F.card ≤ n) : faceDim F ≠ n := by
  have hp : 0 < F.card := Finset.card_pos.mpr hF
  dsimp [faceDim]
  omega

noncomputable def invOn {α β : Type} [Nonempty α] (f : α → β) (b : β) : α := by
  classical
  exact if h : ∃ a, f a = b then h.choose else Classical.choice ‹Nonempty α›

theorem invOn_spec {α β : Type} [Nonempty α] (f : α → β) (b : β)
    (hb : ∃ a, f a = b) : f (invOn f b) = b := by
  classical
  simp [invOn, hb, hb.choose_spec]

noncomputable def faceFactor {n : ℕ} (F G : Finset (Fin (n + 1)))
    (hF : F.Nonempty) (hG : G.Nonempty) (hGF : G ⊆ F) :
    Fin (faceDim G + 1) ↪o Fin (faceDim F + 1) := by
  let f : Fin (faceDim G + 1) → Fin (faceDim F + 1) :=
    fun j => invOn (faceEmb F hF) (faceEmb G hG j)
  have hspec : ∀ j, faceEmb F hF (f j) = faceEmb G hG j := by
    intro j
    apply invOn_spec
    have hjG : faceEmb G hG j ∈ G := by
      simpa [faceEmb] using Finset.orderEmbOfFin_mem G
        (k := faceDim G + 1) (by
          have hp : 0 < G.card := Finset.card_pos.mpr hG
          dsimp [faceDim]
          omega) j
    have hjF : faceEmb G hG j ∈ F := hGF hjG
    have hjImg : faceEmb G hG j ∈ Finset.univ.image (faceEmb F hF) := by
      rw [faceEmb_image]
      exact hjF
    rw [Finset.mem_image] at hjImg
    obtain ⟨i, -, hji⟩ := hjImg
    exact ⟨i, hji⟩
  have hstrict : StrictMono f := by
    intro i j hij
    apply lt_of_not_ge
    intro hji
    have hleft : faceEmb F hF (f i) < faceEmb F hF (f j) := by
      rw [hspec i, hspec j]
      exact (faceEmb G hG).strictMono hij
    have hright : faceEmb F hF (f j) ≤ faceEmb F hF (f i) :=
      (faceEmb F hF).monotone hji
    exact (not_le_of_gt hleft) hright
  exact OrderEmbedding.ofStrictMono f hstrict

theorem faceEmb_factor {n : ℕ} (F G : Finset (Fin (n + 1)))
    (hF : F.Nonempty) (hG : G.Nonempty) (hGF : G ⊆ F) (j : Fin (faceDim G + 1)) :
    faceEmb F hF (faceFactor F G hF hG hGF j) = faceEmb G hG j := by
  exact invOn_spec (faceEmb F hF) (faceEmb G hG j) (by
    have hjG : faceEmb G hG j ∈ G := by
      simpa [faceEmb] using Finset.orderEmbOfFin_mem G
        (k := faceDim G + 1) (by
          have hp : 0 < G.card := Finset.card_pos.mpr hG
          dsimp [faceDim]
          omega) j
    have hjF : faceEmb G hG j ∈ F := hGF hjG
    have hjImg : faceEmb G hG j ∈ Finset.univ.image (faceEmb F hF) := by
      rw [faceEmb_image]
      exact hjF
    rw [Finset.mem_image] at hjImg
    obtain ⟨i, -, hji⟩ := hjImg
    exact ⟨i, hji⟩)

noncomputable def faceFactorHom {n : ℕ} (F G : Finset (Fin (n + 1)))
    (hF : F.Nonempty) (hG : G.Nonempty) (hGF : G ⊆ F) :
    Henry.SemiSimplexCategory.mk (faceDim G) ⟶ Henry.SemiSimplexCategory.mk (faceDim F) :=
  vhom (faceFactor F G hF hG hGF) (faceFactor F G hF hG hGF).strictMono

theorem faceHom_factor {n : ℕ} (F G : Finset (Fin (n + 1)))
    (hF : F.Nonempty) (hG : G.Nonempty) (hGF : G ⊆ F) :
    faceHom G hG = faceFactorHom F G hF hG hGF ≫ faceHom F hF := by
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  exact (faceEmb_factor F G hF hG hGF j).symm

theorem faceMap_comp {W : SemiSSet.{u}} {n p q : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (θF : Henry.SemiSimplexCategory.mk p ⟶ Henry.SemiSimplexCategory.mk n)
    (θG : Henry.SemiSimplexCategory.mk q ⟶ Henry.SemiSimplexCategory.mk n)
    (ρ : Henry.SemiSimplexCategory.mk q ⟶ Henry.SemiSimplexCategory.mk p)
    (hθ : θG = ρ ≫ θF) :
    W.map ρ.op (W.map θF.op y) = W.map θG.op y := by
  rw [hθ, op_comp, W.map_comp]
  rfl

theorem semiEmb_comp {a b c : ℕ}
    (f : Henry.SemiSimplexCategory.mk a ⟶ Henry.SemiSimplexCategory.mk b)
    (g : Henry.SemiSimplexCategory.mk b ⟶ Henry.SemiSimplexCategory.mk c) :
    semiEmb (f ≫ g) = (semiEmb f).trans (semiEmb g) := by
  ext i
  rfl

theorem elι_factor_of_faces {X W : SemiSSet.{u}} (φ : W ⟶ sharp X) {n p q : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (θF : Henry.SemiSimplexCategory.mk p ⟶ Henry.SemiSimplexCategory.mk n)
    (θG : Henry.SemiSimplexCategory.mk q ⟶ Henry.SemiSimplexCategory.mk n)
    (ρ : Henry.SemiSimplexCategory.mk q ⟶ Henry.SemiSimplexCategory.mk p)
    (hθ : θG = ρ ≫ θF)
    (hzg : W.map ρ.op (W.map θF.op y) = W.map θG.op y) :
    elι φ (elFaceHom y θG) =
      elι φ (show elOf (W.map θF.op y) ⟶ elOf (W.map θG.op y) from
        ⟨ρ.op, hzg⟩) ≫ elι φ (elFaceHom y θF) := by
  let zF := W.map θF.op y
  let zG := W.map θG.op y
  let g : elOf zF ⟶ elOf zG := ⟨ρ.op, hzg⟩
  have hF := (elι_spec φ (elFaceHom y θF)).1
  have hG := (elι_spec φ (elFaceHom y θG)).1
  have hR := (elι_spec φ g).1
  have hθfun : θG.1.toOrderHom = θF.1.toOrderHom ∘ ρ.1.toOrderHom := by
    funext j
    simpa using congrFun (congrArg (fun f => f.1.toOrderHom) hθ) j
  have hR' : (elNF φ (elOf zF)).v ∘ ρ.1.toOrderHom =
      (elι φ g).1.toOrderHom ∘ (elNF φ (elOf zG)).v := by
    simpa [elFace, g] using hR
  apply semiSimplex_hom_ext_of_surjective (elNF φ (elOf zG)).v
    (elNF φ (elOf zG)).surj
  funext j
  change (elι φ (elFaceHom y θG)).1.toOrderHom ((elNF φ (elOf zG)).v j) =
    (elι φ g ≫ elι φ (elFaceHom y θF)).1.toOrderHom ((elNF φ (elOf zG)).v j)
  calc
    (elι φ (elFaceHom y θG)).1.toOrderHom ((elNF φ (elOf zG)).v j) =
        (elNF φ (elOf y)).v (θG.1.toOrderHom j) := (congrFun hG j).symm
    _ = (elNF φ (elOf y)).v (θF.1.toOrderHom (ρ.1.toOrderHom j)) := by
      rw [hθfun]
      rfl
    _ = (elι φ (elFaceHom y θF)).1.toOrderHom
        ((elNF φ (elOf zF)).v (ρ.1.toOrderHom j)) :=
      congrFun hF (ρ.1.toOrderHom j)
    _ = (elι φ (elFaceHom y θF)).1.toOrderHom
        ((elι φ g).1.toOrderHom ((elNF φ (elOf zG)).v j)) := by
      have hRj := congrFun hR' j
      simp only [Function.comp_apply] at hRj
      rw [hRj]
    _ = (elι φ g ≫ elι φ (elFaceHom y θF)).1.toOrderHom
        ((elNF φ (elOf zG)).v j) := rfl

def pullFinset {a b : ℕ} (e : Fin a ↪ Fin b) (S : Finset (Fin b)) : Finset (Fin a) :=
  Finset.univ.filter fun i => e i ∈ S

theorem map_pullFinset {a b : ℕ} (e : Fin a ↪ Fin b) (S : Finset (Fin b))
    (hS : S ⊆ Finset.univ.image e) : Finset.map e (pullFinset e S) = S := by
  classical
  ext x
  simp only [Finset.mem_map, pullFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    have hxe : x ∈ Finset.univ.image e := hS hx
    rw [Finset.mem_image] at hxe
    obtain ⟨i, -, hix⟩ := hxe
    refine ⟨i, ?_, hix⟩
    simpa [hix] using hx

theorem mapV_injective {n m n' m' : ℕ} (θ : Fin (n' + 1) ↪ Fin (n + 1))
    (ι : Fin (m' + 1) ↪ Fin (m + 1)) :
    Function.Injective (DV.mapV θ ι : DV n' m' → DV n m) := by
  intro a b hab
  cases a with
  | top i =>
    cases b with
    | top j =>
      simp only [DV.mapV, DV.top.injEq] at hab
      exact congrArg DV.top (θ.injective hab)
    | mid S => cases hab
    | bot c => cases hab
  | mid S =>
    cases b with
    | top j => cases hab
    | mid T =>
      simp only [DV.mapV, DV.mid.injEq] at hab
      exact congrArg DV.mid (Finset.map_injective θ hab)
    | bot c => cases hab
  | bot c =>
    cases b with
    | top j => cases hab
    | mid T => cases hab
    | bot d =>
      simp only [DV.mapV, DV.bot.injEq] at hab
      exact congrArg DV.bot (ι.injective hab)

theorem mapV_comp {n m n' m' n'' m'' : ℕ}
    (θ : Fin (n' + 1) ↪ Fin (n + 1)) (ι : Fin (m' + 1) ↪ Fin (m + 1))
    (θ' : Fin (n'' + 1) ↪ Fin (n' + 1)) (ι' : Fin (m'' + 1) ↪ Fin (m' + 1)) :
    DV.mapV θ ι ∘ DV.mapV θ' ι' = DV.mapV (θ'.trans θ) (ι'.trans ι) := by
  funext a
  cases a <;> simp [DV.mapV, Finset.map_map]

noncomputable def pullDV {n m n' m' : ℕ}
    (θ : Fin (n' + 1) ↪ Fin (n + 1)) (ι : Fin (m' + 1) ↪ Fin (m + 1)) :
    DV n m → DV n' m'
  | .top i => .top (invOn θ i)
  | .mid S => .mid (pullFinset θ S)
  | .bot c => .bot (invOn ι c)

theorem mapV_pullDV_top {n m n' m' : ℕ} (θ : Fin (n' + 1) ↪ Fin (n + 1))
    (ι : Fin (m' + 1) ↪ Fin (m + 1)) {i : Fin (n + 1)}
    (hi : ∃ j, θ j = i) : DV.mapV θ ι (pullDV θ ι (.top i)) = .top i := by
  simp only [pullDV, DV.mapV, DV.top.injEq]
  exact invOn_spec θ i hi

theorem mapV_pullDV_mid {n m n' m' : ℕ} (θ : Fin (n' + 1) ↪ Fin (n + 1))
    (ι : Fin (m' + 1) ↪ Fin (m + 1)) {S : Finset (Fin (n + 1))}
    (hS : S ⊆ Finset.univ.image θ) :
    DV.mapV θ ι (pullDV θ ι (.mid S)) = .mid S := by
  simp only [pullDV, DV.mapV, DV.mid.injEq]
  exact map_pullFinset θ S hS

theorem mapV_pullDV_bot {n m n' m' : ℕ} (θ : Fin (n' + 1) ↪ Fin (n + 1))
    (ι : Fin (m' + 1) ↪ Fin (m + 1)) {c : Fin (m + 1)}
    (hc : ∃ d, ι d = c) : DV.mapV θ ι (pullDV θ ι (.bot c)) = .bot c := by
  simp only [pullDV, DV.mapV, DV.bot.injEq]
  exact invOn_spec ι c hc

theorem finsetMap_subset_reflect {a b : ℕ} (e : Fin a ↪ Fin b)
    {S T : Finset (Fin a)} (h : Finset.map e S ⊆ Finset.map e T) : S ⊆ T := by
  intro i hi
  have hie : e i ∈ Finset.map e S := Finset.mem_map.mpr ⟨i, hi, rfl⟩
  have hit : e i ∈ Finset.map e T := h hie
  obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hit
  exact e.injective hji ▸ hj

theorem pullComplex {n m n' m' : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    {v' : Fin (n' + 1) → Fin (m' + 1)}
    (θ : Fin (n' + 1) ↪ Fin (n + 1))
    (ι : Fin (m' + 1) ↪ Fin (m + 1))
    (hv : v ∘ θ = ι ∘ v') {R : Finset (DV n m)}
    (hR : (dcylDComplex v).S R) (pull : DV n m → DV n' m')
    (hp : ∀ a ∈ R, DV.mapV θ ι (pull a) = a) :
    (dcylDComplex v').S (R.image pull) := by
  classical
  have hpull {a : DV n' m'} (ha : a ∈ R.image pull) : DV.mapV θ ι a ∈ R := by
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
    rw [← hba, hp b hb]
    exact hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T hT
    have hT' : DV.mid (Finset.map θ T) ∈ R := by
      simpa [DV.mapV] using hpull hT
    exact Finset.map_nonempty.mp (hR.1 _ hT')
  · intro T U hT hU
    have hT' : DV.mid (Finset.map θ T) ∈ R := by
      simpa [DV.mapV] using hpull hT
    have hU' : DV.mid (Finset.map θ U) ∈ R := by
      simpa [DV.mapV] using hpull hU
    rcases hR.2.1 _ _ hT' hU' with h | h
    · exact Or.inl (finsetMap_subset_reflect θ h)
    · exact Or.inr (finsetMap_subset_reflect θ h)
  · intro i c hi hc
    have hi' : DV.top (θ i) ∈ R := by simpa [DV.mapV] using hpull hi
    have hc' : DV.bot (ι c) ∈ R := by simpa [DV.mapV] using hpull hc
    exact hR.2.2.1 _ _ hi' hc'
  · intro i T hi hT
    have hi' : DV.top (θ i) ∈ R := by simpa [DV.mapV] using hpull hi
    have hT' : DV.mid (Finset.map θ T) ∈ R := by
      simpa [DV.mapV] using hpull hT
    have hmem := hR.2.2.2.1 _ _ hi' hT'
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hmem
    simpa [θ.injective hji] using hj
  · intro c T hc hT
    have hc' : DV.bot (ι c) ∈ R := by simpa [DV.mapV] using hpull hc
    have hT' : DV.mid (Finset.map θ T) ∈ R := by
      simpa [DV.mapV] using hpull hT
    obtain ⟨k, hk, hvk⟩ := hR.2.2.2.2 _ _ hc' hT'
    obtain ⟨j, hj, hjk⟩ := Finset.mem_map.mp hk
    have hvj := congrFun hv j
    simp only [Function.comp_apply] at hvj
    have heq : ι (v' j) = ι c := by
      calc
        ι (v' j) = v (θ j) := hvj.symm
        _ = ι c := by simpa [hjk] using hvk
    exact ⟨j, hj, ι.injective heq⟩

theorem pullSimplex {n m n' m' k : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    {v' : Fin (n' + 1) → Fin (m' + 1)}
    (θ : Fin (n' + 1) ↪ Fin (n + 1)) (hθ : StrictMono θ)
    (ι : Fin (m' + 1) ↪ Fin (m + 1)) (hι : StrictMono ι)
    (hv : v ∘ θ = ι ∘ v') (R : Finset (DV n m))
    (hR : (dcylDComplex v).S R) (w : Fin (k + 1) → DV n m)
    (hRset : R = Finset.univ.image w)
    (hw : StrictMono w) (pull : DV n m → DV n' m')
    (hp : ∀ j, DV.mapV θ ι (pull (w j)) = w j) :
    StrictMono (pull ∘ w) ∧ (dcylDComplex v').S (Finset.univ.image (pull ∘ w)) := by
  classical
  let w' : Fin (k + 1) → DV n' m' := pull ∘ w
  have hR' : ∀ a ∈ R, DV.mapV θ ι (pull a) = a := by
    intro a ha
    rw [hRset] at ha
    obtain ⟨j, -, hja⟩ := Finset.mem_image.mp ha
    subst a
    exact hp j
  have hlocal : (dcylDComplex v').S (R.image pull) :=
    pullComplex θ ι hv hR pull hR'
  have hlocalSet : Finset.univ.image w' = R.image pull := by
    rw [hRset]
    dsimp [w']
    exact (Finset.image_image).symm
  have hlocal' : (dcylDComplex v').S (Finset.univ.image w') := by
    rw [hlocalSet]
    exact hlocal
  have hmapStrict := (dcylDMapHom θ hθ ι hι hv).strictMonoOn _ hlocal'
  refine ⟨?_, hlocal'⟩
  intro i j hij
  have htarget : DV.mapV θ ι (w' i) < DV.mapV θ ι (w' j) := by
    change DV.mapV θ ι (pull (w i)) < DV.mapV θ ι (pull (w j))
    rw [hp i, hp j]
    exact hw hij
  by_contra hnot
  have hne : w' i ≠ w' j := by
    intro heq
    rw [heq] at htarget
    exact (lt_irrefl _ htarget)
  have hrev : w' j < w' i := lt_of_le_of_ne (le_of_not_gt hnot) hne.symm
  have hmapRev := hmapStrict (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    (Finset.mem_image_of_mem _ (Finset.mem_univ i)) hrev
  exact (lt_asymm htarget hmapRev)

theorem exists_mid_of_bot_nonbottom {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    {R : Finset (DV n m)} (hR : (dcylDComplex v).S R)
    (hnot : ¬ ∀ a ∈ R, ∃ c, a = DV.bot c) {c : Fin (m + 1)} (hc : DV.bot c ∈ R) :
    ∃ T, DV.mid T ∈ R := by
  classical
  by_contra hmid
  have hnoMid : ∀ T, DV.mid T ∉ R := by
    intro T hT
    exact hmid ⟨T, hT⟩
  have hnoTop : ∀ i, DV.top i ∉ R := by
    intro i hi
    exact (hR.2.2.1 i c hi hc).elim
  apply hnot
  intro a ha
  cases a with
  | top i => exact (hnoTop i ha).elim
  | mid T => exact (hnoMid T ha).elim
  | bot d => exact ⟨d, rfl⟩

noncomputable def bottomCarrierMap {X Y : SemiSSet.{u}} (g : X ⟶ Y) {m k : ℕ}
    (x : X.obj (op (Henry.SemiSimplexCategory.mk m)))
    (c : Fin (k + 1) → Fin (m + 1)) (hc : StrictMono c) :
    stdSimplex.obj (Henry.SemiSimplexCategory.mk k) ⟶ Y :=
  uliftYonedaEquiv.symm (X.map (vhom c hc).op x) ≫ g

theorem bottomCarrierMap_precomp {X Y : SemiSSet.{u}} (g : X ⟶ Y) {m k l : ℕ}
    (x : X.obj (op (Henry.SemiSimplexCategory.mk m)))
    (α : Henry.SemiSimplexCategory.mk l ⟶ Henry.SemiSimplexCategory.mk k)
    (c : Fin (k + 1) → Fin (m + 1)) (hc : StrictMono c)
    (d : Fin (l + 1) → Fin (m + 1)) (hd : StrictMono d)
    (hcd : d = c ∘ α.1.toOrderHom) :
    Henry.SemiSSet.stdSimplex.map α ≫ bottomCarrierMap g x c hc =
      bottomCarrierMap g x d hd := by
  have hmap : vhom d hd = α ≫ vhom c hc := by
    apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    exact congrFun hcd j
  unfold bottomCarrierMap
  rw [uliftYonedaEquiv_symm_map, uliftYonedaEquiv_symm_map]
  calc
    Henry.SemiSSet.stdSimplex.map α ≫
        (Henry.SemiSSet.stdSimplex.map (vhom c hc) ≫ uliftYonedaEquiv.symm x) ≫ g =
      (Henry.SemiSSet.stdSimplex.map α ≫ Henry.SemiSSet.stdSimplex.map (vhom c hc)) ≫
        uliftYonedaEquiv.symm x ≫ g := by simp [Category.assoc]
    _ = Henry.SemiSSet.stdSimplex.map (α ≫ vhom c hc) ≫ uliftYonedaEquiv.symm x ≫ g := by
      rw [← Henry.SemiSSet.stdSimplex.map_comp]
    _ = Henry.SemiSSet.stdSimplex.map (vhom d hd) ≫ uliftYonedaEquiv.symm x ≫ g := by
      rw [← hmap]

def botCode {n m k : ℕ} (w : Fin (k + 1) → DV n m) : Fin (k + 1) → Fin (m + 1) :=
  fun j => match w j with
    | .top _ => 0
    | .mid _ => 0
    | .bot c => c

theorem botCode_spec {n m k : ℕ} {w : Fin (k + 1) → DV n m}
    (hbot : ∀ a ∈ Finset.univ.image w, ∃ c, a = DV.bot c) (j : Fin (k + 1)) :
    w j = DV.bot (botCode w j) := by
  obtain ⟨c, hc⟩ := hbot (w j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  cases h : w j with
  | top i =>
      have hEq : DV.top i = DV.bot c := by simpa [h] using hc
      cases hEq
  | mid S =>
      have hEq : DV.mid S = DV.bot c := by simpa [h] using hc
      cases hEq
  | bot d => simpa [botCode, h] using hc

theorem botCode_strict {n m k : ℕ} {w : Fin (k + 1) → DV n m}
    (hbot : ∀ a ∈ Finset.univ.image w, ∃ c, a = DV.bot c) (hw : StrictMono w) :
    StrictMono (botCode w) := by
  intro i j hij
  apply DV.bot_lt_bot.1
  rw [← botCode_spec hbot i, ← botCode_spec hbot j]
  exact hw hij

noncomputable def faceCarrierDesc {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)
    (A : Subfunctor W) {n : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    {q : ℕ} (θ : Henry.SemiSimplexCategory.mk q ⟶ Henry.SemiSimplexCategory.mk n)
    (hθ : q ≠ n) (hz : W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk q)))
    {k : ℕ} (w : Fin (k + 1) → DV q (elNF φ (elOf (W.map θ.op y))).m)
    (hw : StrictMono w)
    (hS : (dcylDComplex (elNF φ (elOf (W.map θ.op y))).v).S
      (Finset.univ.image w)) :
    stdSimplex.obj (Henry.SemiSimplexCategory.mk k) ⟶ (cylSub φ A).obj := by
  let z := W.map θ.op y
  let zA : A.toFunctor.Elements := A.toFunctor.elementsMk _ ⟨z, hz⟩
  exact ((dcylDComplex (elNF φ (elOf z)).v).simplexMap w hw hS) ≫
    colimit.ι (cylSub φ A).DC (op zA) ≫ (cylSub φ A).incl

theorem faceCarrierDesc_precomp {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)
    (A : Subfunctor W) {n p q k l : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (θF : Henry.SemiSimplexCategory.mk p ⟶ Henry.SemiSimplexCategory.mk n)
    (θG : Henry.SemiSimplexCategory.mk q ⟶ Henry.SemiSimplexCategory.mk n)
    (ρ : Henry.SemiSimplexCategory.mk q ⟶ Henry.SemiSimplexCategory.mk p)
    (hθ : θG = ρ ≫ θF)
    (hθF : p ≠ n) (hθG : q ≠ n)
    (hzF : W.map θF.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk p)))
    (hzG : W.map θG.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk q)))
    (hzg : W.map ρ.op (W.map θF.op y) = W.map θG.op y)
    (α : Henry.SemiSimplexCategory.mk l ⟶ Henry.SemiSimplexCategory.mk k)
    (wF : Fin (k + 1) → DV p (elNF φ (elOf (W.map θF.op y))).m)
    (hwF : StrictMono wF)
    (hSF : (dcylDComplex (elNF φ (elOf (W.map θF.op y))).v).S
      (Finset.univ.image wF))
    (wG : Fin (l + 1) → DV q (elNF φ (elOf (W.map θG.op y))).m)
    (hwG : StrictMono wG)
    (hSG : (dcylDComplex (elNF φ (elOf (W.map θG.op y))).v).S
      (Finset.univ.image wG))
    (hfun : (dcylDElMap φ
      (show elOf (W.map θF.op y) ⟶ elOf (W.map θG.op y) from ⟨ρ.op, hzg⟩)).f ∘ wG =
        wF ∘ α.1.toOrderHom) :
    Henry.SemiSSet.stdSimplex.map α ≫
        faceCarrierDesc φ A y θF hθF hzF wF hwF hSF =
      faceCarrierDesc φ A y θG hθG hzG wG hwG hSG := by
  let zF := W.map θF.op y
  let zG := W.map θG.op y
  let eF : A.toFunctor.Elements := A.toFunctor.elementsMk _ ⟨zF, hzF⟩
  let eG : A.toFunctor.Elements := A.toFunctor.elementsMk _ ⟨zG, hzG⟩
  let gA : eF ⟶ eG := ⟨ρ.op, by
    apply Subtype.ext
    exact hzg⟩
  let gW : elOf zF ⟶ elOf zG := ⟨ρ.op, hzg⟩
  let q := dcylDElMap φ gW
  have hPreStrict := hwF.comp (SemiSimplexCategory.strictMono α)
  have hPreS : (dcylDComplex (elNF φ (elOf zF)).v).S
      (Finset.univ.image (wF ∘ α.1.toOrderHom)) := by
    apply (dcylDComplex (elNF φ (elOf zF)).v).down _ hSF
    intro a ha
    obtain ⟨i, -, hia⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨α.1.toOrderHom i, Finset.mem_univ _, by simpa using hia⟩
  have hQStrict : StrictMono (q.f ∘ wG) := by
    intro i j hij
    apply q.strictMonoOn _ hSG
    · exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    · exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
    · exact hwG hij
  have hQS : (dcylDComplex (elNF φ (elOf zF)).v).S
      (Finset.univ.image (q.f ∘ wG)) := by
    simpa [Finset.image_image] using q.map_S _ hSG
  have hmapEq : (dcylDComplex (elNF φ (elOf zF)).v).simplexMap
      (wF ∘ α.1.toOrderHom) hPreStrict hPreS =
      (dcylDComplex (elNF φ (elOf zF)).v).simplexMap (q.f ∘ wG) hQStrict hQS :=
    simplexMap_congr hfun.symm hPreStrict hPreS hQStrict hQS
  have hsimplex : Henry.SemiSSet.stdSimplex.map α ≫
      (dcylDComplex (elNF φ (elOf zF)).v).simplexMap wF hwF hSF =
      (dcylDComplex (elNF φ (elOf zG)).v).simplexMap wG hwG hSG ≫ q.toSemiSSet := by
    calc
      Henry.SemiSSet.stdSimplex.map α ≫
          (dcylDComplex (elNF φ (elOf zF)).v).simplexMap wF hwF hSF =
        (dcylDComplex (elNF φ (elOf zF)).v).simplexMap (wF ∘ α.1.toOrderHom)
          hPreStrict hPreS :=
          simplexMap_precomp α wF hwF hSF
      _ = (dcylDComplex (elNF φ (elOf zF)).v).simplexMap (q.f ∘ wG) hQStrict hQS := hmapEq
      _ = (dcylDComplex (elNF φ (elOf zG)).v).simplexMap wG hwG hSG ≫ q.toSemiSSet :=
          (simplexMap_compHom q wG hwG hSG).symm
  have hcol : (cylSub φ A).DC.map (Opposite.op gA) ≫
      colimit.ι (cylSub φ A).DC (Opposite.op eF) =
        colimit.ι (cylSub φ A).DC (Opposite.op eG) :=
    colimit.w (cylSub φ A).DC (Opposite.op gA)
  have hq : q.toSemiSSet = (cylSub φ A).DC.map (Opposite.op gA) := by rfl
  have hFaceF : faceCarrierDesc φ A y θF hθF hzF wF hwF hSF =
      (dcylDComplex (elNF φ (elOf zF)).v).simplexMap wF hwF hSF ≫
        colimit.ι (cylSub φ A).DC (Opposite.op eF) ≫ (cylSub φ A).incl := by rfl
  have hFaceG : faceCarrierDesc φ A y θG hθG hzG wG hwG hSG =
      (dcylDComplex (elNF φ (elOf zG)).v).simplexMap wG hwG hSG ≫
        colimit.ι (cylSub φ A).DC (Opposite.op eG) ≫ (cylSub φ A).incl := by rfl
  have hpost :
      ((Henry.SemiSSet.stdSimplex.map α ≫
          (dcylDComplex (elNF φ (elOf zF)).v).simplexMap wF hwF hSF) ≫
          colimit.ι (cylSub φ A).DC (Opposite.op eF)) ≫ (cylSub φ A).incl =
        (((dcylDComplex (elNF φ (elOf zG)).v).simplexMap wG hwG hSG ≫ q.toSemiSSet) ≫
          colimit.ι (cylSub φ A).DC (Opposite.op eF)) ≫ (cylSub φ A).incl :=
    congrArg (fun f => f ≫ (cylSub φ A).incl)
      (congrArg (fun f => f ≫ colimit.ι (cylSub φ A).DC (Opposite.op eF)) hsimplex)
  have hqi : q.toSemiSSet ≫ colimit.ι (cylSub φ A).DC (Opposite.op eF) =
      colimit.ι (cylSub φ A).DC (Opposite.op eG) :=
    (congrArg (fun f => f ≫ colimit.ι (cylSub φ A).DC (Opposite.op eF)) hq).trans hcol
  calc
    Henry.SemiSSet.stdSimplex.map α ≫ faceCarrierDesc φ A y θF hθF hzF wF hwF hSF =
        ((Henry.SemiSSet.stdSimplex.map α ≫
          (dcylDComplex (elNF φ (elOf zF)).v).simplexMap wF hwF hSF) ≫
          colimit.ι (cylSub φ A).DC (Opposite.op eF)) ≫ (cylSub φ A).incl := by
      rw [hFaceF]
      calc
        Henry.SemiSSet.stdSimplex.map α ≫
            ((dcylDComplex (elNF φ (elOf zF)).v).simplexMap wF hwF hSF ≫
              colimit.ι (cylSub φ A).DC (Opposite.op eF) ≫ (cylSub φ A).incl) =
          (Henry.SemiSSet.stdSimplex.map α ≫
            (dcylDComplex (elNF φ (elOf zF)).v).simplexMap wF hwF hSF) ≫
              (colimit.ι (cylSub φ A).DC (Opposite.op eF) ≫ (cylSub φ A).incl) :=
                by cat_disch
        _ = ((Henry.SemiSSet.stdSimplex.map α ≫
            (dcylDComplex (elNF φ (elOf zF)).v).simplexMap wF hwF hSF) ≫
              colimit.ι (cylSub φ A).DC (Opposite.op eF)) ≫ (cylSub φ A).incl := by cat_disch
    _ = (((dcylDComplex (elNF φ (elOf zG)).v).simplexMap wG hwG hSG ≫ q.toSemiSSet) ≫
          colimit.ι (cylSub φ A).DC (Opposite.op eF)) ≫ (cylSub φ A).incl := hpost
    _ = ((dcylDComplex (elNF φ (elOf zG)).v).simplexMap wG hwG hSG ≫
          (q.toSemiSSet ≫ colimit.ι (cylSub φ A).DC (Opposite.op eF))) ≫
          (cylSub φ A).incl := by cat_disch
    _ = (dcylDComplex (elNF φ (elOf zG)).v).simplexMap wG hwG hSG ≫
          colimit.ι (cylSub φ A).DC (Opposite.op eG) ≫ (cylSub φ A).incl := by
      rw [hqi]
      cat_disch
    _ = faceCarrierDesc φ A y θG hθG hzG wG hwG hSG := by
      rw [hFaceG]

theorem cylDatum_botCondition {X : SemiSSet.{u}} {I : Type u} [Category.{0} I]
    (D : CylDatum X I) (i : I) :
    D.botN.app i ≫ colimit.ι D.DC i ≫ D.incl = D.xN.app i ≫ D.base := by
  have h := pushout.condition
    (f := colimit.desc D.B (Cocone.mk X D.xN)) (g := colimMap D.botN)
  have h := congrArg (fun k => colimit.ι D.B i ≫ k) h
  simp only [colimit.ι_desc_assoc, ι_colimMap_assoc] at h
  exact h.symm

theorem simplexMap_bottom_factor {n m k l : ℕ}
    {v : Fin (n + 1) → Fin (m + 1)}
    (α : Henry.SemiSimplexCategory.mk l ⟶ Henry.SemiSimplexCategory.mk k)
    (w : Fin (k + 1) → DV n m) (hw : StrictMono w)
    (hS : (dcylDComplex v).S (Finset.univ.image w))
    (c : Fin (l + 1) → Fin (m + 1)) (hc : StrictMono c)
    (hlist : w ∘ α.1.toOrderHom = fun j => DV.bot (c j)) :
    Henry.SemiSSet.stdSimplex.map α ≫
        (dcylDComplex v).simplexMap w hw hS =
      Henry.SemiSSet.stdSimplex.map (vhom c hc) ≫ dcylDBot v := by
  let b : Fin (m + 1) → DV n m := fun i => DV.bot i
  have hb : StrictMono b := by
    intro i j hij
    exact DV.bot_lt_bot.2 hij
  have hbS : (dcylDComplex v).S (Finset.univ.image b) :=
    ⟨by simp, by simp, by simp, by simp, by simp⟩
  have hpre := simplexMap_precomp α w hw hS
  have hbotpre := simplexMap_precomp (vhom c hc) b hb hbS
  have hsame : w ∘ α.1.toOrderHom = b ∘ c := by
    funext j
    exact congrFun hlist j
  unfold dcylDBot
  calc
    Henry.SemiSSet.stdSimplex.map α ≫
        (dcylDComplex v).simplexMap w hw hS =
      (dcylDComplex v).simplexMap (w ∘ α.1.toOrderHom)
        (hw.comp (SemiSimplexCategory.strictMono α)) _ := hpre
    _ = (dcylDComplex v).simplexMap (b ∘ c) _ _ := by
      apply simplexMap_congr hsame
    _ = Henry.SemiSSet.stdSimplex.map (vhom c hc) ≫
        (dcylDComplex v).simplexMap b hb hbS := hbotpre.symm

noncomputable def boundarySimplexDesc {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)
    (A : Subfunctor W) {n : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hfaces : ∀ (k : ℕ) (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n),
      k ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)))
    {k : ℕ}
    (σ : ULift ((dcylDBoundaryComplex (elNF φ (elOf y)).v).Simplex k)) :
    stdSimplex.obj (Henry.SemiSimplexCategory.mk k) ⟶ (cylSub φ A).obj := by
  classical
  let nf0 := elNF φ (elOf y)
  let v0 := nf0.v
  let m0 := nf0.m
  let w := σ.down.1
  let R := Finset.univ.image w
  let hbdry : (dcylDBoundaryComplex v0).S R := by
    simpa [v0, w, R, nf0] using σ.down.2.2
  by_cases hbot : ∀ a ∈ R, ∃ c, a = DV.bot c
  · let c : Fin (k + 1) → Fin (m0 + 1) := fun j =>
      botCode w j
    have hc : StrictMono c := botCode_strict hbot σ.down.2.1
    exact bottomCarrierMap (cylSub φ A).base (elNF φ (elOf y)).x c hc
  · have hnot : ¬ ∀ a ∈ R, ∃ c, a = DV.bot c := hbot
    have hR : (dcylDComplex v0).S R := hbdry.1
    let F := dcylCarrier R
    have hF : F.Nonempty := dcylCarrier_nonempty_of_not_bottom hR hnot
    have hFcard : F.card ≤ n := dcylCarrier_card_le_of_boundary hbdry hnot
    have hθn : faceDim F ≠ n := faceHom_ne F hF hFcard
    let θ := faceHom F hF
    let z := W.map θ.op y
    have hz : z ∈ A.obj (op (Henry.SemiSimplexCategory.mk (faceDim F))) :=
      hfaces (faceDim F) θ hθn
    let f := elFaceHom y θ
    let iotaCat := elι φ f
    let localTheta : Fin (faceDim F + 1) ↪ Fin (n + 1) := semiEmb θ
    let localIota : Fin ((elNF φ (elOf z)).m + 1) ↪ Fin (m0 + 1) := semiEmb iotaCat
    have hThetaEq : localTheta = (faceEmb F hF).toEmbedding := by
      ext j
      rfl
    have hThetaImg : Finset.univ.image localTheta = F := by
      rw [hThetaEq]
      exact faceEmb_image F hF
    have hv : v0 ∘ localTheta = localIota ∘ (elNF φ (elOf z)).v := by
      change v0 ∘ θ.1.toOrderHom = iotaCat.1.toOrderHom ∘ (elNF φ (elOf z)).v
      exact (elι_spec φ (elFaceHom y θ)).1
    let pull := pullDV localTheta localIota
    have hpull : ∀ j, DV.mapV localTheta localIota (pull (w j)) = w j := by
      intro j
      have hjR : w j ∈ R := Finset.mem_image_of_mem _ (Finset.mem_univ j)
      cases h : w j with
      | top i =>
          have hiR : DV.top i ∈ R := by rw [← h]; exact hjR
          have hiF : i ∈ F := mem_dcylCarrier_top hiR
          have hiImg : i ∈ Finset.univ.image localTheta := by
            rw [hThetaImg]
            exact hiF
          obtain ⟨d, -, hdi⟩ := Finset.mem_image.mp hiImg
          exact mapV_pullDV_top localTheta localIota ⟨d, hdi⟩
      | mid T =>
          have hTR : DV.mid T ∈ R := by rw [← h]; exact hjR
          have hTF : T ⊆ F := subset_dcylCarrier_mid hTR
          have hTImg : T ⊆ Finset.univ.image localTheta := by
            rw [hThetaImg]
            exact hTF
          exact mapV_pullDV_mid localTheta localIota hTImg
      | bot c =>
          have hcR : DV.bot c ∈ R := by rw [← h]; exact hjR
          obtain ⟨T, hTR⟩ := exists_mid_of_bot_nonbottom hR hnot hcR
          obtain ⟨a, ha, hva⟩ := hR.2.2.2.2 c T hcR hTR
          have haF : a ∈ F := subset_dcylCarrier_mid hTR ha
          have haImg : a ∈ Finset.univ.image localTheta := by
            rw [hThetaImg]
            exact haF
          obtain ⟨d, -, hda⟩ := Finset.mem_image.mp haImg
          have hvd := congrFun hv d
          have hcImage : ∃ e, localIota e = c := by
            refine ⟨(elNF φ (elOf z)).v d, ?_⟩
            calc
              localIota ((elNF φ (elOf z)).v d) = v0 (localTheta d) := hvd.symm
              _ = v0 a := by rw [hda]
              _ = c := hva
          exact mapV_pullDV_bot localTheta localIota hcImage
    have hlocal := pullSimplex localTheta (semiEmb_strictMono θ) localIota
      (semiEmb_strictMono iotaCat) hv R hR w rfl σ.down.2.1 pull hpull
    exact faceCarrierDesc φ A y θ hθn hz (pull ∘ w) hlocal.1 hlocal.2

theorem boundarySimplexDesc_eq_bottom {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)
    (A : Subfunctor W) {n k : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hfaces : ∀ (j : ℕ) (θ : Henry.SemiSimplexCategory.mk j ⟶ Henry.SemiSimplexCategory.mk n),
      j ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk j)))
    (σ : ULift ((dcylDBoundaryComplex (elNF φ (elOf y)).v).Simplex k))
    (hbot : ∀ a ∈ Finset.univ.image σ.down.1, ∃ c, a = DV.bot c) :
    boundarySimplexDesc φ A y hfaces σ =
      bottomCarrierMap (cylSub φ A).base (elNF φ (elOf y)).x
        (botCode σ.down.1) (botCode_strict hbot σ.down.2.1) := by
  unfold boundarySimplexDesc
  simp [hbot]

theorem boundarySimplexDesc_precomp {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)
    (A : Subfunctor W) {n k l : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hfaces : ∀ (j : ℕ) (θ : Henry.SemiSimplexCategory.mk j ⟶ Henry.SemiSimplexCategory.mk n),
      j ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk j)))
    (σ : ULift ((dcylDBoundaryComplex (elNF φ (elOf y)).v).Simplex k))
    (α : Henry.SemiSimplexCategory.mk l ⟶ Henry.SemiSimplexCategory.mk k) :
    Henry.SemiSSet.stdSimplex.map α ≫ boundarySimplexDesc φ A y hfaces σ =
      boundarySimplexDesc φ A y hfaces
        ((dcylDBoundary (elNF φ (elOf y)).v).map α.op σ) := by
  classical
  let w := σ.down.1
  let R := Finset.univ.image w
  let σ' : ULift ((dcylDBoundaryComplex (elNF φ (elOf y)).v).Simplex l) :=
    (dcylDBoundary (elNF φ (elOf y)).v).map α.op σ
  let w' := σ'.down.1
  have hw' : w' = w ∘ α.1.toOrderHom := by rfl
  by_cases hbot : ∀ a ∈ R, ∃ c, a = DV.bot c
  · have hbot' : ∀ a ∈ Finset.univ.image w', ∃ c, a = DV.bot c := by
      intro a ha
      obtain ⟨j, -, hja⟩ := Finset.mem_image.mp ha
      refine ⟨botCode w (α.1.toOrderHom j), ?_⟩
      calc
        a = w' j := hja.symm
        _ = w (α.1.toOrderHom j) := by simp [hw']
        _ = DV.bot (botCode w (α.1.toOrderHom j)) := botCode_spec hbot _
    have hcodes : botCode w' = botCode w ∘ α.1.toOrderHom := by
      funext j
      have hchild := botCode_spec hbot' j
      rw [hw'] at hchild
      have hparent := botCode_spec hbot (α.1.toOrderHom j)
      have heq : DV.bot (botCode w' j) = DV.bot (botCode w (α.1.toOrderHom j)) :=
        hchild.symm.trans hparent
      exact DV.bot.inj heq
    rw [boundarySimplexDesc_eq_bottom φ A y hfaces σ hbot,
      boundarySimplexDesc_eq_bottom φ A y hfaces σ' hbot']
    exact bottomCarrierMap_precomp (cylSub φ A).base (elNF φ (elOf y)).x α
      (botCode w) (botCode_strict hbot σ.down.2.1)
      (botCode w') (botCode_strict hbot' σ'.down.2.1) hcodes
  · have hnotF : ¬ ∀ a ∈ R, ∃ c, a = DV.bot c := hbot
    let nf0 := elNF φ (elOf y)
    let v0 := nf0.v
    have hbdryF : (dcylDBoundaryComplex v0).S R := by
      simpa [v0, w, R, nf0] using σ.down.2.2
    have hRF : (dcylDComplex v0).S R := hbdryF.1
    let F := dcylCarrier R
    have hF : F.Nonempty := dcylCarrier_nonempty_of_not_bottom hRF hnotF
    have hFcard : F.card ≤ n := dcylCarrier_card_le_of_boundary hbdryF hnotF
    have hθFn : faceDim F ≠ n := faceHom_ne F hF hFcard
    let θF := faceHom F hF
    let zF := W.map θF.op y
    have hzF : zF ∈ A.obj (op (Henry.SemiSimplexCategory.mk (faceDim F))) :=
      hfaces (faceDim F) θF hθFn
    let eF : A.toFunctor.Elements := A.toFunctor.elementsMk _ ⟨zF, hzF⟩
    let iotaF := elι φ (elFaceHom y θF)
    let thetaEmbF : Fin (faceDim F + 1) ↪ Fin (n + 1) := semiEmb θF
    let iotaEmbF : Fin ((elNF φ (elOf zF)).m + 1) ↪ Fin (nf0.m + 1) := semiEmb iotaF
    have hThetaEqF : thetaEmbF = (faceEmb F hF).toEmbedding := by
      ext j
      rfl
    have hThetaImgF : Finset.univ.image thetaEmbF = F := by
      rw [hThetaEqF]
      exact faceEmb_image F hF
    have hvF : v0 ∘ thetaEmbF = iotaEmbF ∘ (elNF φ (elOf zF)).v := by
      change v0 ∘ θF.1.toOrderHom = iotaF.1.toOrderHom ∘ (elNF φ (elOf zF)).v
      exact (elι_spec φ (elFaceHom y θF)).1
    let pullF := pullDV thetaEmbF iotaEmbF
    have hpullF : ∀ j, DV.mapV thetaEmbF iotaEmbF (pullF (w j)) = w j := by
      intro j
      have hjR : w j ∈ R := Finset.mem_image_of_mem _ (Finset.mem_univ j)
      cases h : w j with
      | top i =>
          have hiR : DV.top i ∈ R := by rw [← h]; exact hjR
          have hiF : i ∈ F := mem_dcylCarrier_top hiR
          have hiImg : i ∈ Finset.univ.image thetaEmbF := by rw [hThetaImgF]; exact hiF
          obtain ⟨d, -, hdi⟩ := Finset.mem_image.mp hiImg
          exact mapV_pullDV_top thetaEmbF iotaEmbF ⟨d, hdi⟩
      | mid T =>
          have hTR : DV.mid T ∈ R := by rw [← h]; exact hjR
          have hTF : T ⊆ F := subset_dcylCarrier_mid hTR
          have hTImg : T ⊆ Finset.univ.image thetaEmbF := by rw [hThetaImgF]; exact hTF
          exact mapV_pullDV_mid thetaEmbF iotaEmbF hTImg
      | bot c =>
          have hcR : DV.bot c ∈ R := by rw [← h]; exact hjR
          obtain ⟨T, hTR⟩ := exists_mid_of_bot_nonbottom hRF hnotF hcR
          obtain ⟨a, ha, hva⟩ := hRF.2.2.2.2 c T hcR hTR
          have haF : a ∈ F := subset_dcylCarrier_mid hTR ha
          have haImg : a ∈ Finset.univ.image thetaEmbF := by rw [hThetaImgF]; exact haF
          obtain ⟨d, -, hda⟩ := Finset.mem_image.mp haImg
          have hvd := congrFun hvF d
          have hcImage : ∃ e, iotaEmbF e = c := by
            refine ⟨(elNF φ (elOf zF)).v d, ?_⟩
            calc
              iotaEmbF ((elNF φ (elOf zF)).v d) = v0 (thetaEmbF d) := hvd.symm
              _ = v0 a := by rw [hda]
              _ = c := hva
          exact mapV_pullDV_bot thetaEmbF iotaEmbF hcImage
    have hlocalF := pullSimplex thetaEmbF (semiEmb_strictMono θF) iotaEmbF
      (semiEmb_strictMono iotaF) hvF R hRF w rfl σ.down.2.1 pullF hpullF
    let localF := pullF ∘ w
    have hParentDesc : boundarySimplexDesc φ A y hfaces σ =
        faceCarrierDesc φ A y θF hθFn hzF localF hlocalF.1 hlocalF.2 := by
      have hnotSet : ¬ ∀ a ∈ Finset.univ.image σ.down.1, ∃ c, a = DV.bot c := by
        simpa [R, w] using hnotF
      unfold boundarySimplexDesc
      rw [dif_neg hnotSet]
    have hbdryG : (dcylDBoundaryComplex v0).S (Finset.univ.image w') :=
      σ'.down.2.2
    by_cases hbotG : ∀ a ∈ Finset.univ.image w', ∃ c, a = DV.bot c
    · have hLocalBot : ∀ j, ∃ c, localF (α.1.toOrderHom j) = DV.bot c := by
        intro j
        obtain ⟨c, hc⟩ := hbotG (w' j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
        have hParent : DV.mapV thetaEmbF iotaEmbF
            (localF (α.1.toOrderHom j)) = w' j := by
          change DV.mapV thetaEmbF iotaEmbF (pullF (w (α.1.toOrderHom j))) = w' j
          calc
            DV.mapV thetaEmbF iotaEmbF (pullF (w (α.1.toOrderHom j))) =
                w (α.1.toOrderHom j) := hpullF _
            _ = w' j := by
              simpa [Function.comp_apply] using (congrFun hw' j).symm
        cases h : localF (α.1.toOrderHom j) with
        | top i =>
            have hTop : DV.mapV thetaEmbF iotaEmbF (DV.top i) = w' j := by
              calc
                DV.mapV thetaEmbF iotaEmbF (DV.top i) =
                    DV.mapV thetaEmbF iotaEmbF (localF (α.1.toOrderHom j)) :=
                  congrArg (DV.mapV thetaEmbF iotaEmbF) h.symm
                _ = w' j := hParent
            have hTop' : DV.top (thetaEmbF i) = DV.bot c := by
              simpa [DV.mapV] using hTop.trans hc
            nomatch hTop'
        | mid S =>
            have hMid : DV.mapV thetaEmbF iotaEmbF (DV.mid S) = w' j := by
              calc
                DV.mapV thetaEmbF iotaEmbF (DV.mid S) =
                    DV.mapV thetaEmbF iotaEmbF (localF (α.1.toOrderHom j)) :=
                  congrArg (DV.mapV thetaEmbF iotaEmbF) h.symm
                _ = w' j := hParent
            have hMid' : DV.mid (Finset.map thetaEmbF S) = DV.bot c := by
              simpa [DV.mapV] using hMid.trans hc
            nomatch hMid'
        | bot d => exact ⟨d, rfl⟩
      let localChild : Fin (l + 1) → DV (faceDim F) (elNF φ (elOf zF)).m :=
        localF ∘ α.1.toOrderHom
      have hLocalChildStrict : StrictMono localChild :=
        hlocalF.1.comp (SemiSimplexCategory.strictMono α)
      have hLocalChildBot : ∀ a ∈ Finset.univ.image localChild, ∃ c, a = DV.bot c := by
        intro a ha
        obtain ⟨j, -, hja⟩ := Finset.mem_image.mp ha
        obtain ⟨c, hc⟩ := hLocalBot j
        exact ⟨c, hja.symm.trans hc⟩
      let cF := botCode localChild
      have hcF : StrictMono cF := botCode_strict hLocalChildBot hLocalChildStrict
      have hlocalList : localF ∘ α.1.toOrderHom = fun j => DV.bot (cF j) := by
        funext j
        exact botCode_spec hLocalChildBot j
      have hlocalBottom := simplexMap_bottom_factor α localF hlocalF.1 hlocalF.2 cF hcF
        hlocalList
      let beta := vhom cF hcF
      have hCodes : botCode w' = iotaEmbF ∘ cF := by
        funext j
        have hParent := hpullF (α.1.toOrderHom j)
        have hval : w (α.1.toOrderHom j) = w' j := by
          simpa [Function.comp_apply] using (congrFun hw' j).symm
        change DV.mapV thetaEmbF iotaEmbF ((localF ∘ α.1.toOrderHom) j) =
          w (α.1.toOrderHom j) at hParent
        rw [hlocalList, hval, botCode_spec hbotG j] at hParent
        simp only [DV.mapV, DV.bot.injEq] at hParent
        exact hParent.symm
      have hBotArrow : vhom iotaEmbF (semiEmb_strictMono iotaF) = iotaF := by
        apply WideSubcategory.hom_ext
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext i
        change iotaEmbF i = iotaF.1.toOrderHom i
        rfl
      have hXFace : X.map (vhom iotaEmbF (semiEmb_strictMono iotaF)).op
          (elNF φ (elOf y)).x = (elNF φ (elOf zF)).x := by
        rw [hBotArrow]
        exact (elι_spec φ (elFaceHom y θF)).2
      have hxN : (cylSub φ A).xN.app (Opposite.op eF) =
          uliftYonedaEquiv.symm (elNF φ (elOf zF)).x := by rfl
      have hBottomFace : bottomCarrierMap (cylSub φ A).base
          (elNF φ (elOf y)).x iotaEmbF (semiEmb_strictMono iotaF) =
          (cylSub φ A).xN.app (Opposite.op eF) ≫ (cylSub φ A).base := by
        unfold bottomCarrierMap
        change uliftYonedaEquiv.symm
            (X.map (vhom iotaEmbF (semiEmb_strictMono iotaF)).op (elNF φ (elOf y)).x) ≫
              (cylSub φ A).base =
          uliftYonedaEquiv.symm (elNF φ (elOf zF)).x ≫ (cylSub φ A).base
        rw [hXFace, ← hxN]
      have hBotInCyl : (cylSub φ A).botN.app (Opposite.op eF) =
          dcylDBot (elNF φ (elOf zF)).v := by rfl
      have hPushF : dcylDBot (elNF φ (elOf zF)).v ≫
          colimit.ι (cylSub φ A).DC (Opposite.op eF) ≫ (cylSub φ A).incl =
            (cylSub φ A).xN.app (Opposite.op eF) ≫ (cylSub φ A).base := by
        have h := cylDatum_botCondition (cylSub φ A) (Opposite.op eF)
        rw [hBotInCyl] at h
        exact h
      have hFaceF : faceCarrierDesc φ A y θF hθFn hzF localF hlocalF.1 hlocalF.2 =
          (dcylDComplex (elNF φ (elOf zF)).v).simplexMap localF hlocalF.1 hlocalF.2 ≫
            colimit.ι (cylSub φ A).DC (Opposite.op eF) ≫ (cylSub φ A).incl := by rfl
      have hBottomPre := bottomCarrierMap_precomp (cylSub φ A).base
        (elNF φ (elOf y)).x beta iotaEmbF (semiEmb_strictMono iotaF)
        (botCode w') (botCode_strict hbotG σ'.down.2.1) (by
          change botCode w' = iotaEmbF ∘ cF
          exact hCodes)
      rw [hParentDesc]
      calc
        Henry.SemiSSet.stdSimplex.map α ≫ faceCarrierDesc φ A y θF hθFn hzF
            localF hlocalF.1 hlocalF.2 =
          (Henry.SemiSSet.stdSimplex.map α ≫
              ((dcylDComplex (elNF φ (elOf zF)).v).simplexMap localF
                hlocalF.1 hlocalF.2)) ≫
            colimit.ι (cylSub φ A).DC (Opposite.op eF) ≫ (cylSub φ A).incl := by
              rw [hFaceF]
              cat_disch
        _ = (Henry.SemiSSet.stdSimplex.map beta ≫
              dcylDBot (elNF φ (elOf zF)).v) ≫
            colimit.ι (cylSub φ A).DC (Opposite.op eF) ≫ (cylSub φ A).incl := by
              rw [hlocalBottom]
        _ = Henry.SemiSSet.stdSimplex.map beta ≫
              ((cylSub φ A).xN.app (Opposite.op eF) ≫ (cylSub φ A).base) := by
              rw [Category.assoc, hPushF]
              rfl
        _ = Henry.SemiSSet.stdSimplex.map beta ≫
              bottomCarrierMap (cylSub φ A).base (elNF φ (elOf y)).x iotaEmbF
                (semiEmb_strictMono iotaF) := by
              exact congrArg (fun f => Henry.SemiSSet.stdSimplex.map beta ≫ f)
                hBottomFace.symm
        _ = bottomCarrierMap (cylSub φ A).base (elNF φ (elOf y)).x
              (botCode w') (botCode_strict hbotG σ'.down.2.1) := hBottomPre
        _ = boundarySimplexDesc φ A y hfaces σ' := by
              rw [boundarySimplexDesc_eq_bottom φ A y hfaces σ' hbotG]
    · have hRG : (dcylDComplex v0).S (Finset.univ.image w') := hbdryG.1
      let G := dcylCarrier (Finset.univ.image w')
      have hG : G.Nonempty := dcylCarrier_nonempty_of_not_bottom hRG hbotG
      have hGcard : G.card ≤ n := dcylCarrier_card_le_of_boundary hbdryG hbotG
      have hθGn : faceDim G ≠ n := faceHom_ne G hG hGcard
      let θG := faceHom G hG
      let zG := W.map θG.op y
      have hzG : zG ∈ A.obj (op (Henry.SemiSimplexCategory.mk (faceDim G))) :=
        hfaces (faceDim G) θG hθGn
      let iotaG := elι φ (elFaceHom y θG)
      let thetaEmbG : Fin (faceDim G + 1) ↪ Fin (n + 1) := semiEmb θG
      let iotaEmbG : Fin ((elNF φ (elOf zG)).m + 1) ↪ Fin (nf0.m + 1) := semiEmb iotaG
      have hThetaEqG : thetaEmbG = (faceEmb G hG).toEmbedding := by
        ext j
        rfl
      have hThetaImgG : Finset.univ.image thetaEmbG = G := by
        rw [hThetaEqG]
        exact faceEmb_image G hG
      have hvG : v0 ∘ thetaEmbG = iotaEmbG ∘ (elNF φ (elOf zG)).v := by
        change v0 ∘ θG.1.toOrderHom = iotaG.1.toOrderHom ∘ (elNF φ (elOf zG)).v
        exact (elι_spec φ (elFaceHom y θG)).1
      let pullG := pullDV thetaEmbG iotaEmbG
      have hpullG : ∀ j, DV.mapV thetaEmbG iotaEmbG (pullG (w' j)) = w' j := by
        intro j
        have hjR : w' j ∈ Finset.univ.image w' := Finset.mem_image_of_mem _ (Finset.mem_univ j)
        cases h : w' j with
        | top i =>
            have hiR : DV.top i ∈ Finset.univ.image w' := by rw [← h]; exact hjR
            have hiF : i ∈ G := mem_dcylCarrier_top hiR
            have hiImg : i ∈ Finset.univ.image thetaEmbG := by rw [hThetaImgG]; exact hiF
            obtain ⟨d, -, hdi⟩ := Finset.mem_image.mp hiImg
            exact mapV_pullDV_top thetaEmbG iotaEmbG ⟨d, hdi⟩
        | mid T =>
            have hTR : DV.mid T ∈ Finset.univ.image w' := by rw [← h]; exact hjR
            have hTF : T ⊆ G := subset_dcylCarrier_mid hTR
            have hTImg : T ⊆ Finset.univ.image thetaEmbG := by rw [hThetaImgG]; exact hTF
            exact mapV_pullDV_mid thetaEmbG iotaEmbG hTImg
        | bot c =>
            have hcR : DV.bot c ∈ Finset.univ.image w' := by rw [← h]; exact hjR
            obtain ⟨T, hTR⟩ := exists_mid_of_bot_nonbottom hRG hbotG hcR
            obtain ⟨a, ha, hva⟩ := hRG.2.2.2.2 c T hcR hTR
            have haF : a ∈ G := subset_dcylCarrier_mid hTR ha
            have haImg : a ∈ Finset.univ.image thetaEmbG := by rw [hThetaImgG]; exact haF
            obtain ⟨d, -, hda⟩ := Finset.mem_image.mp haImg
            have hvd := congrFun hvG d
            have hcImage : ∃ e, iotaEmbG e = c := by
              refine ⟨(elNF φ (elOf zG)).v d, ?_⟩
              calc
                iotaEmbG ((elNF φ (elOf zG)).v d) = v0 (thetaEmbG d) := hvd.symm
                _ = v0 a := by rw [hda]
                _ = c := hva
            exact mapV_pullDV_bot thetaEmbG iotaEmbG hcImage
      have hlocalG := pullSimplex thetaEmbG (semiEmb_strictMono θG) iotaEmbG
        (semiEmb_strictMono iotaG) hvG (Finset.univ.image w') hRG w' rfl σ'.down.2.1
        pullG hpullG
      let localG := pullG ∘ w'
      have hChildDesc : boundarySimplexDesc φ A y hfaces σ' =
          faceCarrierDesc φ A y θG hθGn hzG localG hlocalG.1 hlocalG.2 := by
        have hnotSetG : ¬ ∀ a ∈ Finset.univ.image σ'.down.1, ∃ c, a = DV.bot c := by
          simpa [w'] using hbotG
        unfold boundarySimplexDesc
        rw [dif_neg hnotSetG]
      have hRsub : Finset.univ.image w' ⊆ R := by
        intro b hb
        obtain ⟨j, -, hjb⟩ := Finset.mem_image.mp hb
        exact Finset.mem_image.mpr ⟨α.1.toOrderHom j, Finset.mem_univ _, by
          have hval : w (α.1.toOrderHom j) = w' j := by
            simpa [Function.comp_apply] using (congrFun hw' j).symm
          exact hval.trans hjb⟩
      have hGF : G ⊆ F := dcylCarrier_mono hRsub
      let rho := faceFactorHom F G hF hG hGF
      have hθfactor : θG = rho ≫ θF := faceHom_factor F G hF hG hGF
      have hzg : W.map rho.op zF = zG := faceMap_comp y θF θG rho hθfactor
      let gW : elOf zF ⟶ elOf zG := ⟨rho.op, hzg⟩
      let iotaR := elι φ gW
      have hFactorIota : iotaG = iotaR ≫ iotaF :=
        elι_factor_of_faces φ y θF θG rho hθfactor hzg
      have hThetaEmbFactor : thetaEmbG = (semiEmb rho).trans thetaEmbF := by
        change semiEmb (faceHom G hG) = (semiEmb rho).trans (semiEmb (faceHom F hF))
        calc
          semiEmb (faceHom G hG) = semiEmb (rho ≫ faceHom F hF) := by
            exact congrArg semiEmb hθfactor
          _ = (semiEmb rho).trans (semiEmb (faceHom F hF)) := semiEmb_comp rho (faceHom F hF)
      have hIotaEmbFactor : iotaEmbG = (semiEmb iotaR).trans iotaEmbF := by
        change semiEmb (elι φ (elFaceHom y θG)) =
          (semiEmb iotaR).trans (semiEmb (elι φ (elFaceHom y θF)))
        calc
          semiEmb (elι φ (elFaceHom y θG)) = semiEmb (iotaR ≫ iotaF) :=
            congrArg semiEmb hFactorIota
          _ = (semiEmb iotaR).trans (semiEmb iotaF) := semiEmb_comp iotaR iotaF
      have hMapVComp : DV.mapV thetaEmbF iotaEmbF ∘ DV.mapV (semiEmb rho) (semiEmb iotaR) =
          DV.mapV thetaEmbG iotaEmbG := by
        rw [mapV_comp, hThetaEmbFactor, hIotaEmbFactor]
      have hLocalFactor : ∀ j,
          DV.mapV (semiEmb rho) (semiEmb iotaR) (pullG (w' j)) = pullF (w (α.1.toOrderHom j)) := by
        intro j
        apply mapV_injective thetaEmbF iotaEmbF
        calc
          DV.mapV thetaEmbF iotaEmbF
              (DV.mapV (semiEmb rho) (semiEmb iotaR) (pullG (w' j))) =
            DV.mapV thetaEmbG iotaEmbG (pullG (w' j)) :=
              congrFun hMapVComp (pullG (w' j))
          _ = w' j := hpullG j
          _ = w (α.1.toOrderHom j) := by
            simpa [Function.comp_apply] using congrFun hw' j
          _ = DV.mapV thetaEmbF iotaEmbF (pullF (w (α.1.toOrderHom j))) :=
            (hpullF (α.1.toOrderHom j)).symm
      have hfun : (dcylDElMap φ gW).f ∘ localG = localF ∘ α.1.toOrderHom := by
        funext j
        change DV.mapV (semiEmb rho) (semiEmb iotaR) (pullG (w' j)) =
          pullF (w (α.1.toOrderHom j))
        exact hLocalFactor j
      rw [hParentDesc, hChildDesc]
      exact faceCarrierDesc_precomp φ A y θF θG rho hθfactor hθFn hθGn hzF hzG hzg α
        localF hlocalF.1 hlocalF.2 localG hlocalG.1 hlocalG.2 hfun
noncomputable def boundaryDescNat {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)
    (A : Subfunctor W) {n : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hfaces : ∀ (k : ℕ) (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n),
      k ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk k))) :
    Presheaf.functorToRepresentables.{u} (dcylDBoundary.{u} (elNF φ (elOf y)).v) ⟶
      (Functor.const (dcylDBoundary.{u} (elNF φ (elOf y)).v).Elementsᵒᵖ).obj (cylSub φ A).obj where
  app e := boundarySimplexDesc φ A y hfaces e.unop.val
  naturality e₁ e₂ f := by
    ext k σ
    have h := boundarySimplexDesc_precomp φ A y hfaces e₂.unop.val f.unop.hom.unop
    have hval : (dcylDBoundary (elNF φ (elOf y)).v).map
        f.unop.hom.unop.op (unop e₂).val = (unop e₁).val := by
      simpa using f.unop.map_val
    rw [hval] at h
    change ((Henry.SemiSSet.stdSimplex.map f.unop.hom.unop ≫
      boundarySimplexDesc φ A y hfaces (unop e₂).val).app k) σ =
        ((boundarySimplexDesc φ A y hfaces (unop e₁).val).app k) σ
    exact congrFun (congrArg (fun g => g.app k) h) σ

theorem boundarySimplexDesc_face {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)
    (A : Subfunctor W) {n p k : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hfaces : ∀ (j : ℕ) (θ : Henry.SemiSimplexCategory.mk j ⟶ Henry.SemiSimplexCategory.mk n),
      j ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk j)))
    (θ : Henry.SemiSimplexCategory.mk p ⟶ Henry.SemiSimplexCategory.mk n)
    (hk : p ≠ n)
    (hz : W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk p)))
    (σ : ULift ((dcylDComplex (elNF φ (elOf (W.map θ.op y))).v).Simplex k)) :
    boundarySimplexDesc φ A y hfaces
        ((faceBdry φ y θ hk).toSemiSSet.app (op (Henry.SemiSimplexCategory.mk k)) σ) =
      (dcylDComplex (elNF φ (elOf (W.map θ.op y))).v).simplexMap
        σ.down.1 σ.down.2.1 σ.down.2.2 ≫
        colimit.ι (cylSub φ A).DC
          (op (A.toFunctor.elementsMk _ ⟨W.map θ.op y, hz⟩)) ≫ (cylSub φ A).incl := by
  classical
  let zF := W.map θ.op y
  let eF := A.toFunctor.elementsMk _ ⟨zF, hz⟩
  let wF := σ.down.1
  let Rlocal := Finset.univ.image wF
  let thetaEmbF : Fin (p + 1) ↪ Fin (n + 1) := semiEmb θ
  let iotaF := elι φ (elFaceHom y θ)
  let iotaEmbF : Fin ((elNF φ (elOf zF)).m + 1) ↪ Fin ((elNF φ (elOf y)).m + 1) :=
    semiEmb iotaF
  let w := ((faceBdry φ y θ hk).toSemiSSet.app (op (Henry.SemiSimplexCategory.mk k)) σ).down.1
  let R := Finset.univ.image w
  have hGlobalMap : w = DV.mapV thetaEmbF iotaEmbF ∘ wF := by rfl
  have hVertexMap : (faceBdry φ y θ hk).f = DV.mapV thetaEmbF iotaEmbF := by rfl
  have hRmap : R = Rlocal.image (faceBdry φ y θ hk).f := by
    dsimp [R, Rlocal]
    rw [hGlobalMap, Finset.image_image, ← hVertexMap]
  have hbdry : (dcylDBoundaryComplex (elNF φ (elOf y)).v).S R := by
    rw [hRmap]
    exact (faceBdry φ y θ hk).map_S Rlocal σ.down.2.2
  by_cases hbot : ∀ a ∈ R, ∃ c, a = DV.bot c
  · rw [boundarySimplexDesc_eq_bottom φ A y hfaces _ hbot]
    have hLocalBot : ∀ a ∈ Rlocal, ∃ c, a = DV.bot c := by
      intro a ha
      obtain ⟨j, -, hja⟩ := Finset.mem_image.mp ha
      obtain ⟨c, hc⟩ := hbot (w j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
      have hmap := congrFun hGlobalMap j
      change w j = DV.mapV thetaEmbF iotaEmbF (wF j) at hmap
      rw [hja] at hmap
      have hEq : DV.mapV thetaEmbF iotaEmbF a = DV.bot c := hmap.symm.trans hc
      cases a with
      | top i => simp [DV.mapV] at hEq
      | mid S => simp [DV.mapV] at hEq
      | bot d => exact ⟨d, by rfl⟩
    let cF := botCode wF
    have hcF : StrictMono cF := botCode_strict hLocalBot σ.down.2.1
    have hLocalList : wF = fun j => DV.bot (cF j) := by
      funext j
      exact botCode_spec hLocalBot j
    let beta := vhom cF hcF
    have hlocalBottom : (dcylDComplex (elNF φ (elOf zF)).v).simplexMap
          wF σ.down.2.1 σ.down.2.2 =
        Henry.SemiSSet.stdSimplex.map beta ≫ dcylDBot (elNF φ (elOf zF)).v := by
      have h := simplexMap_bottom_factor (𝟙 (Henry.SemiSimplexCategory.mk k))
        wF σ.down.2.1 σ.down.2.2 cF hcF (by
          funext j
          simp [hLocalList])
      simpa using h
    have hCodes : botCode w = iotaEmbF ∘ cF := by
      funext j
      have hmap := congrFun hGlobalMap j
      change w j = DV.mapV thetaEmbF iotaEmbF (wF j) at hmap
      rw [hLocalList, botCode_spec hbot j] at hmap
      change DV.bot (botCode w j) = DV.bot (iotaEmbF (cF j)) at hmap
      simp only [DV.bot.injEq] at hmap
      exact hmap
    have hBotArrow : vhom iotaEmbF (semiEmb_strictMono iotaF) = iotaF := by
      apply WideSubcategory.hom_ext
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      change iotaEmbF i = iotaF.1.toOrderHom i
      rfl
    have hXFace : X.map (vhom iotaEmbF (semiEmb_strictMono iotaF)).op
        (elNF φ (elOf y)).x = (elNF φ (elOf zF)).x := by
      rw [hBotArrow]
      exact (elι_spec φ (elFaceHom y θ)).2
    have hxN : (cylSub φ A).xN.app (Opposite.op eF) =
        uliftYonedaEquiv.symm (elNF φ (elOf zF)).x := by rfl
    have hBottomFace : bottomCarrierMap (cylSub φ A).base
        (elNF φ (elOf y)).x iotaEmbF (semiEmb_strictMono iotaF) =
        (cylSub φ A).xN.app (Opposite.op eF) ≫ (cylSub φ A).base := by
      unfold bottomCarrierMap
      change uliftYonedaEquiv.symm
          (X.map (vhom iotaEmbF (semiEmb_strictMono iotaF)).op (elNF φ (elOf y)).x) ≫
            (cylSub φ A).base =
        uliftYonedaEquiv.symm (elNF φ (elOf zF)).x ≫ (cylSub φ A).base
      rw [hXFace, ← hxN]
    have hBotInCyl : (cylSub φ A).botN.app (Opposite.op eF) =
        dcylDBot (elNF φ (elOf zF)).v := by rfl
    have hPushF : dcylDBot (elNF φ (elOf zF)).v ≫
        colimit.ι (cylSub φ A).DC (Opposite.op eF) ≫ (cylSub φ A).incl =
          (cylSub φ A).xN.app (Opposite.op eF) ≫ (cylSub φ A).base := by
      have h := cylDatum_botCondition (cylSub φ A) (Opposite.op eF)
      rw [hBotInCyl] at h
      exact h
    have hBottomPre := bottomCarrierMap_precomp (cylSub φ A).base
      (elNF φ (elOf y)).x beta iotaEmbF (semiEmb_strictMono iotaF)
      (botCode w) (botCode_strict hbot
        ((faceBdry φ y θ hk).toSemiSSet.app (op (Henry.SemiSimplexCategory.mk k)) σ).down.2.1)
      hCodes
    calc
      bottomCarrierMap (cylSub φ A).base (elNF φ (elOf y)).x
          (botCode w) (botCode_strict hbot
            ((faceBdry φ y θ hk).toSemiSSet.app (op (Henry.SemiSimplexCategory.mk k)) σ).down.2.1) =
        Henry.SemiSSet.stdSimplex.map beta ≫
          bottomCarrierMap (cylSub φ A).base (elNF φ (elOf y)).x iotaEmbF
            (semiEmb_strictMono iotaF) := hBottomPre.symm
      _ = Henry.SemiSSet.stdSimplex.map beta ≫
          ((cylSub φ A).xN.app (Opposite.op eF) ≫ (cylSub φ A).base) := by
        rw [hBottomFace]
        rfl
      _ = Henry.SemiSSet.stdSimplex.map beta ≫
          (dcylDBot (elNF φ (elOf zF)).v ≫
            colimit.ι (cylSub φ A).DC (Opposite.op eF) ≫ (cylSub φ A).incl) := by
        calc
          _ = Henry.SemiSSet.stdSimplex.map beta ≫
              ((cylSub φ A).xN.app (Opposite.op eF) ≫ (cylSub φ A).base) := by
                cat_disch
          _ = _ := congrArg (fun g => Henry.SemiSSet.stdSimplex.map beta ≫ g) hPushF.symm
      _ = (Henry.SemiSSet.stdSimplex.map beta ≫ dcylDBot (elNF φ (elOf zF)).v) ≫
          colimit.ι (cylSub φ A).DC (Opposite.op eF) ≫ (cylSub φ A).incl := by
        cat_disch
      _ = (dcylDComplex (elNF φ (elOf zF)).v).simplexMap
            wF σ.down.2.1 σ.down.2.2 ≫
          colimit.ι (cylSub φ A).DC (Opposite.op eF) ≫ (cylSub φ A).incl := by
        rw [hlocalBottom]
  · have hnot : ¬∀ a ∈ R, ∃ c, a = DV.bot c := hbot
    have hR : (dcylDComplex (elNF φ (elOf y)).v).S R := hbdry.1
    let G := dcylCarrier R
    have hG : G.Nonempty := dcylCarrier_nonempty_of_not_bottom hR hnot
    have hGcard : G.card ≤ n := dcylCarrier_card_le_of_boundary hbdry hnot
    have hθG : faceDim G ≠ n := faceHom_ne G hG hGcard
    let θG := faceHom G hG
    let zG := W.map θG.op y
    have hzG : zG ∈ A.obj (op (Henry.SemiSimplexCategory.mk (faceDim G))) :=
      hfaces (faceDim G) θG hθG
    let iotaG := elι φ (elFaceHom y θG)
    let thetaEmbG : Fin (faceDim G + 1) ↪ Fin (n + 1) := semiEmb θG
    let iotaEmbG : Fin ((elNF φ (elOf zG)).m + 1) ↪ Fin ((elNF φ (elOf y)).m + 1) :=
      semiEmb iotaG
    have hThetaEqG : thetaEmbG = (faceEmb G hG).toEmbedding := by
      ext j
      rfl
    have hThetaImgG : Finset.univ.image thetaEmbG = G := by
      rw [hThetaEqG]
      exact faceEmb_image G hG
    have hGF : G ⊆ Finset.univ.image thetaEmbF := by
      intro i hi
      dsimp [G] at hi
      simp only [dcylCarrier, Finset.mem_biUnion] at hi
      obtain ⟨a, ha, hia⟩ := hi
      obtain ⟨j, -, hja⟩ := Finset.mem_image.mp ha
      have hval : a = DV.mapV thetaEmbF iotaEmbF (wF j) := by
        calc
          a = w j := hja.symm
          _ = DV.mapV thetaEmbF iotaEmbF (wF j) := by
            simpa [Function.comp_apply] using congrFun hGlobalMap j
      cases a with
      | top i' =>
          cases hw : wF j with
          | top d =>
              rw [hw] at hval
              have hEq : i' = thetaEmbF d := by simpa [DV.mapV] using hval
              have hii : i = i' := by simpa using hia
              exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hEq.symm.trans hii.symm⟩
          | mid S => rw [hw] at hval; simp [DV.mapV] at hval
          | bot c => rw [hw] at hval; simp [DV.mapV] at hval
      | mid S' =>
          cases hw : wF j with
          | top d => rw [hw] at hval; simp [DV.mapV] at hval
          | mid S =>
              rw [hw] at hval
              have hEq : S' = S.map thetaEmbF := by simpa [DV.mapV] using hval
              rw [hEq] at hia
              obtain ⟨d, -, hd⟩ := Finset.mem_map.mp hia
              exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hd⟩
          | bot c => rw [hw] at hval; simp [DV.mapV] at hval
      | bot c => simp at hia
    let rhoV : Fin (faceDim G + 1) → Fin (p + 1) :=
      fun j => invOn thetaEmbF (thetaEmbG j)
    have hRhoSpec : ∀ j, thetaEmbF (rhoV j) = thetaEmbG j := by
      intro j
      apply invOn_spec
      have hjG : thetaEmbG j ∈ G := by
        rw [hThetaEqG]
        simpa [faceEmb] using Finset.orderEmbOfFin_mem G (k := faceDim G + 1) (by
          have hp : 0 < G.card := Finset.card_pos.mpr hG
          dsimp [faceDim]
          omega) j
      have hjF : thetaEmbG j ∈ Finset.univ.image thetaEmbF := hGF hjG
      rw [Finset.mem_image] at hjF
      obtain ⟨i, -, hji⟩ := hjF
      exact ⟨i, hji⟩
    have hRhoStrict : StrictMono rhoV := by
      intro i j hij
      apply lt_of_not_ge
      intro hji
      have hleft : thetaEmbF (rhoV i) < thetaEmbF (rhoV j) := by
        rw [hRhoSpec i, hRhoSpec j]
        exact semiEmb_strictMono θG hij
      have hright : thetaEmbF (rhoV j) ≤ thetaEmbF (rhoV i) :=
        (semiEmb_strictMono θ).monotone hji
      exact (not_le_of_gt hleft) hright
    let rhoEmb : Fin (faceDim G + 1) ↪ Fin (p + 1) := ⟨rhoV, hRhoStrict.injective⟩
    let rho : Henry.SemiSimplexCategory.mk (faceDim G) ⟶ Henry.SemiSimplexCategory.mk p :=
      vhom rhoEmb hRhoStrict
    have hThetaFactor : θG = rho ≫ θ := by
      apply WideSubcategory.hom_ext
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext j
      change thetaEmbG j = thetaEmbF (rhoEmb j)
      exact (hRhoSpec j).symm
    have hzg : W.map rho.op zF = zG := faceMap_comp y θ θG rho hThetaFactor
    let gRG : elOf zF ⟶ elOf zG := ⟨rho.op, hzg⟩
    let iotaR := elι φ gRG
    let iotaREmb : Fin ((elNF φ (elOf zG)).m + 1) ↪ Fin ((elNF φ (elOf zF)).m + 1) :=
      semiEmb iotaR
    have hIotaFactor : iotaG = iotaR ≫ iotaF :=
      elι_factor_of_faces φ y θ θG rho hThetaFactor hzg
    have hThetaEmbFactor : thetaEmbG = rhoEmb.trans thetaEmbF := by
      ext j
      simpa [rhoEmb, RelEmbedding.trans_apply] using congrArg Fin.val (hRhoSpec j).symm
    have hIotaEmbFactor : iotaEmbG = iotaREmb.trans iotaEmbF := by
      change semiEmb iotaG = (semiEmb iotaR).trans (semiEmb iotaF)
      rw [hIotaFactor, semiEmb_comp]
    have hMapFactor : DV.mapV thetaEmbG iotaEmbG =
        DV.mapV thetaEmbF iotaEmbF ∘ DV.mapV rhoEmb iotaREmb := by
      calc
        DV.mapV thetaEmbG iotaEmbG =
            DV.mapV (rhoEmb.trans thetaEmbF) (iotaREmb.trans iotaEmbF) := by
              rw [hThetaEmbFactor, hIotaEmbFactor]
        _ = DV.mapV thetaEmbF iotaEmbF ∘ DV.mapV rhoEmb iotaREmb :=
              (mapV_comp thetaEmbF iotaEmbF rhoEmb iotaREmb).symm
    have hvG : (elNF φ (elOf y)).v ∘ thetaEmbG =
        iotaEmbG ∘ (elNF φ (elOf zG)).v := by
      change (elNF φ (elOf y)).v ∘ θG.1.toOrderHom =
        iotaG.1.toOrderHom ∘ (elNF φ (elOf zG)).v
      exact (elι_spec φ (elFaceHom y θG)).1
    let pullG := pullDV thetaEmbG iotaEmbG
    have hpullG : ∀ j, DV.mapV thetaEmbG iotaEmbG (pullG (w j)) = w j := by
      intro j
      have hjR : w j ∈ R := Finset.mem_image_of_mem _ (Finset.mem_univ j)
      cases hw : w j with
      | top i =>
          have hiR : DV.top i ∈ R := by rw [← hw]; exact hjR
          have hiG : i ∈ G := mem_dcylCarrier_top hiR
          have hiImg : i ∈ Finset.univ.image thetaEmbG := by
            rw [hThetaImgG]
            exact hiG
          obtain ⟨d, -, hdi⟩ := Finset.mem_image.mp hiImg
          exact mapV_pullDV_top thetaEmbG iotaEmbG ⟨d, hdi⟩
      | mid S =>
          have hSR : DV.mid S ∈ R := by rw [← hw]; exact hjR
          have hSG : S ⊆ G := subset_dcylCarrier_mid hSR
          have hSImg : S ⊆ Finset.univ.image thetaEmbG := by
            rw [hThetaImgG]
            exact hSG
          exact mapV_pullDV_mid thetaEmbG iotaEmbG hSImg
      | bot c =>
          have hcR : DV.bot c ∈ R := by rw [← hw]; exact hjR
          obtain ⟨S, hSR⟩ := exists_mid_of_bot_nonbottom hR hnot hcR
          obtain ⟨a, ha, hva⟩ := hR.2.2.2.2 c S hcR hSR
          have haG : a ∈ G := subset_dcylCarrier_mid hSR ha
          have haImg : a ∈ Finset.univ.image thetaEmbG := by
            rw [hThetaImgG]
            exact haG
          obtain ⟨d, -, hda⟩ := Finset.mem_image.mp haImg
          have hvd := congrFun hvG d
          have hcImage : ∃ e, iotaEmbG e = c := by
            refine ⟨(elNF φ (elOf zG)).v d, ?_⟩
            calc
              iotaEmbG ((elNF φ (elOf zG)).v d) = (elNF φ (elOf y)).v (thetaEmbG d) := hvd.symm
              _ = (elNF φ (elOf y)).v a := by rw [hda]
              _ = c := hva
          exact mapV_pullDV_bot thetaEmbG iotaEmbG hcImage
    have hlocalG := pullSimplex thetaEmbG (semiEmb_strictMono θG)
      iotaEmbG (semiEmb_strictMono iotaG) hvG R hR w rfl
      ((faceBdry φ y θ hk).toSemiSSet.app (op (Henry.SemiSimplexCategory.mk k)) σ).down.2.1
      pullG hpullG
    have hfun : (dcylDElMap φ gRG).f ∘ (pullG ∘ w) = wF := by
      funext j
      apply mapV_injective thetaEmbF iotaEmbF
      calc
        DV.mapV thetaEmbF iotaEmbF ((dcylDElMap φ gRG).f (pullG (w j))) =
            DV.mapV thetaEmbG iotaEmbG (pullG (w j)) := by
              have h := congrFun hMapFactor (pullG (w j))
              change DV.mapV thetaEmbF iotaEmbF
                (DV.mapV rhoEmb iotaREmb (pullG (w j))) =
                  DV.mapV thetaEmbG iotaEmbG (pullG (w j))
              simpa [Function.comp_apply] using h.symm
        _ = w j := hpullG j
        _ = DV.mapV thetaEmbF iotaEmbF (wF j) := by
              simpa [Function.comp_apply] using (congrFun hGlobalMap j)
    have hdesc : boundarySimplexDesc φ A y hfaces
        ((faceBdry φ y θ hk).toSemiSSet.app (op (Henry.SemiSimplexCategory.mk k)) σ) =
        faceCarrierDesc φ A y θG hθG hzG (pullG ∘ w) hlocalG.1 hlocalG.2 := by
      unfold boundarySimplexDesc
      rw [dif_neg hnot]
    have hnested := faceCarrierDesc_precomp φ A y θ θG rho hThetaFactor hk hθG hz hzG hzg
      (𝟙 (Henry.SemiSimplexCategory.mk k)) wF σ.down.2.1 σ.down.2.2 (pullG ∘ w)
      hlocalG.1 hlocalG.2 hfun
    have hcarrier : faceCarrierDesc φ A y θG hθG hzG (pullG ∘ w) hlocalG.1 hlocalG.2 =
        faceCarrierDesc φ A y θ hk hz wF σ.down.2.1 σ.down.2.2 := by
      simpa using hnested.symm
    rw [hdesc]
    calc
      _ = faceCarrierDesc φ A y θ hk hz wF σ.down.2.1 σ.down.2.2 := hcarrier
      _ = _ := by rfl

theorem exists_dcylDBoundary_desc_proof (A : Subfunctor W) {n : ℕ}
    (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hfaces : ∀ (k : ℕ) (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n),
      k ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk k))) :
    ∃ κ : dcylDBoundary.{u} (elNF φ (elOf y)).v ⟶ (cylSub φ A).obj,
      (∀ (e : A.toFunctor.Elements) (f : elOf y ⟶ W.elementsMk e.obj e.val.1)
        (hk : elDim (W.elementsMk e.obj e.val.1) ≠ n),
        (faceBdryGen φ y f hk).toSemiSSet ≫ κ =
          colimit.ι (cylSub φ A).DC (op e) ≫ (cylSub φ A).incl) ∧
      botBdry (elNF φ (elOf y)).v ≫ κ =
        uliftYonedaEquiv.symm (elNF φ (elOf y)).x ≫ (cylSub φ A).base := by
  classical
  let T := boundaryDescNat φ A y hfaces
  let κ := (cylSub φ A).topMap T
  have hFace : ∀ (k : ℕ) (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n)
      (hk : k ≠ n),
      (faceBdry φ y θ hk).toSemiSSet ≫ κ =
        colimit.ι (cylSub φ A).DC
          (op (A.toFunctor.elementsMk _ ⟨W.map θ.op y, hfaces k θ hk⟩)) ≫
          (cylSub φ A).incl := by
    intro k θ hk
    let z := W.map θ.op y
    have hz : z ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)) := hfaces k θ hk
    let eF := A.toFunctor.elementsMk _ ⟨z, hz⟩
    let K := (cylSub φ A).DC.obj (op eF)
    apply (Presheaf.colimitOfRepresentable
      K).hom_ext
    intro e
    let eG := (dcylDBoundaryComplex (elNF φ (elOf y)).v).toSemiSSet.elementsMk
      e.unop.obj ((faceBdry φ y θ hk).toSemiSSet.app e.unop.obj e.unop.val)
    have hι := (cylSub φ A).ι_topMap T (op eG)
    have hEVal : eG.val =
        ((faceBdry φ y θ hk).toSemiSSet.app e.unop.obj) e.unop.val := rfl
    have hι' : uliftYonedaEquiv.symm
        (((faceBdry φ y θ hk).toSemiSSet.app e.unop.obj) e.unop.val) ≫
          κ = T.app (op eG) :=
      (congrArg (fun a => uliftYonedaEquiv.symm a ≫ (cylSub φ A).topMap T) hEVal).symm.trans hι
    have hTapp : T.app (op eG) = boundarySimplexDesc φ A y hfaces
        (((faceBdry φ y θ hk).toSemiSSet.app e.unop.obj) e.unop.val) := rfl
    have hFaceRestrict : boundarySimplexDesc φ A y hfaces
        (((faceBdry φ y θ hk).toSemiSSet.app e.unop.obj) e.unop.val) =
        uliftYonedaEquiv.symm e.unop.val ≫
          colimit.ι (cylSub φ A).DC (op eF) ≫ (cylSub φ A).incl :=
      boundarySimplexDesc_face φ A y hfaces θ hk hz e.unop.val
    have hFaceGen := uliftYonedaEquiv_symm_comp e.unop.val
      (faceBdry φ y θ hk).toSemiSSet
    have hFaceComp := congrArg (fun g => g ≫ (cylSub φ A).topMap T) hFaceGen
    have hCore : (uliftYonedaEquiv.symm e.unop.val ≫ (faceBdry φ y θ hk).toSemiSSet) ≫
          κ =
        uliftYonedaEquiv.symm e.unop.val ≫
          colimit.ι (cylSub φ A).DC (op eF) ≫ (cylSub φ A).incl :=
      hFaceComp.trans (hι'.trans (hTapp.trans hFaceRestrict))
    change uliftYonedaEquiv.symm e.unop.val ≫ (faceBdry φ y θ hk).toSemiSSet ≫
        (cylSub φ A).topMap T =
      uliftYonedaEquiv.symm e.unop.val ≫
        colimit.ι (cylSub φ A).DC (op eF) ≫ (cylSub φ A).incl
    calc
      _ = (uliftYonedaEquiv.symm e.unop.val ≫ (faceBdry φ y θ hk).toSemiSSet) ≫
          κ := by cat_disch
      _ = _ := hCore
  refine ⟨κ, ?_, ?_⟩
  · intro e f hk
    let k := elDim (W.elementsMk e.obj e.val.1)
    have hk' : k ≠ n := by simpa [k] using hk
    have hObj : Henry.SemiSimplexCategory.mk k = unop e.obj := by
      rfl
    let θ₀ := f.hom.unop
    let θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n :=
      eqToHom hObj ≫ θ₀
    let z := W.map θ.op y
    have hgWid : Quiver.Hom.op (eqToHom hObj.symm) = 𝟙 e.obj := by rfl
    have hval : W.map (Quiver.Hom.op (eqToHom hObj.symm)) z = e.val.1 := by
      rw [hgWid, FunctorToTypes.map_id_apply]
      simpa [z, θ, θ₀] using f.map_val
    have hz : z ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)) := hfaces k θ hk'
    let eF : A.toFunctor.Elements :=
      A.toFunctor.elementsMk _ ⟨z, hz⟩
    let gA : eF ⟶ e :=
      { hom := Quiver.Hom.op (eqToHom hObj.symm)
        map_val := by
          apply Subtype.ext
          simpa [eF, hgWid] using hval }
    let gW : elOf z ⟶ W.elementsMk e.obj e.val.1 :=
      { hom := Quiver.Hom.op (eqToHom hObj.symm)
        map_val := hval }
    have hf : elFaceHom y θ ≫ gW = f := by
      apply Functor.Elements.Hom.ext
      change f.hom ≫ Quiver.Hom.op (eqToHom hObj.symm) = f.hom
      rw [hgWid]
      simp
    have hgA : (cylSub φ A).DC.map (Opposite.op gA) =
        (dcylDElMap φ gW).toSemiSSet := by rfl
    have hOpp : Quiver.Hom.op f = Quiver.Hom.op gW ≫
        Quiver.Hom.op (elFaceHom y θ) := by
      rw [← hf, op_comp]
    have hFullComp : (dcylDElMap φ f).toSemiSSet =
        (dcylDElMap φ gW).toSemiSSet ≫
          (dcylDElMap φ (elFaceHom y θ)).toSemiSSet := by
      change (dcylDFunctor φ).map (Quiver.Hom.op f) =
        (dcylDFunctor φ).map (Quiver.Hom.op gW) ≫
          (dcylDFunctor φ).map (Quiver.Hom.op (elFaceHom y θ))
      exact (congrArg (dcylDFunctor φ).map hOpp).trans
        ((dcylDFunctor φ).map_comp _ _)
    have hFull : (faceBdryGen φ y f hk).toSemiSSet ≫
          dcylDBoundaryι (elNF φ (elOf y)).v =
        ((cylSub φ A).DC.map (Opposite.op gA) ≫
          (faceBdry φ y θ hk').toSemiSSet) ≫
          dcylDBoundaryι (elNF φ (elOf y)).v := by
      rw [faceBdryGen_ι φ y f hk, hFullComp, ← hgA,
        ← faceBdry_ι φ y θ hk']
      cat_disch
    have hιInj (k : Henry.SemiSimplexCategoryᵒᵖ) : Function.Injective
        ((dcylDBoundaryι (elNF φ (elOf y)).v).app k) := by
      intro a b hab
      apply ULift.ext
      apply Subtype.ext
      exact congrArg (fun s => s.1) (congrArg ULift.down hab)
    have hComp : (faceBdryGen φ y f hk).toSemiSSet =
        (cylSub φ A).DC.map (Opposite.op gA) ≫
          (faceBdry φ y θ hk').toSemiSSet := by
      ext k σ
      apply hιInj k
      exact congrArg (fun q => q.app k σ) hFull
    have hCompW : (faceBdryGen φ y f hk).toSemiSSet =
        (dcylDElMap φ gW).toSemiSSet ≫ (faceBdry φ y θ hk').toSemiSSet := by
      rw [hComp, hgA]
      rfl
    have hcol : (cylSub φ A).DC.map (Opposite.op gA) ≫
        colimit.ι (cylSub φ A).DC (op eF) =
          colimit.ι (cylSub φ A).DC (op e) :=
      colimit.w (cylSub φ A).DC (Opposite.op gA)
    have hFacePre : (dcylDElMap φ gW).toSemiSSet ≫
        ((faceBdry φ y θ hk').toSemiSSet ≫ κ) =
          (dcylDElMap φ gW).toSemiSSet ≫
            (colimit.ι (cylSub φ A).DC (op eF) ≫ (cylSub φ A).incl) :=
      congrArg (fun q => (dcylDElMap φ gW).toSemiSSet ≫ q) (hFace k θ hk')
    have hcolW : (dcylDElMap φ gW).toSemiSSet ≫
        colimit.ι (cylSub φ A).DC (op eF) =
          colimit.ι (cylSub φ A).DC (op e) := by
      rw [← hgA]
      exact hcol
    have hAssoc : (dcylDElMap φ gW).toSemiSSet ≫
        (colimit.ι (cylSub φ A).DC (op eF) ≫ (cylSub φ A).incl) =
          ((dcylDElMap φ gW).toSemiSSet ≫
            colimit.ι (cylSub φ A).DC (op eF)) ≫ (cylSub φ A).incl := by
      cat_disch
    have hPost : (dcylDElMap φ gW).toSemiSSet ≫
        (colimit.ι (cylSub φ A).DC (op eF) ≫ (cylSub φ A).incl) =
          colimit.ι (cylSub φ A).DC (op e) ≫ (cylSub φ A).incl :=
      hAssoc.trans (congrArg (fun q => q ≫ (cylSub φ A).incl) hcolW)
    have hFirst : (faceBdryGen φ y f hk).toSemiSSet ≫ κ =
        (dcylDElMap φ gW).toSemiSSet ≫
          ((faceBdry φ y θ hk').toSemiSSet ≫ κ) := by
      rw [hCompW]
      cat_disch
    exact hFirst.trans (hFacePre.trans hPost)
  · let nf := elNF φ (elOf y)
    let wBot : Fin (nf.m + 1) → DV (elDim (elOf y)) nf.m := fun c => DV.bot c
    have hwBot : StrictMono wBot := by
      intro i j hij
      exact DV.bot_lt_bot.2 hij
    have hSBot : (dcylDBoundaryComplex nf.v).S (Finset.univ.image wBot) := by
      simpa [wBot] using
        (show (dcylDBoundaryComplex nf.v).S
            (Finset.univ.image (fun c => DV.bot c)) from
          ⟨⟨by simp, by simp, by simp, by simp, by simp⟩, Or.inl (by simp)⟩)
    let sigmaBot : ULift ((dcylDBoundaryComplex nf.v).Simplex nf.m) :=
      ULift.up ⟨wBot, hwBot, hSBot⟩
    let eBot := (dcylDBoundaryComplex nf.v).toSemiSSet.elementsMk
      (op (Henry.SemiSimplexCategory.mk nf.m)) sigmaBot
    have hBotGen : uliftYonedaEquiv.symm eBot.val = botBdry nf.v := by
      dsimp [eBot, sigmaBot, botBdry, Complex.simplexMap, wBot]
    have hbotBot : ∀ a ∈ Finset.univ.image wBot, ∃ c, a = DV.bot c := by
      intro a ha
      obtain ⟨c, -, hca⟩ := Finset.mem_image.mp ha
      exact ⟨c, hca.symm⟩
    have hCode : botCode wBot = (fun c => c) := by
      funext c
      rfl
    have hDesc : boundarySimplexDesc φ A y hfaces sigmaBot =
        bottomCarrierMap (cylSub φ A).base nf.x (botCode wBot)
          (botCode_strict hbotBot hwBot) :=
      boundarySimplexDesc_eq_bottom φ A y hfaces sigmaBot hbotBot
    have hCodeArrow : vhom (botCode wBot) (botCode_strict hbotBot hwBot) =
        𝟙 (Henry.SemiSimplexCategory.mk nf.m) := by
      apply WideSubcategory.hom_ext
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext c
      exact congrFun hCode c
    have hBaseCode : bottomCarrierMap (cylSub φ A).base nf.x (botCode wBot)
        (botCode_strict hbotBot hwBot) =
          uliftYonedaEquiv.symm nf.x ≫ (cylSub φ A).base := by
      unfold bottomCarrierMap
      rw [hCodeArrow]
      simp
    have hGenComp := congrArg (fun f => f ≫ κ) hBotGen.symm
    have hIota := (cylSub φ A).ι_topMap T (op eBot)
    have hTapp : T.app (op eBot) = boundarySimplexDesc φ A y hfaces sigmaBot := by rfl
    have hBotTop : botBdry nf.v ≫ κ =
        boundarySimplexDesc φ A y hfaces sigmaBot := hGenComp.trans (hIota.trans hTapp)
    exact hBotTop.trans (hDesc.trans hBaseCode)

#print axioms exists_dcylDBoundary_desc_proof

end HomotopyHypothesis.Cylinder.BoundaryDescription
