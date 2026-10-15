import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.Faces.FaceUnions
import HomotopyHypothesis.Realization.SemisimplicialComparison.CDeltaFacts
import HomotopyHypothesis.Realization.SemisimplicialComparison.CellAttach
import HomotopyHypothesis.Realization.SemisimplicialComparison.FaceUnions
import HomotopyHypothesis.Realization.SemisimplicialComparison.TopSimplex
/-!
# Free horn inclusions are weak equivalences of `C^Δ` (H Prop 5.2.3)

Let `W` be any class of weak equivalences of `C^Δ` (isomorphisms, composition, 2-out-of-6, gluing)
containing the maps between free simplices induced by face inclusions. Pushouts of free maps on
semi-simplicial subsets of a simplex are pushouts in `C^Δ`, the free maps on inclusions of such
subsets are cofibrations, and `W` is stable under pushout along cofibrations. Building the horn
`Λ^{n+1}_k` from the vertex `k` by adding one face at a time, each step is a pushout of the free
map on a smaller generalized horn of a face (induction on the number of vertices). Hence the free
vertex `F Δ₀ ⟶ F Λ^{n+1}_k` is in `W`, and so is the free horn inclusion by 2-out-of-3.
-/

universe u

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra

namespace HomotopyHypothesis.Realization.SemisimplicialComparison

open HomotopyHypothesis.Henry

/-- A pushout of a cell attachment is a cell attachment. -/
theorem CellData.isCellAttachment_of_isPushout {A B X P : AlgKan.{u}} {i : A ⟶ B} (d : CellData i)
    {f : A ⟶ X} {k : B ⟶ P} {j : X ⟶ P} (sq : IsPushout i f k j) : AlgKan.IsCellAttachment j := by
  refine ⟨d.n, d.a ≫ f.hom, d.y ≫ k.hom, ?_, fun Z g z hz => ?_⟩
  · rw [← Category.assoc, d.w, Category.assoc, Category.assoc]
    exact congrArg (d.a ≫ ·) (congrArg AlgKan.Hom.hom sq.w)
  · have hz' : (SemiSSet.boundary d.n).ι ≫ z = d.a ≫ (f ≫ g).hom := by
      rw [hz, Category.assoc]; rfl
    obtain ⟨b, ⟨hb₁, hb₂⟩, hbu⟩ := d.univ Z (f ≫ g) z hz'
    obtain ⟨p, hp₁, hp₂⟩ := sq.exists_desc b g hb₁
    refine ⟨p, ⟨hp₂, ?_⟩, fun p' ⟨h₁, h₂⟩ => sq.hom_ext ?_ (h₁.trans hp₂.symm)⟩
    · rw [Category.assoc, ← hb₂]
      exact congrArg (d.y ≫ ·) (congrArg AlgKan.Hom.hom hp₁)
    · rw [hp₁]
      apply hbu
      refine ⟨?_, ?_⟩
      · rw [← Category.assoc, sq.w, Category.assoc, h₁]
      · rw [← h₂, Category.assoc]; rfl

/-- The free map on `∂Δ_n ↪ Δ_n` is a cell attachment. -/
theorem isCellAttachment_of_isFreeOn_boundary {n : ℕ} {B D : AlgKan.{u}}
    {ηB : (SemiSSet.boundary.{u} n).toFunctor ⟶ B.X}
    {ηD : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ D.X}
    (hB : B.IsFreeOn ηB) (hD : D.IsFreeOn ηD) (ι : B ⟶ D)
    (hι : ηB ≫ ι.hom = (SemiSSet.boundary n).ι ≫ ηD) : AlgKan.IsCellAttachment ι := by
  refine ⟨n, ηB, ηD, hι.symm, fun Z g z hz => ?_⟩
  obtain ⟨g', hg', hu⟩ := hD Z z
  refine ⟨g', ⟨?_, hg'⟩, fun g'' h => hu g'' h.2⟩
  refine (hB Z (ηB ≫ g.hom)).unique ?_ rfl
  change ηB ≫ ι.hom ≫ g'.hom = ηB ≫ g.hom
  rw [← Category.assoc, hι, Category.assoc, hg', hz]

section Subsets

variable {N : ℕ}

/-- A chosen free object of `C^Δ` on a semi-simplicial subset of `Δ_N`. -/
noncomputable def FS (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) :
    CDelta.{u} :=
  (exists_free_subfunctor N S).choose

/-- Its generators. -/
noncomputable def ηS (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) :
    S.toFunctor ⟶ (FS S).obj.X :=
  (exists_free_subfunctor N S).choose_spec.choose

theorem FS_isFreeOn
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) :
    (FS S).obj.IsFreeOn (ηS S) :=
  (exists_free_subfunctor N S).choose_spec.choose_spec

/-- The free map on an inclusion of semi-simplicial subsets. -/
noncomputable def FMap
    {S' S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (h : S' ≤ S) : FS S' ⟶ FS S :=
  ObjectProperty.homMk ((FS_isFreeOn S') (FS S).obj (Subfunctor.homOfLe h ≫ ηS S)).exists.choose

theorem FMap_spec
    {S' S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (h : S' ≤ S) : ηS S' ≫ (FMap h).hom.hom = Subfunctor.homOfLe h ≫ ηS S :=
  ((FS_isFreeOn S') (FS S).obj (Subfunctor.homOfLe h ≫ ηS S)).exists.choose_spec

theorem FMap_comp
    {S'' S' S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (h₁ : S'' ≤ S') (h₂ : S' ≤ S) : FMap h₁ ≫ FMap h₂ = FMap (h₁.trans h₂) :=
  ObjectProperty.hom_ext _ (isFreeOn_hom_ext (FS_isFreeOn S'') (by
    change ηS S'' ≫ (FMap h₁).hom.hom ≫ (FMap h₂).hom.hom = _
    rw [← Category.assoc, FMap_spec, Category.assoc, FMap_spec, FMap_spec, ← Category.assoc]
    rfl))

theorem FMap_refl (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) :
    FMap (le_refl S) = 𝟙 _ :=
  ObjectProperty.hom_ext _ (isFreeOn_hom_ext (FS_isFreeOn S) (by
    rw [FMap_spec]
    rfl))

instance isIso_FMap_of_eq
    {S' S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (e : S' = S) : IsIso (FMap e.le) :=
  ⟨⟨FMap e.ge, by rw [FMap_comp, FMap_refl], by rw [FMap_comp, FMap_refl]⟩⟩

/-- **Free maps on inclusions of semi-simplicial subsets are cofibrations.** -/
theorem FMap_cofibration
    {S' S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (h : S' ≤ S) : cofibrations CDelta.{u} (FMap h) := by
  suffices H : ∀ (c : ℕ) (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj
      (Henry.SemiSimplexCategory.mk N))) (h : S' ≤ S), simplexCount.{u} S.toFunctor N = c →
      cofibrations CDelta.{u} (FMap h) from H _ S h rfl
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro S h hc
    by_cases hne : S' = S
    · subst hne
      rw [FMap_refl]
      exact MorphismProperty.multiplicativeClosure.id _
    · obtain ⟨m, S'', h₁, h₂, b, σ, sq, hcount⟩ := Simplicial.Faces.exists_topSimplex_pushout_rel_proof h hne
      have hc₁ := ih _ (hc ▸ hcount) S'' h₁ rfl
      obtain ⟨B, ηB, hB⟩ := exists_free_boundary.{u} m
      obtain ⟨D, ηD, hD⟩ := exists_free_simplex.{u} m
      obtain ⟨β, hβ, -⟩ := hB (FS S'').obj (b ≫ ηS S'')
      obtain ⟨ι, hι, -⟩ := hB D.obj ((SemiSSet.boundary m).ι ≫ ηD)
      obtain ⟨ybar, hy, -⟩ := hD (FS S).obj (σ ≫ ηS S)
      have sqA := isPushout_of_free sq hB (FS_isFreeOn S'') hD (FS_isFreeOn S) hβ hι
        (FMap_spec h₂) hy
      have hcell : AlgKan.IsCellAttachment (FMap h₂).hom :=
        CellData.isCellAttachment_of_isPushout
          (AlgKan.IsCellAttachment.data (isCellAttachment_of_isFreeOn_boundary hB hD ι hι))
          sqA.flip
      have hc₂ : cofibrations CDelta.{u} (FMap h₂) :=
        MorphismProperty.multiplicativeClosure.of _ (Or.inl hcell)
      rw [← FMap_comp h₁ h₂]
      exact (MorphismProperty.multiplicativeClosure _).comp_mem _ _ hc₁ hc₂

/-- Free maps on unions and intersections form pushout squares of `C^Δ`. -/
theorem isPushout_FMap_inf_sup
    (A B : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) :
    IsPushout (FMap (inf_le_right : A ⊓ B ≤ B)) (FMap (inf_le_left : A ⊓ B ≤ A))
      (FMap (le_sup_right : B ≤ A ⊔ B)) (FMap (le_sup_left : A ≤ A ⊔ B)) :=
  isPushout_of_alg (isPushout_of_free (Simplicial.Faces.isPushout_inf_sup_proof A B).flip (FS_isFreeOn _)
    (FS_isFreeOn _) (FS_isFreeOn _) (FS_isFreeOn _) (FMap_spec _) (FMap_spec _) (FMap_spec _)
    (FMap_spec _))

end Subsets

section Weq

variable (W : MorphismProperty CDelta.{u})
  (hW : IsWeakEquivalenceClass CDelta.{u} (cofibrations CDelta.{u}) W)
  (hWs : CDelta.simplexMaps ≤ W)

include hW in
theorem W_of_isIso {X Y : CDelta.{u}} (f : X ⟶ Y) (hf : IsIso f) : W f :=
  hW.1 _ hf

include hW in
theorem W_comp {X Y Z : CDelta.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : W f) (hg : W g) :
    W (f ≫ g) :=
  hW.2.1.comp_mem f g hf hg

include hW in
theorem W_of_comp_left {X Y Z : CDelta.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : W f)
    (hfg : W (f ≫ g)) : W g :=
  (hW.2.2.1 (𝟙 X) f g (by rwa [Category.id_comp]) hfg).2.2.1

include hW in
/-- Pushouts of trivial cofibrations are weak equivalences (gluing along the identity). -/
theorem W_of_isPushout {A B X P : CDelta.{u}} {i : A ⟶ B} {f : A ⟶ X} {k : B ⟶ P} {j : X ⟶ P}
    (sq : IsPushout i f k j) (hi : cofibrations CDelta.{u} i) (hiW : W i) : W j := by
  have sq₀ : IsPushout (𝟙 A) f f (𝟙 X) := IsPushout.of_horiz_isIso ⟨by simp⟩
  have h := hW.2.2.2 (𝟙 A) f f (𝟙 X) i f k j (𝟙 A) i (𝟙 X) j sq₀ sq
    (MorphismProperty.multiplicativeClosure.id _) hi (W_of_isIso W hW _ inferInstance) hiW
    (W_of_isIso W hW _ inferInstance)
    (by simp) (by simp) sq.w.symm (by simp)
  exact h

include hWs in
theorem W_FMap_faceSub {N : ℕ} {V' V : Finset (Fin (N + 1))} (hV' : V'.Nonempty) (h : V' ⊆ V) :
    W (FMap (show faceSub.{u} V' ≤ faceSub V from fun _ _ hf x => h (hf x))) := by
  obtain ⟨m, m', σ, e, e', he⟩ := Simplicial.Faces.exists_faceSub_iso_proof.{u} hV' h
  apply hWs
  refine ⟨m', m, σ, e'.hom ≫ ηS _, e.hom ≫ ηS _, isFreeOn_comp_iso (FS_isFreeOn _) e',
    isFreeOn_comp_iso (FS_isFreeOn _) e, ?_⟩
  rw [Category.assoc, FMap_spec, ← Category.assoc, he, Category.assoc]

theorem faceSub_singleton_le_hornSub {N : ℕ} {k : Fin (N + 1)} {V J : Finset (Fin (N + 1))}
    (hk : k ∈ V) (hJ : J.Nonempty) (hJk : J ⊆ V.erase k) :
    faceSub.{u} {k} ≤ hornSub V J := by
  obtain ⟨j, hj⟩ := hJ
  have hjk : j ≠ k := (Finset.mem_erase.1 (hJk hj)).1
  intro _ f hf
  refine ⟨j, hj, fun x => ?_⟩
  have := hf x
  rw [Finset.mem_singleton] at this
  rw [this, Finset.mem_erase]
  exact ⟨fun h' => hjk h'.symm, hk⟩

include hW hWs in
/-- **The free vertex of a generalized horn is a weak equivalence.** -/
theorem W_vertex_hornSub {N : ℕ} (k : Fin (N + 1)) : ∀ (c : ℕ) (V J : Finset (Fin (N + 1)))
    (_ : V.card = c) (hk : k ∈ V) (hJ : J.Nonempty) (hJk : J ⊆ V.erase k),
    W (FMap (faceSub_singleton_le_hornSub.{u} hk hJ hJk)) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro V J hc hk hJ
    induction hJ using Finset.Nonempty.cons_induction with
    | singleton j =>
      intro hJk
      have hj : j ∈ V.erase k := hJk (Finset.mem_singleton_self j)
      have hjk : j ≠ k := (Finset.mem_erase.1 hj).1
      have hkj : k ∈ V.erase j := Finset.mem_erase.2 ⟨fun h' => hjk h'.symm, hk⟩
      have e := Simplicial.Faces.hornSub_singleton_proof.{u} V j
      have h₁ := W_FMap_faceSub W hWs (Finset.singleton_nonempty k)
        (Finset.singleton_subset_iff.2 hkj)
      have := W_comp W hW h₁ (W_of_isIso W hW (FMap e.ge) (isIso_FMap_of_eq e.symm))
      rwa [FMap_comp] at this
    | cons j J hjJ hJne ihJ =>
      intro hJk
      have hjV : j ∈ V.erase k := hJk (Finset.mem_cons_self j J)
      have hjk : j ≠ k := (Finset.mem_erase.1 hjV).1
      have hJk' : J ⊆ V.erase k := fun x hx => hJk (Finset.mem_cons_of_mem hx)
      have hkj : k ∈ V.erase j := Finset.mem_erase.2 ⟨fun h' => hjk h'.symm, hk⟩
      have hJk'' : J ⊆ (V.erase j).erase k := by
        intro x hx
        have hx' := hJk' hx
        rw [Finset.mem_erase] at hx' ⊢
        refine ⟨hx'.1, Finset.mem_erase.2 ⟨fun h' => hjJ (h' ▸ hx), hx'.2⟩⟩
      let A := hornSub.{u} V J
      let B := faceSub.{u} (V.erase j)
      -- the vertex into `A`
      have hA : W (FMap (faceSub_singleton_le_hornSub.{u} hk hJne hJk')) := ihJ hJk'
      -- the vertex into `A ⊓ B`
      have hcard : (V.erase j).card < c := by
        rw [← hc]
        exact Finset.card_erase_lt_of_mem (Finset.mem_of_mem_erase hjV)
      have hAB := ih _ hcard (V.erase j) J rfl hkj hJne hJk''
      have eAB : A ⊓ B = hornSub (V.erase j) J := Simplicial.Faces.hornSub_inf_faceSub_proof V J j
      have hAB' : W (FMap ((faceSub_singleton_le_hornSub.{u} hkj hJne hJk'').trans eAB.ge)) := by
        have := W_comp W hW hAB (W_of_isIso W hW (FMap eAB.ge) (isIso_FMap_of_eq eAB.symm))
        rwa [FMap_comp] at this
      -- the vertex into `B`
      have hB : W (FMap (show faceSub.{u} {k} ≤ B from fun _ _ hf x => by
          have := hf x
          rw [Finset.mem_singleton] at this
          rw [this]
          exact hkj)) :=
        W_FMap_faceSub W hWs (Finset.singleton_nonempty k) (Finset.singleton_subset_iff.2 hkj)
      -- `A ⊓ B ⟶ B` is a trivial cofibration
      have hiW : W (FMap (inf_le_right : A ⊓ B ≤ B)) := by
        refine W_of_comp_left W hW hAB' ?_
        rw [FMap_comp]
        exact hB
      have hjW := W_of_isPushout W hW (isPushout_FMap_inf_sup A B) (FMap_cofibration _) hiW
      have e : A ⊔ B = hornSub V (Finset.cons j J hjJ) := by
        rw [Finset.cons_eq_insert, Simplicial.Faces.hornSub_insert_proof]
      have := W_comp W hW (W_comp W hW hA hjW) (W_of_isIso W hW (FMap e.le) (isIso_FMap_of_eq e))
      rwa [FMap_comp, FMap_comp] at this

theorem hornSub_le_faceSub {N : ℕ} (V J : Finset (Fin (N + 1))) :
    hornSub.{u} V J ≤ faceSub V := by
  rintro _ f ⟨j, -, hf⟩ x
  exact Finset.mem_of_mem_erase (hf x)

include hW hWs in
theorem W_free_horn (n : ℕ) (k : Fin (n + 2)) :
    W (FMap (hornSub_le_faceSub.{u} (Finset.univ : Finset (Fin (n + 2))) (Finset.univ.erase k))) := by
  have hne : (Finset.univ.erase k).Nonempty := by
    refine ⟨k.succAbove 0, Finset.mem_erase.2 ⟨Fin.succAbove_ne k 0, Finset.mem_univ _⟩⟩
  have h₁ := W_vertex_hornSub W hW hWs k _ Finset.univ (Finset.univ.erase k) rfl
    (Finset.mem_univ k) hne (le_refl _)
  have h₂ := W_FMap_faceSub W hWs (Finset.singleton_nonempty k)
    (Finset.subset_univ {k})
  refine W_of_comp_left W hW h₁ ?_
  rw [FMap_comp]
  exact h₂

/-- An isomorphism of semi-simplicial sets from an equality of subfunctors. -/
def subfunctorIsoOfEq {F : SemiSSet.{u}} {A B : Subfunctor F} (e : A = B) :
    A.toFunctor ≅ B.toFunctor where
  hom := Subfunctor.homOfLe e.le
  inv := Subfunctor.homOfLe e.ge

end Weq

/-- **H Prop 5.2.3**: the free maps on the horn inclusions `Λ^{n+1}_k ↪ Δ_{n+1}` are weak
equivalences of `C^Δ`. -/
theorem cDelta_horn_weakEquivalence_proof (n : ℕ) (k : Fin (n + 2)) {X Y : CDelta.{u}}
    (ηX : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ X.obj.X)
    (ηY : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk (n + 1)) ⟶ Y.obj.X)
    (hX : X.obj.IsFreeOn ηX) (hY : Y.obj.IsFreeOn ηY) (f : X ⟶ Y)
    (hf : ηX ≫ f.hom.hom = (SemiSSet.horn (n + 1) k).ι ≫ ηY) :
    weakEquivalences CDelta.{u} f := by
  change (sInf {W | IsWeakEquivalenceClass CDelta.{u} (cofibrations CDelta.{u}) W ∧
    CDelta.simplexMaps ≤ W} : MorphismProperty CDelta.{u}) f
  rw [MorphismProperty.sInf_iff]
  rintro W ⟨hW, hWs⟩
  let H := hornSub.{u} (Finset.univ : Finset (Fin (n + 2))) (Finset.univ.erase k)
  let U := faceSub.{u} (Finset.univ : Finset (Fin (n + 2)))
  have eH : SemiSSet.horn.{u} (n + 1) k = H := Simplicial.Faces.horn_eq_hornSub_proof n k
  let eU : U.toFunctor ≅ SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk (n + 1)) :=
    subfunctorIsoOfEq Simplicial.Faces.faceSub_univ_proof ≪≫ topIso (n + 1)
  have hX' := isFreeOn_comp_iso hX (subfunctorIsoOfEq eH).symm
  have hY' := isFreeOn_comp_iso hY eU
  let iX := isoOfIsFreeOn (FS_isFreeOn H) hX'
  let iY := isoOfIsFreeOn (FS_isFreeOn U) hY'
  let iXC : FS H ≅ X := (ObjectProperty.fullyFaithfulι _).preimageIso iX
  let iYC : FS U ≅ Y := (ObjectProperty.fullyFaithfulι _).preimageIso iY
  have key : iXC.hom ≫ f = FMap (hornSub_le_faceSub _ _) ≫ iYC.hom := by
    apply ObjectProperty.hom_ext
    apply isFreeOn_hom_ext (FS_isFreeOn H)
    have e1 : ηS H ≫ iX.hom.hom = (subfunctorIsoOfEq eH).symm.hom ≫ ηX := isoOfIsFreeOn_hom _ _
    have e2 : ηS U ≫ iY.hom.hom = eU.hom ≫ ηY := isoOfIsFreeOn_hom _ _
    have e3 : (subfunctorIsoOfEq eH).symm.hom ≫ (SemiSSet.horn (n + 1) k).ι =
        Subfunctor.homOfLe (hornSub_le_faceSub _ _) ≫ eU.hom := by
      ext d x
      rfl
    change ηS H ≫ iX.hom.hom ≫ f.hom.hom =
      ηS H ≫ (FMap (hornSub_le_faceSub _ _)).hom.hom ≫ iY.hom.hom
    calc ηS H ≫ iX.hom.hom ≫ f.hom.hom
        = ((subfunctorIsoOfEq eH).symm.hom ≫ ηX) ≫ f.hom.hom := by
          rw [← e1, Category.assoc]
      _ = (subfunctorIsoOfEq eH).symm.hom ≫ (SemiSSet.horn (n + 1) k).ι ≫ ηY := by
          rw [Category.assoc, hf]
      _ = Subfunctor.homOfLe (hornSub_le_faceSub _ _) ≫ eU.hom ≫ ηY := by
          rw [← Category.assoc, e3, Category.assoc]
      _ = ηS H ≫ (FMap (hornSub_le_faceSub _ _)).hom.hom ≫ iY.hom.hom := by
          rw [← e2, ← Category.assoc, ← Category.assoc, ← FMap_spec, Category.assoc]
  have hf' : f = iXC.inv ≫ FMap (hornSub_le_faceSub _ _) ≫ iYC.hom := by
    rw [← key, Iso.inv_hom_id_assoc]
  rw [hf']
  exact W_comp W hW (W_of_isIso W hW _ inferInstance)
    (W_comp W hW (W_free_horn W hW hWs n k) (W_of_isIso W hW _ inferInstance))

end HomotopyHypothesis.Realization.SemisimplicialComparison
