import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.TopSimplex.TopSimplex
import HomotopyHypothesis.Realization.SemisimplicialComparison.FaceUnions
import HomotopyHypothesis.Realization.SemisimplicialComparison.TopSimplex
/-!
# Faces and generalized horns of a standard simplex: proofs

Set identities for faces and generalized horns, union/intersection pushouts, faces as standard
simplices, and the relative top simplex attachment.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Simplicial.Faces

open HomotopyHypothesis.Henry

variable {N : ℕ}

theorem hornSub_inf_faceSub_proof (V J : Finset (Fin (N + 1))) (j : Fin (N + 1)) :
    HomotopyHypothesis.Realization.SemisimplicialComparison.hornSub.{u} V J ⊓
      HomotopyHypothesis.Realization.SemisimplicialComparison.faceSub (V.erase j) =
    HomotopyHypothesis.Realization.SemisimplicialComparison.hornSub (V.erase j) J := by
  classical
  ext d f
  change ((∃ k ∈ J, ∀ x,
      (ULift.down f).hom.toOrderHom x ∈ V.erase k) ∧
      ∀ x, (ULift.down f).hom.toOrderHom x ∈ V.erase j) ↔
    (∃ k ∈ J, ∀ x,
      (ULift.down f).hom.toOrderHom x ∈ (V.erase j).erase k)
  constructor
  · rintro ⟨⟨k, hk, hVk⟩, hj⟩
    refine ⟨k, hk, ?_⟩
    intro x
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hVk x)).1, hj x⟩
  · rintro ⟨k, hk, h⟩
    refine ⟨⟨k, hk, ?_⟩, ?_⟩
    · intro x
      rcases Finset.mem_erase.mp (h x) with ⟨hxk, hxj⟩
      exact Finset.mem_erase.mpr ⟨hxk, (Finset.mem_erase.mp hxj).2⟩
    · intro x
      exact (Finset.mem_erase.mp (h x)).2

#print axioms HomotopyHypothesis.Simplicial.Faces.hornSub_inf_faceSub_proof


theorem hornSub_insert_proof {N : ℕ} (V J : Finset (Fin (N + 1))) (j : Fin (N + 1)) :
    HomotopyHypothesis.Realization.SemisimplicialComparison.hornSub.{u} V (insert j J) =
      HomotopyHypothesis.Realization.SemisimplicialComparison.hornSub V J ⊔
        HomotopyHypothesis.Realization.SemisimplicialComparison.faceSub (V.erase j) := by
  classical
  ext d f
  change (∃ k ∈ insert j J, ∀ x,
      (ULift.down f).hom.toOrderHom x ∈ V.erase k) ↔
    ((∃ k ∈ J, ∀ x, (ULift.down f).hom.toOrderHom x ∈ V.erase k) ∨
      ∀ x, (ULift.down f).hom.toOrderHom x ∈ V.erase j)
  constructor
  · rintro ⟨k, hk, hV⟩
    rcases Finset.mem_insert.mp hk with hkj | hkJ
    · right
      simpa [hkj] using hV
    · exact Or.inl ⟨k, hkJ, hV⟩
  · rintro (⟨k, hk, hV⟩ | hj)
    · exact ⟨k, Finset.mem_insert_of_mem hk, hV⟩
    · exact ⟨j, Finset.mem_insert_self j J, hj⟩

#print axioms HomotopyHypothesis.Simplicial.Faces.hornSub_insert_proof


theorem hornSub_singleton_proof (V : Finset (Fin (N + 1))) (j : Fin (N + 1)) :
    HomotopyHypothesis.Realization.SemisimplicialComparison.hornSub.{u} V {j} =
      HomotopyHypothesis.Realization.SemisimplicialComparison.faceSub (V.erase j) := by
  classical
  ext d f
  change (∃ k ∈ ({j} : Finset (Fin (N + 1))), ∀ x,
      (ULift.down f).hom.toOrderHom x ∈ V.erase k) ↔
    ∀ x, (ULift.down f).hom.toOrderHom x ∈ V.erase j
  constructor
  · rintro ⟨k, hk, hV⟩
    have hkj : k = j := Finset.mem_singleton.mp hk
    subst k
    exact hV
  · intro hj
    exact ⟨j, Finset.mem_singleton.mpr rfl, hj⟩

#print axioms HomotopyHypothesis.Simplicial.Faces.hornSub_singleton_proof


theorem horn_eq_hornSub_proof (n : ℕ) (k : Fin (n + 2)) :
    SemiSSet.horn.{u} (n + 1) k =
      HomotopyHypothesis.Realization.SemisimplicialComparison.hornSub Finset.univ (Finset.univ.erase k) := by
  classical
  ext d f
  change (∃ j, j ≠ k ∧ j ∉ Set.range (ULift.down f).hom.toOrderHom) ↔
    (∃ j ∈ (Finset.univ.erase k : Finset (Fin (n + 2))), ∀ x,
      (ULift.down f).hom.toOrderHom x ∈
        (Finset.univ : Finset (Fin (n + 2))).erase j)
  constructor
  · rintro ⟨j, hjk, hjmiss⟩
    refine ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩, ?_⟩
    intro x
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro hx
    exact hjmiss ⟨x, hx⟩
  · rintro ⟨j, hjmem, hjface⟩
    refine ⟨j, (Finset.mem_erase.mp hjmem).1, ?_⟩
    intro hjrange
    rcases hjrange with ⟨x, hx⟩
    exact (Finset.mem_erase.mp (hjface x)).1 hx

#print axioms HomotopyHypothesis.Simplicial.Faces.horn_eq_hornSub_proof


theorem faceSub_univ_proof :
    HomotopyHypothesis.Realization.SemisimplicialComparison.faceSub.{u}
      (Finset.univ : Finset (Fin (N + 1))) = ⊤ := by
  classical
  ext d f
  change (∀ x, (ULift.down f).hom.toOrderHom x ∈
      (Finset.univ : Finset (Fin (N + 1)))) ↔ True
  simp

#print axioms HomotopyHypothesis.Simplicial.Faces.faceSub_univ_proof


theorem isPushout_inf_sup_proof {F : SemiSSet.{u}} (A B : Subfunctor F) :
    IsPushout (Subfunctor.homOfLe (inf_le_left : A ⊓ B ≤ A))
      (Subfunctor.homOfLe (inf_le_right : A ⊓ B ≤ B))
      (Subfunctor.homOfLe (le_sup_left : A ≤ A ⊔ B))
      (Subfunctor.homOfLe (le_sup_right : B ≤ A ⊔ B)) := by
  classical
  apply IsPushout.of_forall_isPushout_app
  intro d
  let iAB := Subfunctor.homOfLe (inf_le_left : A ⊓ B ≤ A)
  let iBB := Subfunctor.homOfLe (inf_le_right : A ⊓ B ≤ B)
  let iAS := Subfunctor.homOfLe (le_sup_left : A ≤ A ⊔ B)
  let iBS := Subfunctor.homOfLe (le_sup_right : B ≤ A ⊔ B)
  have hpb : IsPullback (iAB.app d) (iBB.app d) (iAS.app d) (iBS.app d) := by
    apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨?_, ?_, ?_⟩
    · change iAB.app d ≫ iAS.app d = iBB.app d ≫ iBS.app d
      ext x
      rfl
    · intro x y ⟨hxy, _⟩
      have hinj : Function.Injective (iAB.app d) := by
        rw [← mono_iff_injective]
        infer_instance
      exact hinj hxy
    · intro x y hxy
      have hv : (x : F.obj d) = y := by
        simpa [iAS, iBS, Subfunctor.homOfLe] using congrArg Subtype.val hxy
      refine ⟨⟨x.1, x.2, ?_⟩, ?_, ?_⟩
      · rw [hv]
        exact y.2
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        exact hv
  haveI : Mono (iAS.app d) := by
    dsimp [iAS]
    infer_instance
  have hcover : Set.range (iAS.app d) ⊔ Set.range (iBS.app d) = Set.univ := by
    change Set.range (iAS.app d) ∪ Set.range (iBS.app d) = Set.univ
    ext x
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      rcases x.2 with hxA | hxB
      · left
        refine ⟨⟨x.1, hxA⟩, ?_⟩
        apply Subtype.ext
        rfl
      · right
        refine ⟨⟨x.1, hxB⟩, ?_⟩
        apply Subtype.ext
        rfl
  have hinj : ∀ (x y : B.toFunctor.obj d)
      (_ : x ∉ Set.range (iBB.app d)) (_ : y ∉ Set.range (iBB.app d)),
      iBS.app d x = iBS.app d y → x = y := by
    intro x y _ _ hxy
    apply Subtype.ext
    simpa [iBS, Subfunctor.homOfLe] using congrArg Subtype.val hxy
  exact Types.isPushout_of_isPullback_of_mono' hpb hcover hinj

#print axioms HomotopyHypothesis.Simplicial.Faces.isPushout_inf_sup_proof


theorem exists_faceSub_iso_proof {V' V : Finset (Fin (N + 1))} (hV' : V'.Nonempty)
    (h : V' ⊆ V) :
    ∃ (m m' : ℕ) (σ : Henry.SemiSimplexCategory.mk m' ⟶ Henry.SemiSimplexCategory.mk m)
      (e : SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m) ≅
        (HomotopyHypothesis.Realization.SemisimplicialComparison.faceSub V).toFunctor)
      (e' : SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m') ≅
        (HomotopyHypothesis.Realization.SemisimplicialComparison.faceSub V').toFunctor),
      e'.hom ≫ Subfunctor.homOfLe
        (show HomotopyHypothesis.Realization.SemisimplicialComparison.faceSub.{u} V' ≤
          HomotopyHypothesis.Realization.SemisimplicialComparison.faceSub V from fun _ _ hf x => h (hf x)) =
        SemiSSet.stdSimplex.map σ ≫ e.hom := by
  classical
  have hVne : V.Nonempty := by
    obtain ⟨v, hv⟩ := hV'
    exact ⟨v, h hv⟩
  have hVpos : 0 < V.card := Finset.card_pos.mpr hVne
  have hV'pos : 0 < V'.card := Finset.card_pos.mpr hV'
  let m := V.card - 1
  let m' := V'.card - 1
  have hmcard : V.card = m + 1 := by dsimp [m]; omega
  have hm'card : V'.card = m' + 1 := by dsimp [m']; omega
  let eV : Fin (m + 1) ≃o V := V.orderIsoOfFin hmcard
  let eV' : Fin (m' + 1) ≃o V' := V'.orderIsoOfFin hm'card
  let α : Fin (m + 1) ↪o Fin (N + 1) :=
    eV.toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ V))
  let α' : Fin (m' + 1) ↪o Fin (N + 1) :=
    eV'.toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ V'))
  let σHom : (Henry.SemiSimplexCategory.mk m).obj ⟶
      (Henry.SemiSimplexCategory.mk N).obj := SimplexCategory.Hom.mk α.toOrderHom
  have hσMono : Mono σHom := by
    rw [SimplexCategory.mono_iff_injective]
    exact α.injective
  let σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N :=
    ⟨σHom, hσMono⟩
  let σ'Hom : (Henry.SemiSimplexCategory.mk m').obj ⟶
      (Henry.SemiSimplexCategory.mk N).obj := SimplexCategory.Hom.mk α'.toOrderHom
  have hσ'Mono : Mono σ'Hom := by
    rw [SimplexCategory.mono_iff_injective]
    exact α'.injective
  let σ' : Henry.SemiSimplexCategory.mk m' ⟶ Henry.SemiSimplexCategory.mk N :=
    ⟨σ'Hom, hσ'Mono⟩
  let FV := HomotopyHypothesis.Realization.SemisimplicialComparison.faceSub.{u} V
  let FV' := HomotopyHypothesis.Realization.SemisimplicialComparison.faceSub.{u} V'
  have hσV : ULift.up σ ∈ FV.obj (op (Henry.SemiSimplexCategory.mk m)) := by
    change ∀ i, α i ∈ V
    intro i
    exact (eV i).property
  have hσ'V : ULift.up σ' ∈ FV'.obj (op (Henry.SemiSimplexCategory.mk m')) := by
    change ∀ i, α' i ∈ V'
    intro i
    exact (eV' i).property
  let fV := HomotopyHypothesis.Approximation.TopSimplex.simplexMapToSub FV (ULift.up σ) hσV
  let fV' := HomotopyHypothesis.Approximation.TopSimplex.simplexMapToSub FV' (ULift.up σ') hσ'V
  have hbijV (d : Henry.SemiSimplexCategoryᵒᵖ) : Function.Bijective (fV.app d) := by
    constructor
    · exact HomotopyHypothesis.Approximation.TopSimplex.simplexMapToSub_app_injective FV
        (ULift.up σ) hσV
    · intro y
      rcases y with ⟨y, hy⟩
      let φ := y.down.hom.toOrderHom
      change ∀ i, φ i ∈ V at hy
      haveI : Mono y.down.hom := y.down.property
      have hφinj : Function.Injective φ :=
        (SimplexCategory.mono_iff_injective).1 (inferInstance : Mono y.down.hom)
      have hφstrict : StrictMono φ := φ.monotone.strictMono_of_injective hφinj
      let gV : Fin (d.unop.obj.len + 1) → V := fun i => ⟨φ i, hy i⟩
      have hgV : StrictMono gV := by
        intro i j hij
        exact hφstrict hij
      let q : Fin (d.unop.obj.len + 1) ↪o Fin (m + 1) :=
        (OrderEmbedding.ofStrictMono gV hgV).trans eV.symm.toOrderEmbedding
      let qHom : d.unop.obj ⟶ (Henry.SemiSimplexCategory.mk m).obj :=
        SimplexCategory.Hom.mk q.toOrderHom
      have hqHom : Mono qHom := by
        rw [SimplexCategory.mono_iff_injective]
        exact q.injective
      let τ : d.unop ⟶ Henry.SemiSimplexCategory.mk m := ⟨qHom, hqHom⟩
      have hfactor : τ ≫ σ = y.down := by
        apply Henry.SemiSimplexCategory.incl.map_injective
        simp only [Functor.map_comp]
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext i
        change (eV (eV.symm ⟨φ i, hy i⟩)).val = φ i
        exact congrArg Subtype.val (eV.apply_symm_apply ⟨φ i, hy i⟩)
      let z : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj d :=
        ULift.up τ
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change ULift.up (τ ≫ σ) = y
      rw [hfactor]
  have hbijV' (d : Henry.SemiSimplexCategoryᵒᵖ) : Function.Bijective (fV'.app d) := by
    constructor
    · exact HomotopyHypothesis.Approximation.TopSimplex.simplexMapToSub_app_injective FV'
        (ULift.up σ') hσ'V
    · intro y
      rcases y with ⟨y, hy⟩
      let φ := y.down.hom.toOrderHom
      change ∀ i, φ i ∈ V' at hy
      haveI : Mono y.down.hom := y.down.property
      have hφinj : Function.Injective φ :=
        (SimplexCategory.mono_iff_injective).1 (inferInstance : Mono y.down.hom)
      have hφstrict : StrictMono φ := φ.monotone.strictMono_of_injective hφinj
      let gV' : Fin (d.unop.obj.len + 1) → V' := fun i => ⟨φ i, hy i⟩
      have hgV' : StrictMono gV' := by
        intro i j hij
        exact hφstrict hij
      let q : Fin (d.unop.obj.len + 1) ↪o Fin (m' + 1) :=
        (OrderEmbedding.ofStrictMono gV' hgV').trans eV'.symm.toOrderEmbedding
      let qHom : d.unop.obj ⟶ (Henry.SemiSimplexCategory.mk m').obj :=
        SimplexCategory.Hom.mk q.toOrderHom
      have hqHom : Mono qHom := by
        rw [SimplexCategory.mono_iff_injective]
        exact q.injective
      let τ : d.unop ⟶ Henry.SemiSimplexCategory.mk m' := ⟨qHom, hqHom⟩
      have hfactor : τ ≫ σ' = y.down := by
        apply Henry.SemiSimplexCategory.incl.map_injective
        simp only [Functor.map_comp]
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext i
        change (eV' (eV'.symm ⟨φ i, hy i⟩)).val = φ i
        exact congrArg Subtype.val (eV'.apply_symm_apply ⟨φ i, hy i⟩)
      let z : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m')).obj d :=
        ULift.up τ
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change ULift.up (τ ≫ σ') = y
      rw [hfactor]
  have hIsoV : IsIso fV := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro d
    rw [isIso_iff_bijective]
    exact hbijV d
  have hIsoV' : IsIso fV' := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro d
    rw [isIso_iff_bijective]
    exact hbijV' d
  let e : SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m) ≅ FV.toFunctor :=
    asIso fV
  let e' : SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m') ≅ FV'.toFunctor :=
    asIso fV'
  let incV : V' ↪o V := {
    toFun := fun x => ⟨x.1, h x.2⟩
    inj' := by
      intro x y hxy
      apply Subtype.ext
      simpa using congrArg (fun z : V => (z : Fin (N + 1))) hxy
    map_rel_iff' := by
      intro x y
      change (x.1 ≤ y.1) ↔ (x.1 ≤ y.1)
      rfl
  }
  let θ : Fin (m' + 1) ↪o Fin (m + 1) :=
    eV'.toOrderEmbedding.trans (incV.trans eV.symm.toOrderEmbedding)
  let θHom : (Henry.SemiSimplexCategory.mk m').obj ⟶
      (Henry.SemiSimplexCategory.mk m).obj := SimplexCategory.Hom.mk θ.toOrderHom
  have hθMono : Mono θHom := by
    rw [SimplexCategory.mono_iff_injective]
    exact θ.injective
  let τ : Henry.SemiSimplexCategory.mk m' ⟶ Henry.SemiSimplexCategory.mk m :=
    ⟨θHom, hθMono⟩
  have hfactor : τ ≫ σ = σ' := by
    apply Henry.SemiSimplexCategory.incl.map_injective
    simp only [Functor.map_comp]
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    change (eV (eV.symm (incV (eV' i)))).val = (eV' i).val
    exact congrArg Subtype.val (eV.apply_symm_apply (incV (eV' i)))
  have hVι : fV ≫ FV.ι = SemiSSet.stdSimplex.map σ := by
    ext d z
    rfl
  have hV'ι : fV' ≫ FV'.ι = SemiSSet.stdSimplex.map σ' := by
    ext d z
    rfl
  refine ⟨m, m', τ, e, e', ?_⟩
  apply (cancel_mono FV.ι).1
  calc
    (fV' ≫ Subfunctor.homOfLe
        (show FV' ≤ FV from fun _ _ hf i => h (hf i))) ≫ FV.ι =
        SemiSSet.stdSimplex.map σ' := by
      simp only [Category.assoc, Subfunctor.homOfLe_ι, hV'ι]
    _ = SemiSSet.stdSimplex.map (τ ≫ σ) := by rw [hfactor]
    _ = SemiSSet.stdSimplex.map τ ≫ SemiSSet.stdSimplex.map σ := by
      rw [← Functor.map_comp]
    _ = (SemiSSet.stdSimplex.map τ ≫ fV) ≫ FV.ι := by
      rw [← hVι]
      simp [Category.assoc]

#print axioms HomotopyHypothesis.Simplicial.Faces.exists_faceSub_iso_proof


theorem exists_topSimplex_pushout_rel_proof
    {S' S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (hle : S' ≤ S) (hne : S' ≠ S) :
    ∃ (m : ℕ) (S'' : Subfunctor (SemiSSet.stdSimplex.{u}.obj
        (Henry.SemiSimplexCategory.mk N)))
      (h₁ : S' ≤ S'') (h₂ : S'' ≤ S) (b : (SemiSSet.boundary.{u} m).toFunctor ⟶ S''.toFunctor)
      (σ : SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m) ⟶ S.toFunctor),
      IsPushout b (SemiSSet.boundary.{u} m).ι (Subfunctor.homOfLe h₂) σ ∧
      HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount S''.toFunctor N <
        HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount S.toFunctor N := by
  classical
  have hnotle : ¬ S ≤ S' := by
    intro h
    exact hne (le_antisymm hle h)
  have hdiff : ∃ d x, x ∈ S.obj d ∧ x ∉ S'.obj d := by
    by_contra h
    apply hnotle
    intro d x hx
    by_contra hxs
    exact h ⟨d, x, hx, hxs⟩
  obtain ⟨d₀, x₀, hx₀S, hx₀not⟩ := hdiff
  let p₀ := d₀.unop.obj.len
  have hp₀N : p₀ ≤ N :=
    HomotopyHypothesis.Approximation.TopSimplex.simplex_dimension_le (N := N) (d := d₀) (x := x₀)
  have hd₀ : d₀ = op (Henry.SemiSimplexCategory.mk p₀) := by
    apply congrArg op
    apply WideSubcategory.ext
    exact (SimplexCategory.mk_len d₀.unop.obj).symm
  have hx₀S' : x₀ ∈ S.obj (op (Henry.SemiSimplexCategory.mk p₀)) := by
    simpa [p₀, hd₀] using hx₀S
  have hx₀not' : x₀ ∉ S'.obj (op (Henry.SemiSimplexCategory.mk p₀)) := by
    simpa [p₀, hd₀] using hx₀not
  let dims : Finset (Fin (N + 1)) := Finset.univ.filter fun i =>
    ∃ x, x ∈ S.obj (op (Henry.SemiSimplexCategory.mk i.1)) ∧
      x ∉ S'.obj (op (Henry.SemiSimplexCategory.mk i.1))
  have hdims : dims.Nonempty := by
    refine ⟨⟨p₀, by omega⟩, ?_⟩
    simp only [dims, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x₀, hx₀S', hx₀not'⟩
  let mFin := dims.max' hdims
  let m := mFin.1
  have hmN : m ≤ N := by omega
  have hmMem : (mFin : Fin (N + 1)) ∈ dims := Finset.max'_mem dims hdims
  have hmWitness : ∃ x, x ∈ S.obj (op (Henry.SemiSimplexCategory.mk m)) ∧
      x ∉ S'.obj (op (Henry.SemiSimplexCategory.mk m)) := by
    simpa [dims, m] using hmMem
  obtain ⟨σ₀, hσS, hσnot⟩ := hmWitness
  let sigma : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj
      (op (Henry.SemiSimplexCategory.mk m)) := σ₀
  have hσS' : sigma ∈ S.obj (op (Henry.SemiSimplexCategory.mk m)) := hσS
  have hσnotS' : sigma ∉ S'.obj (op (Henry.SemiSimplexCategory.mk m)) := hσnot
  have hmaxOut : ∀ d, (∃ x, x ∈ S.obj d ∧ x ∉ S'.obj d) → d.unop.obj.len ≤ m := by
    intro d hd
    obtain ⟨x, hxS, hxnot⟩ := hd
    let p := d.unop.obj.len
    have hpN : p ≤ N :=
      HomotopyHypothesis.Approximation.TopSimplex.simplex_dimension_le (N := N) (d := d) (x := x)
    have hd' : d = op (Henry.SemiSimplexCategory.mk p) := by
      apply congrArg op
      apply WideSubcategory.ext
      exact (SimplexCategory.mk_len d.unop.obj).symm
    have hxS' : x ∈ S.obj (op (Henry.SemiSimplexCategory.mk p)) := by
      simpa [p, hd'] using hxS
    have hxnot' : x ∉ S'.obj (op (Henry.SemiSimplexCategory.mk p)) := by
      simpa [p, hd'] using hxnot
    have hpmem : (⟨p, by omega⟩ : Fin (N + 1)) ∈ dims := by
      simp only [dims, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hxS', hxnot'⟩
    have hple : (⟨p, by omega⟩ : Fin (N + 1)) ≤ mFin := Finset.le_max' dims _ hpmem
    exact Fin.le_iff_val_le_val.mp hple
  let S'' : Subfunctor (SemiSSet.stdSimplex.{u}.obj
      (Henry.SemiSimplexCategory.mk N)) := {
    obj := fun d => {x | x ∈ S.obj d ∧ ∀ hd : d = op (Henry.SemiSimplexCategory.mk m), hd ▸ x ≠ sigma}
    map := by
      intro U V i x hx
      refine ⟨S.map i hx.1, ?_⟩
      intro hV
      subst V
      intro heq
      have hdim : m ≤ U.unop.obj.len := by
        have hle := @SimplexCategory.len_le_of_mono _ _ i.unop.hom i.unop.property
        simpa [Henry.SemiSimplexCategory.mk] using hle
      by_cases hum : U.unop.obj.len = m
      · have hU : U = op (Henry.SemiSimplexCategory.mk m) := by
          apply congrArg op
          apply WideSubcategory.ext
          calc
            U.unop.obj = SimplexCategory.mk U.unop.obj.len :=
              (SimplexCategory.mk_len U.unop.obj).symm
            _ = SimplexCategory.mk m := by rw [hum]
        subst U
        have hiUnop : i.unop = 𝟙 _ := by
          haveI : Mono i.unop.hom := i.unop.property
          apply WideSubcategory.hom_ext
          exact SimplexCategory.eq_id_of_mono i.unop.hom
        have hi : i = 𝟙 _ := by
          apply Quiver.Hom.unop_inj
          exact hiUnop
        have hxEq : x = sigma := by simpa [hi] using heq
        exact hx.2 rfl hxEq
      · have hlt : m < U.unop.obj.len := by omega
        have hxnotS' : x ∉ S'.obj U := by
          intro hxS'
          apply hσnotS'
          have hmem : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).map i x ∈
              S'.obj (op (Henry.SemiSimplexCategory.mk m)) := S'.map i hxS'
          have heq' : (SemiSSet.stdSimplex.{u}.obj
              (Henry.SemiSimplexCategory.mk N)).map i x = sigma := by
            simpa using heq
          rw [heq'] at hmem
          exact hmem
        have hupper : U.unop.obj.len ≤ m := hmaxOut U ⟨x, hx.1, hxnotS'⟩
        omega
  }
  have hS''le : S'' ≤ S := by
    intro d x hx
    exact hx.1
  have hS'le : S' ≤ S'' := by
    intro d x hx
    refine ⟨hle d hx, ?_⟩
    intro hd heq
    have hmem : hd ▸ x ∈ S'.obj (op (Henry.SemiSimplexCategory.mk m)) := by
      cases hd
      exact hx
    rw [heq] at hmem
    exact hσnotS' hmem
  let smap := HomotopyHypothesis.Approximation.TopSimplex.simplexMapToSub S sigma hσS'
  let b0 := (SemiSSet.boundary.{u} m).ι ≫ smap
  let b : (SemiSSet.boundary.{u} m).toFunctor ⟶ S''.toFunctor := by
    refine { app := fun d => ↾fun z => ?_, naturality := ?_ }
    · refine ⟨(b0.app d z).1, ?_⟩
      refine ⟨(b0.app d z).2, ?_⟩
      intro hd
      subst d
      simpa [b0] using
        HomotopyHypothesis.Approximation.TopSimplex.boundary_map_avoids_top S sigma hσS' z
    · intro X Y f
      ext z
      apply Subtype.ext
      simpa [b0, Subfunctor.toFunctor] using
        congrArg Subtype.val (b0.naturality_apply f z)
  have hcount : HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount S''.toFunctor N <
      HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount S.toFunctor N := by
    classical
    let cellsD := HomotopyHypothesis.Approximation.TopSimplex.simplexCells N S''
    let cellsS := HomotopyHypothesis.Approximation.TopSimplex.simplexCells N S
    haveI : Finite cellsD := HomotopyHypothesis.Approximation.TopSimplex.simplexCells_finite N S''
    haveI : Finite cellsS := HomotopyHypothesis.Approximation.TopSimplex.simplexCells_finite N S
    letI : Fintype cellsD := Fintype.ofFinite _
    letI : Fintype cellsS := Fintype.ofFinite _
    let f : cellsD → cellsS := fun z =>
      ⟨z.1, ⟨z.2.1, (show z.2.1 ∈ S.obj
        (op (Henry.SemiSimplexCategory.mk z.1.1)) from z.2.2.1)⟩⟩
    have hf : Function.Injective f := by
      intro a b hab
      rcases a with ⟨p, x⟩
      rcases b with ⟨q, y⟩
      dsimp [f] at hab
      have hidx : (⟨p.1, by omega⟩ : Fin (N + 1)) = ⟨q.1, by omega⟩ :=
        congrArg Sigma.fst hab
      have hp : p.1 = q.1 := by
        simpa using congrArg (fun i : Fin (N + 1) => i.1) hidx
      have hp' : p = q := Fin.ext hp
      subst q
      have hsub := eq_of_heq (Sigma.ext_iff.mp hab).2
      have hval : x.1 = y.1 :=
        congrArg (fun z : S.toFunctor.obj
          (op (Henry.SemiSimplexCategory.mk p.1)) => z.1) hsub
      have hxy : x = y := Subtype.ext hval
      subst y
      rfl
    let pTop : Fin (N + 1) := ⟨m, by omega⟩
    let top : cellsS := ⟨pTop, ⟨sigma, hσS'⟩⟩
    have htop : top ∉ Set.range f := by
      rintro ⟨⟨p, x⟩, h⟩
      dsimp [f, top] at h
      have hp : p = pTop := (Sigma.ext_iff.mp h).1
      have hsub := (Sigma.ext_iff.mp h).2
      subst p
      have hsub' : (⟨x.1, (show x.1 ∈ S.obj _ from x.2.1)⟩ :
          S.toFunctor.obj (op (Henry.SemiSimplexCategory.mk m))) = ⟨sigma, hσS'⟩ :=
        eq_of_heq hsub
      have hσx : x.1 = sigma := congrArg (fun z : S.toFunctor.obj
        (op (Henry.SemiSimplexCategory.mk m)) => z.1) hsub'
      exact x.2.2 rfl hσx
    simp only [HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount, Nat.card_eq_fintype_card]
    exact Fintype.card_lt_of_injective_not_surjective f hf (by
      intro hsurj
      exact htop (hsurj top))
  have hpush : IsPushout b (SemiSSet.boundary.{u} m).ι
      (Subfunctor.homOfLe hS''le) smap := by
    classical
    let incl := Subfunctor.homOfLe hS''le
    let idM : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj
        (op (Henry.SemiSimplexCategory.mk m)) := ULift.up (𝟙 (Henry.SemiSimplexCategory.mk m))
    have hsid : (smap.app (op (Henry.SemiSimplexCategory.mk m)) idM).1 = sigma := by
      change ((HomotopyHypothesis.Approximation.TopSimplex.simplexMapToSub S sigma hσS').app
        (op (Henry.SemiSimplexCategory.mk m)) idM).1 = sigma
      rw [HomotopyHypothesis.Approximation.TopSimplex.simplexMapToSub_app_val]
      simp [idM]
    have hcomm : b ≫ incl = (SemiSSet.boundary.{u} m).ι ≫ smap := by
      ext d z
      rfl
    apply IsPushout.of_forall_isPushout_app
    intro d
    have hpb : IsPullback (b.app d) ((SemiSSet.boundary.{u} m).ι.app d)
        (incl.app d) (smap.app d) := by
      apply (Types.isPullback_iff _ _ _ _).2
      refine ⟨?_, ?_⟩
      · simpa using congrArg (fun α => α.app d) hcomm
      · refine ⟨?_, ?_⟩
        · intro x y hxy
          apply Subtype.ext
          exact hxy.2
        · intro x y hxy
          by_cases hybd : y ∈ (SemiSSet.boundary.{u} m).obj d
          · let z : (SemiSSet.boundary.{u} m).toFunctor.obj d := ⟨y, hybd⟩
            refine ⟨z, ?_, ?_⟩
            · have hcommd := congrArg (fun α => α.app d) hcomm
              have hcommz : incl.app d (b.app d z) = smap.app d y := by
                simpa [z] using congrArg (fun f => f z) hcommd
              have hinj : Function.Injective (incl.app d) := by
                rw [← mono_iff_injective]
                infer_instance
              apply hinj
              calc
                incl.app d (b.app d z) = smap.app d y := hcommz
                _ = incl.app d x := hxy.symm
            · rfl
          · let p := d.unop.obj.len
            have hple : p ≤ m := by
              have hle' := @SimplexCategory.len_le_of_mono _ _ y.down.hom y.down.property
              simpa [Henry.SemiSimplexCategory.mk] using hle'
            by_cases hpm : p = m
            · have hd : d = op (Henry.SemiSimplexCategory.mk m) := by
                apply congrArg op
                apply WideSubcategory.ext
                calc
                  d.unop.obj = SimplexCategory.mk d.unop.obj.len :=
                    (SimplexCategory.mk_len d.unop.obj).symm
                  _ = SimplexCategory.mk m := by
                    simpa [p] using congrArg (fun n : ℕ => SimplexCategory.mk n) hpm
              subst d
              have hyId : y = ULift.up (𝟙 (Henry.SemiSimplexCategory.mk m)) := by
                apply ULift.ext
                haveI : Mono y.down.hom := y.down.property
                apply WideSubcategory.hom_ext
                exact SimplexCategory.eq_id_of_mono y.down.hom
              have hxσ : x.1 = sigma := by
                have hval := congrArg (fun z : S.toFunctor.obj
                  (op (Henry.SemiSimplexCategory.mk m)) => z.1) hxy
                have hval' : x.1 = (smap.app
                    (op (Henry.SemiSimplexCategory.mk m)) idM).1 := by
                  simpa [incl, Subfunctor.homOfLe, hyId] using hval
                exact hval'.trans hsid
              exact False.elim (x.2.2 rfl hxσ)
            · have hlt : p < m := lt_of_le_of_ne hple hpm
              have hySurj : ¬Function.Surjective y.down.hom.toOrderHom := by
                intro hs
                haveI : Mono y.down.hom := y.down.property
                have hinj := (SimplexCategory.mono_iff_injective).1
                  (inferInstance : Mono y.down.hom)
                have hcard₁ := Fintype.card_le_of_injective y.down.hom.toOrderHom hinj
                have hcard₂ := Fintype.card_le_of_surjective y.down.hom.toOrderHom hs
                simp only [Fintype.card_fin] at hcard₁ hcard₂
                omega
              have hmissing : ∃ j : Fin (m + 1),
                  j ∉ Set.range y.down.hom.toOrderHom := by
                by_contra hn
                push_neg at hn
                exact hySurj hn
              obtain ⟨j, hj⟩ := hmissing
              have hybd : y ∈ (SemiSSet.boundary.{u} m).obj d := ⟨j, hj⟩
              let z : (SemiSSet.boundary.{u} m).toFunctor.obj d := ⟨y, hybd⟩
              refine ⟨z, ?_, ?_⟩
              · have hcommd := congrArg (fun α => α.app d) hcomm
                have hcommz : incl.app d (b.app d z) = smap.app d y := by
                  simpa [z] using congrArg (fun f => f z) hcommd
                have hinj : Function.Injective (incl.app d) := by
                  rw [← mono_iff_injective]
                  infer_instance
                apply hinj
                calc
                  incl.app d (b.app d z) = smap.app d y := hcommz
                  _ = incl.app d x := hxy.symm
              · rfl
    haveI : Mono (incl.app d) := by infer_instance
    apply Types.isPushout_of_isPullback_of_mono' hpb
    · change Set.range (incl.app d) ∪ Set.range (smap.app d) = Set.univ
      ext x
      simp only [Set.mem_union, Set.mem_range, Set.mem_univ]
      constructor
      · intro _
        trivial
      · intro _
        by_cases hx' : x.1 ∈ S''.obj d
        · left
          exact ⟨⟨x.1, hx'⟩, rfl⟩
        · right
          have htop : ∃ hd : d = op (Henry.SemiSimplexCategory.mk m), hd ▸ x.1 = sigma := by
            by_contra hn
            apply hx'
            refine ⟨x.2, ?_⟩
            intro hd heq
            exact hn ⟨hd, heq⟩
          obtain ⟨hd, hσx⟩ := htop
          subst d
          refine ⟨idM, ?_⟩
          apply Subtype.ext
          calc
            (smap.app (op (Henry.SemiSimplexCategory.mk m)) idM).1 = sigma := hsid
            _ = x.1 := hσx.symm
    · intro x y _ _ hxy
      exact HomotopyHypothesis.Approximation.TopSimplex.simplexMapToSub_app_injective S sigma hσS' hxy
  refine ⟨m, S'', hS'le, hS''le, b, smap, hpush, hcount⟩

#print axioms HomotopyHypothesis.Simplicial.Faces.exists_topSimplex_pushout_rel_proof

end HomotopyHypothesis.Simplicial.Faces
