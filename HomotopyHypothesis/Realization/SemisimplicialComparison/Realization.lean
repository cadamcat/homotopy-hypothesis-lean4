import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Anodyne.AnodyneDeformationRetract
import HomotopyHypothesis.Realization.SemisimplicialComparison.CDeltaFacts
import HomotopyHypothesis.Realization.SemisimplicialComparison.CellAttach
import HomotopyHypothesis.Realization.SemisimplicialComparison.FreeKan
/-!
# The standard realization of `C^Δ`

Fix retractions `r : ‖Δ_{n+1}‖ ⟶ ‖Λ^{n+1}_k‖` of the realized horn inclusions. The singular
semi-simplicial set of a space `T` is an algebraic Kan complex `Sing T`: a horn `h` is filled by
`r` followed by the realization of `h` (H:2876–2880). For an object `X` of `C^Δ` the functor
`T ↦ Hom(X, Sing T)` is corepresented by a space `R X` (induction over the cells of `X`: free
objects on `S` are corepresented by `‖S‖`, and cell attachments are pushouts). This gives the
standard realization `R : C^Δ ⥤ TopCat` as a partial left adjoint of `Sing`.
-/

universe u

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra

namespace HomotopyHypothesis.Realization.SemisimplicialComparison

open HomotopyHypothesis.Henry

/-- The singular simplices of a space. -/
noncomputable abbrev Sing : TopCat.{u} ⥤ SemiSSet.{u} :=
  Presheaf.restrictedULiftYoneda.{u} SemiSSet.toTop.{u}

/-- The realization adjunction (left Kan extension along the Yoneda embedding). -/
noncomputable def realAdj : SemiSSet.realization.{u} ⊣ Sing.{u} :=
  Presheaf.uliftYonedaAdjunction.{u} (SemiSSet.stdSimplex.{u}.leftKanExtension SemiSSet.toTop.{u})
    (SemiSSet.stdSimplex.{u}.leftKanExtensionUnit SemiSSet.toTop.{u})

theorem exists_hornRetraction (p : HornIdx) :
    ∃ r : SemiSSet.realization.obj (simplexObj.{u} p) ⟶ SemiSSet.realization.obj (hornObj p),
      SemiSSet.realization.map (hornι p) ≫ r = 𝟙 _ := by
  have hA : SemiSSet.anodyne (hornι.{u} p) :=
    MorphismProperty.multiplicativeClosure.of _ (Or.inl (pushouts_mk _
      (IsPushout.of_horiz_isIso ⟨by simp⟩ : IsPushout (𝟙 _) (hornι p) (hornι p) (𝟙 _))
      (MorphismProperty.ofHoms.mk p)))
  obtain ⟨r, hr, -⟩ := Approximation.Anodyne.realization_anodyne_deformationRetract_proof _ hA
  exact ⟨r, hr⟩

/-- A chosen retraction of a realized horn inclusion. -/
noncomputable def hornRetraction (p : HornIdx) :
    SemiSSet.realization.obj (simplexObj.{u} p) ⟶ SemiSSet.realization.obj (hornObj p) :=
  (exists_hornRetraction p).choose

theorem hornRetraction_spec (p : HornIdx) :
    SemiSSet.realization.map (hornι p) ≫ hornRetraction.{u} p = 𝟙 _ :=
  (exists_hornRetraction p).choose_spec

/-- The singular algebraic Kan complex of a space. -/
noncomputable abbrev singAlgObj (T : TopCat.{u}) : AlgKan.{u} where
  X := Sing.obj T
  fill n k h := (realAdj.homEquiv _ _)
    (hornRetraction ⟨n, k⟩ ≫ (realAdj.homEquiv _ _).symm h)
  fill_spec n k h := by
    change hornι ⟨n, k⟩ ≫ _ = h
    rw [← realAdj.homEquiv_naturality_left, ← Category.assoc, hornRetraction_spec,
      Category.id_comp, Equiv.apply_symm_apply]

/-- The singular algebraic Kan complex functor. -/
noncomputable abbrev singAlg : TopCat.{u} ⥤ AlgKan.{u} where
  obj := singAlgObj
  map f := ⟨Sing.map f, fun n k h => by
    change (realAdj.homEquiv _ _) (hornRetraction ⟨n, k⟩ ≫ (realAdj.homEquiv _ _).symm h) ≫
        Sing.map f = (realAdj.homEquiv _ _)
          (hornRetraction ⟨n, k⟩ ≫ (realAdj.homEquiv _ _).symm (h ≫ Sing.map f))
    rw [← realAdj.homEquiv_naturality_right, realAdj.homEquiv_naturality_right_symm,
      Category.assoc]⟩
  map_id T := AlgKan.Hom.ext (Sing.map_id T)
  map_comp f g := AlgKan.Hom.ext (Sing.map_comp f g)

@[simp]
theorem singAlg_map_hom {T T' : TopCat.{u}} (f : T ⟶ T') : (singAlg.map f).hom = Sing.map f := rfl

@[simp]
theorem singAlg_obj_X (T : TopCat.{u}) : (singAlg.obj T).X = Sing.obj T := rfl

/-- `v : X ⟶ Sing T₀` is universal: it corepresents `T ↦ Hom(X, Sing T)`. -/
def IsUniv {X : AlgKan.{u}} {T₀ : TopCat.{u}} (v : X ⟶ singAlg.obj T₀) : Prop :=
  ∀ (T : TopCat.{u}) (g : X ⟶ singAlg.obj T), ∃! f : T₀ ⟶ T, v ≫ singAlg.map f = g

section Univ

variable {X : AlgKan.{u}} {T₀ T₀' : TopCat.{u}} {v : X ⟶ singAlg.obj T₀}
  {v' : X ⟶ singAlg.obj T₀'}

theorem IsUniv.hom_ext (hv : IsUniv v) {T : TopCat.{u}} {f f' : T₀ ⟶ T}
    (h : v ≫ singAlg.map f = v ≫ singAlg.map f') : f = f' :=
  (hv T _).unique rfl h.symm

/-- The comparison of two universal maps. -/
noncomputable def IsUniv.iso (hv : IsUniv v) (hv' : IsUniv v') : T₀ ≅ T₀' where
  hom := (hv _ v').exists.choose
  inv := (hv' _ v).exists.choose
  hom_inv_id := hv.hom_ext (by
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, (hv _ v').exists.choose_spec,
      (hv' _ v).exists.choose_spec, CategoryTheory.Functor.map_id, Category.comp_id])
  inv_hom_id := hv'.hom_ext (by
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, (hv' _ v).exists.choose_spec,
      (hv _ v').exists.choose_spec, CategoryTheory.Functor.map_id, Category.comp_id])

theorem IsUniv.iso_hom (hv : IsUniv v) (hv' : IsUniv v') :
    v ≫ singAlg.map (hv.iso hv').hom = v' :=
  (hv _ v').exists.choose_spec

/-- A universal map exhibits the left adjoint of `singAlg` as defined at `X`. -/
theorem IsUniv.leftAdjointObjIsDefined (hv : IsUniv v) : singAlg.leftAdjointObjIsDefined X :=
  Functor.CorepresentableBy.isCorepresentable
    { homEquiv := fun {T} => Equiv.ofBijective (fun f : T₀ ⟶ T => v ≫ singAlg.map f)
        ⟨fun f f' h => hv.hom_ext h, fun g => (hv T g).exists⟩
      homEquiv_comp := fun g f => by
        change v ≫ singAlg.map (f ≫ g) = (v ≫ singAlg.map f) ≫ singAlg.map g
        rw [CategoryTheory.Functor.map_comp, Category.assoc] }

end Univ

/-- Free objects: the lift of the unit of the realization adjunction is universal. -/
theorem exists_isUniv_free {S : SemiSSet.{u}} {Y : AlgKan.{u}} {η : S ⟶ Y.X} (h : Y.IsFreeOn η) :
    ∃ v : Y ⟶ singAlg.obj (SemiSSet.realization.obj S), η ≫ v.hom = realAdj.unit.app S ∧
      IsUniv v := by
  obtain ⟨v, hv, -⟩ := h (singAlg.obj (SemiSSet.realization.obj S)) (realAdj.unit.app S)
  refine ⟨v, hv, fun T g => ⟨(realAdj.homEquiv S T).symm (η ≫ g.hom), ?_, ?_⟩⟩
  · apply isFreeOn_hom_ext h
    change η ≫ v.hom ≫ Sing.map _ = _
    rw [← Category.assoc, hv, ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
  · intro f hf
    rw [Equiv.eq_symm_apply, Adjunction.homEquiv_unit, ← hv, ← hf]
    rfl

/-- Free objects on a simplex: the generating simplex is universal. -/
theorem exists_isUniv_simplex {n : ℕ} {Y : AlgKan.{u}}
    {η : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ Y.X} (h : Y.IsFreeOn η) :
    ∃ v : Y ⟶ singAlg.obj (SemiSSet.toTop.obj (Henry.SemiSimplexCategory.mk n)),
      η ≫ v.hom = uliftYonedaEquiv.symm (ULift.up (𝟙 _)) ∧ IsUniv v := by
  obtain ⟨v, hv, -⟩ := h (singAlg.obj (SemiSSet.toTop.obj (Henry.SemiSimplexCategory.mk n)))
    (uliftYonedaEquiv.symm (ULift.up (𝟙 _)))
  refine ⟨v, hv, fun T g => ⟨(uliftYonedaEquiv (η ≫ g.hom)).down, ?_, ?_⟩⟩
  · apply isFreeOn_hom_ext h
    change η ≫ v.hom ≫ Sing.map _ = _
    rw [← Category.assoc, hv]
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp]
    erw [Equiv.apply_symm_apply]
    change ULift.up (𝟙 (SemiSSet.toTop.obj (Henry.SemiSimplexCategory.mk n)) ≫ _) = _
    rw [Category.id_comp]
    rfl
  · intro f hf
    rw [← hf]
    change f = (uliftYonedaEquiv (η ≫ v.hom ≫ Sing.map f)).down
    rw [← Category.assoc, hv, uliftYonedaEquiv_comp]
    erw [Equiv.apply_symm_apply]
    change f = 𝟙 (SemiSSet.toTop.obj (Henry.SemiSimplexCategory.mk n)) ≫ f
    rw [Category.id_comp]

/-- An initial object is free on the empty semi-simplicial set. -/
theorem isFreeOn_of_isInitial {X : AlgKan.{u}} (hX : IsInitial X) : X.IsFreeOn (fromEmptyX X.X) :=
  fun Z _ => ⟨hX.to Z, emptyX_hom_ext _ _, fun _ _ => hX.hom_ext _ _⟩

/-- The left adjoint of `singAlg` is defined on every object of `C^Δ`. -/
theorem leftAdjointObjIsDefined_cdelta (X : CDelta.{u}) : singAlg.leftAdjointObjIsDefined X.obj := by
  obtain ⟨X, hX⟩ := X
  induction hX with
  | initial X hX =>
    obtain ⟨hX⟩ := hX
    exact (exists_isUniv_free (isFreeOn_of_isInitial hX)).choose_spec.2.leftAdjointObjIsDefined
  | @attach X Y j _ hj ih =>
    let d := AlgKan.IsCellAttachment.data hj
    obtain ⟨B, ηB, hB⟩ := exists_free_boundary.{u} d.n
    obtain ⟨D, ηD, hD⟩ := exists_free_simplex.{u} d.n
    obtain ⟨ι, hι, -⟩ := hB D.obj ((SemiSSet.boundary d.n).ι ≫ ηD)
    obtain ⟨abar, habar, -⟩ := hB X d.a
    obtain ⟨ybar, hybar, -⟩ := hD Y d.y
    have sq := d.isPushout hB hD hι habar hybar
    refine Functor.leftAdjointObjIsDefined_of_isColimit sq.isColimit ?_
    rintro (_ | _ | _)
    · exact (exists_isUniv_free hB).choose_spec.2.leftAdjointObjIsDefined
    · exact (exists_isUniv_free hD).choose_spec.2.leftAdjointObjIsDefined
    · exact ih

/-- An object of `C^Δ` as an object of the domain of the left adjoint of `singAlg`. -/
abbrev liftC (X : CDelta.{u}) : singAlg.PartialLeftAdjointSource :=
  ⟨X.obj, leftAdjointObjIsDefined_cdelta X⟩

/-- The standard realization `C^Δ ⥤ TopCat`. -/
noncomputable abbrev stdR : CDelta.{u} ⥤ TopCat.{u} where
  obj X := singAlg.partialLeftAdjointObj (liftC X)
  map {X Y} f := singAlg.partialLeftAdjointMap (X := liftC X) (Y := liftC Y)
    (ObjectProperty.homMk f.hom)
  map_id X := singAlg.partialLeftAdjoint.map_id (liftC X)
  map_comp {X Y Z} f g := singAlg.partialLeftAdjoint.map_comp (X := liftC X) (Y := liftC Y)
    (Z := liftC Z) (ObjectProperty.homMk f.hom) (ObjectProperty.homMk g.hom)

/-- The unit `X ⟶ Sing (R X)`. -/
noncomputable def uR (X : CDelta.{u}) : X.obj ⟶ singAlg.obj (stdR.obj X) :=
  singAlg.partialLeftAdjointHomEquiv (X := liftC X) (𝟙 (stdR.obj X))

theorem uR_comp (X : CDelta.{u}) {T : TopCat.{u}} (f : stdR.obj X ⟶ T) :
    uR X ≫ singAlg.map f = singAlg.partialLeftAdjointHomEquiv (X := liftC X) f := by
  rw [uR, ← Functor.partialLeftAdjointHomEquiv_comp, Category.id_comp]

theorem isUniv_uR (X : CDelta.{u}) : IsUniv (uR X) := by
  intro T g
  refine ⟨(singAlg.partialLeftAdjointHomEquiv (X := liftC X)).symm g, ?_, fun f hf => ?_⟩
  · dsimp only
    rw [uR_comp, Equiv.apply_symm_apply]
  · dsimp only at hf
    rw [← hf, uR_comp, Equiv.symm_apply_apply]

theorem uR_naturality {X Y : CDelta.{u}} (f : X ⟶ Y) :
    uR X ≫ singAlg.map (stdR.map f) = f.hom ≫ uR Y := by
  rw [uR_comp]
  exact singAlg.partialLeftAdjointHomEquiv_map
    (ObjectProperty.homMk f.hom : liftC X ⟶ liftC Y)

theorem uR_naturality_assoc {X Y : CDelta.{u}} (f : X ⟶ Y) {Z : AlgKan.{u}}
    (g : singAlg.obj (stdR.obj Y) ⟶ Z) :
    uR X ≫ singAlg.map (stdR.map f) ≫ g = f.hom ≫ uR Y ≫ g := by
  rw [← Category.assoc, uR_naturality, Category.assoc]

/-- The standard realization sends pushouts of algebraic Kan complexes to pushouts. -/
theorem stdR_isPushout {A B X P : CDelta.{u}} {i : A ⟶ B} {f : A ⟶ X} {k : B ⟶ P} {j : X ⟶ P}
    (h : IsPushout i.hom f.hom k.hom j.hom) :
    IsPushout (stdR.map i) (stdR.map f) (stdR.map k) (stdR.map j) := by
  have hw : i ≫ k = f ≫ j := ObjectProperty.hom_ext _ h.w
  refine isPushout_of_universal (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hw])
    fun T b x hbx => ?_
  have hc : i.hom ≫ uR B ≫ singAlg.map b = f.hom ≫ uR X ≫ singAlg.map x := by
    rw [← uR_naturality_assoc, ← uR_naturality_assoc, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hbx]
  obtain ⟨p, hp₁, hp₂⟩ := h.exists_desc _ _ hc
  obtain ⟨o, ho, -⟩ := isUniv_uR P T p
  refine ⟨o, ⟨(isUniv_uR B).hom_ext ?_, (isUniv_uR X).hom_ext ?_⟩, fun o' ⟨h₁, h₂⟩ => ?_⟩
  · rw [CategoryTheory.Functor.map_comp, uR_naturality_assoc, ho, hp₁]
  · rw [CategoryTheory.Functor.map_comp, uR_naturality_assoc, ho, hp₂]
  · apply (isUniv_uR P).hom_ext
    rw [ho]
    apply h.hom_ext
    · rw [← uR_naturality_assoc, ← CategoryTheory.Functor.map_comp, h₁, hp₁]
    · rw [← uR_naturality_assoc, ← CategoryTheory.Functor.map_comp, h₂, hp₂]

/-- The standard realization sends initial objects to initial objects. -/
noncomputable def stdR_isInitial {I : CDelta.{u}} (hI : IsInitial I) : IsInitial (stdR.obj I) :=
  let hI' := isInitial_obj_of_isInitial hI
  IsInitial.ofUniqueHom (fun T => (isUniv_uR I T (hI'.to _)).exists.choose)
    (fun T f => (isUniv_uR I).hom_ext (by
      rw [(isUniv_uR I T (hI'.to _)).exists.choose_spec]
      exact hI'.hom_ext _ _))

/-- The realization of an object free on `S` is `‖S‖`. -/
noncomputable def freeIso {S : SemiSSet.{u}} {X : CDelta.{u}} {η : S ⟶ X.obj.X}
    (h : X.obj.IsFreeOn η) : stdR.obj X ≅ SemiSSet.realization.obj S :=
  (isUniv_uR X).iso (exists_isUniv_free h).choose_spec.2

theorem uR_freeIso {S : SemiSSet.{u}} {X : CDelta.{u}} {η : S ⟶ X.obj.X}
    (h : X.obj.IsFreeOn η) :
    η ≫ (uR X ≫ singAlg.map (freeIso h).hom).hom = realAdj.unit.app S := by
  rw [freeIso, IsUniv.iso_hom]
  exact (exists_isUniv_free h).choose_spec.1

/-- Compatibility of `freeIso` with maps of generators. -/
theorem stdR_map_freeIso {S S' : SemiSSet.{u}} {X Y : CDelta.{u}} {η : S ⟶ X.obj.X}
    {η' : S' ⟶ Y.obj.X} (h : X.obj.IsFreeOn η) (h' : Y.obj.IsFreeOn η') (f : X ⟶ Y) (s : S ⟶ S')
    (hs : η ≫ f.hom.hom = s ≫ η') :
    stdR.map f ≫ (freeIso h').hom = (freeIso h).hom ≫ SemiSSet.realization.map s := by
  apply (isUniv_uR X).hom_ext
  rw [CategoryTheory.Functor.map_comp, uR_naturality_assoc, CategoryTheory.Functor.map_comp, ← Category.assoc]
  apply isFreeOn_hom_ext h
  have e₁ := uR_freeIso h'
  have e₂ := uR_freeIso h
  change η ≫ f.hom.hom ≫ (uR Y ≫ singAlg.map (freeIso h').hom).hom =
    η ≫ (uR X ≫ singAlg.map (freeIso h).hom).hom ≫ Sing.map (SemiSSet.realization.map s)
  rw [← Category.assoc, hs, Category.assoc, e₁, ← Category.assoc, e₂]
  exact realAdj.unit.naturality s

/-- The realization of an object free on `Δ_n` is the topological simplex. -/
noncomputable def simplexIso {n : ℕ} {X : CDelta.{u}}
    {η : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ X.obj.X}
    (h : X.obj.IsFreeOn η) : stdR.obj X ≅ SemiSSet.toTop.obj (Henry.SemiSimplexCategory.mk n) :=
  (isUniv_uR X).iso (exists_isUniv_simplex h).choose_spec.2

theorem uR_simplexIso {n : ℕ} {X : CDelta.{u}}
    {η : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ X.obj.X}
    (h : X.obj.IsFreeOn η) :
    η ≫ (uR X ≫ singAlg.map (simplexIso h).hom).hom = uliftYonedaEquiv.symm (ULift.up (𝟙 _)) := by
  rw [simplexIso, IsUniv.iso_hom]
  exact (exists_isUniv_simplex h).choose_spec.1

theorem stdR_map_simplexIso {m n : ℕ} {Y X : CDelta.{u}}
    {η' : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ Y.obj.X}
    {η : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ X.obj.X}
    (hY : Y.obj.IsFreeOn η') (hX : X.obj.IsFreeOn η)
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) (f : Y ⟶ X)
    (hf : η' ≫ f.hom.hom = SemiSSet.stdSimplex.map σ ≫ η) :
    stdR.map f ≫ (simplexIso hX).hom = (simplexIso hY).hom ≫ SemiSSet.toTop.map σ := by
  apply (isUniv_uR Y).hom_ext
  rw [CategoryTheory.Functor.map_comp, uR_naturality_assoc, CategoryTheory.Functor.map_comp, ← Category.assoc]
  apply isFreeOn_hom_ext hY
  have e₁ := uR_simplexIso hX
  have e₂ := uR_simplexIso hY
  change η' ≫ f.hom.hom ≫ (uR X ≫ singAlg.map (simplexIso hX).hom).hom =
    η' ≫ (uR Y ≫ singAlg.map (simplexIso hY).hom).hom ≫ Sing.map (SemiSSet.toTop.map σ)
  rw [← Category.assoc, hf, Category.assoc, e₁, ← Category.assoc, e₂]
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change ULift.up (SemiSSet.toTop.map σ ≫ 𝟙 _) = ULift.up (𝟙 _ ≫ SemiSSet.toTop.map σ)
  rw [Category.id_comp, Category.comp_id]

end HomotopyHypothesis.Realization.SemisimplicialComparison
