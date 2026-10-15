import HomotopyHypothesis.Blueprint.Bridge.GlobeToOAI
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Bridge.GlobularEquivalence.Transport
/-!
# Transport of tables and shapes

Along the isomorphism of globe categories, the representable disks correspond naturally in the
face maps, and the realizations of tables (iterated pushouts of disks) correspond by canonical
isomorphisms compatible with the last inclusions.
-/

noncomputable section

namespace HomotopyHypothesis.Bridge.Statement

open CategoryTheory CategoryTheory.Limits
open HomotopyHypothesis.Bridge.GlobularEquivalence

universe u

/-- The disk isomorphisms are natural in the maps of the statement's globe category. -/
theorem diskIso_map {m n : ℕ}
    (φ : HomotopyHypothesis.Grothendieck.Globe.mk m ⟶ HomotopyHypothesis.Grothendieck.Globe.mk n) :
    globularPresheafReindex.map
        (uliftYoneda.{u}.map (HomotopyHypothesis.Blueprint.globeToOAI.map φ)) ≫
      (diskIso.{u} n).hom = (diskIso.{u} m).hom ≫ uliftYoneda.{u}.map φ := by
  ext X z
  obtain ⟨z⟩ := z
  change globeEquiv.functor.obj X.unop ⟶
    globeEquiv.functor.obj (HomotopyHypothesis.Grothendieck.Globe.mk m) at z
  change ULift.up (globeEquiv.functor.preimage (z ≫ globeEquiv.functor.map φ)) =
    ULift.up (globeEquiv.functor.preimage z ≫ φ)
  rw [Functor.preimage_comp, Functor.preimage_map]

/-- The disk isomorphisms are natural in the faces. -/
theorem diskIso_face {m n : ℕ} (h : m < n) (b : Bool) :
    globularPresheafReindex.map (OAI.Grothendieck.GlobularPresheaf.face.{u} h b) ≫
      (diskIso.{u} n).hom =
      (diskIso.{u} m).hom ≫ HomotopyHypothesis.Grothendieck.GlobularPresheaf.face.{u} h b :=
  diskIso_map (HomotopyHypothesis.Grothendieck.Globe.face h b)

/-- OpenAI's tables as tables of the statement (constructor by constructor). -/
def tableOfOAI : ∀ {n : ℕ}, OAI.Grothendieck.Table n → HomotopyHypothesis.Grothendieck.Table n
  | _, .globe n => .globe n
  | _, .attach T b h hl hr => .attach (tableOfOAI T) b h hl hr

/-- Tables of the statement as OpenAI's tables. -/
def tableToOAI : ∀ {n : ℕ}, HomotopyHypothesis.Grothendieck.Table n → OAI.Grothendieck.Table n
  | _, .globe n => .globe n
  | _, .attach T b h hl hr => .attach (tableToOAI T) b h hl hr

theorem tableOfOAI_tableToOAI {n : ℕ} (T : HomotopyHypothesis.Grothendieck.Table n) :
    tableOfOAI (tableToOAI T) = T := by
  induction T with
  | globe => rfl
  | attach T b h hl hr ih =>
    exact congrArg (fun T => HomotopyHypothesis.Grothendieck.Table.attach T b h hl hr) ih

theorem tableToOAI_tableOfOAI {n : ℕ} (T : OAI.Grothendieck.Table n) :
    tableToOAI (tableOfOAI T) = T := by
  induction T with
  | globe => rfl
  | attach T b h hl hr ih =>
    exact congrArg (fun T => OAI.Grothendieck.Table.attach T b h hl hr) ih

/-- The realization of an OpenAI table, reindexed, is the realization of the corresponding table,
compatibly with the last inclusions. -/
def realizeData : ∀ {n : ℕ} (T : OAI.Grothendieck.Table n),
    { i : globularPresheafReindex.{0}.obj T.realize ≅ (tableOfOAI T).realize //
      globularPresheafReindex.{0}.map T.lastInclusion ≫ i.hom =
        (diskIso.{0} n).hom ≫ (tableOfOAI T).lastInclusion }
  | _, .globe n => ⟨diskIso.{0} n, by
      change globularPresheafReindex.{0}.map (𝟙 _) ≫ (diskIso.{0} n).hom =
        (diskIso.{0} n).hom ≫ 𝟙 _
      simp⟩
  | _, .attach T b h hl hr =>
    let prev := realizeData T
    let f := OAI.Grothendieck.GlobularPresheaf.face hl true ≫ T.lastInclusion
    let g := OAI.Grothendieck.GlobularPresheaf.face hr false
    let f' := HomotopyHypothesis.Grothendieck.GlobularPresheaf.face hl true ≫
      (tableOfOAI T).lastInclusion
    let g' := HomotopyHypothesis.Grothendieck.GlobularPresheaf.face hr false
    have hf : globularPresheafReindex.{0}.map f ≫ prev.1.hom = (diskIso.{0} b).hom ≫ f' := by
      simp only [f, f', Functor.map_comp, Category.assoc, prev.2]
      rw [← Category.assoc, diskIso_face, Category.assoc]
    have hg : globularPresheafReindex.{0}.map g ≫ (diskIso.{0} h).hom =
        (diskIso.{0} b).hom ≫ g' := diskIso_face hr false
    ⟨(PreservesPushout.iso globularPresheafReindex.{0} f g).symm ≪≫
        pushoutIsoOfIso (f := globularPresheafReindex.{0}.map f)
          (g := globularPresheafReindex.{0}.map g) (f' := f') (g' := g')
          (diskIso.{0} b) prev.1 (diskIso.{0} h) hf hg, by
      change globularPresheafReindex.{0}.map (pushout.inr f g) ≫
          (PreservesPushout.iso globularPresheafReindex.{0} f g).inv ≫ _ =
        (diskIso.{0} h).hom ≫ pushout.inr f' g'
      rw [← Category.assoc, PreservesPushout.inr_iso_inv]
      exact pushout.inr_desc _ _ _⟩

theorem realizeData_attach_inl {n : ℕ} (T : OAI.Grothendieck.Table n) (b h : ℕ) (hl : b < n)
    (hr : b < h) :
    globularPresheafReindex.{0}.map
        (pushout.inl (OAI.Grothendieck.GlobularPresheaf.face hl true ≫ T.lastInclusion)
          (OAI.Grothendieck.GlobularPresheaf.face hr false)) ≫
      (realizeData (.attach T b h hl hr)).1.hom =
      (realizeData T).1.hom ≫
        pushout.inl (HomotopyHypothesis.Grothendieck.GlobularPresheaf.face hl true ≫
            (tableOfOAI T).lastInclusion)
          (HomotopyHypothesis.Grothendieck.GlobularPresheaf.face hr false) := by
  change _ ≫ (PreservesPushout.iso globularPresheafReindex.{0} _ _).inv ≫ _ = _
  rw [← Category.assoc, PreservesPushout.inl_iso_inv]
  exact pushout.inl_desc _ _ _

/-- OpenAI's shapes as shapes of the statement. -/
def shapeOfOAI (S : OAI.Grothendieck.Shape) : HomotopyHypothesis.Grothendieck.Shape :=
  ⟨S.1, tableOfOAI S.2⟩

/-- The realization of an OpenAI shape, reindexed, is the realization of the corresponding shape. -/
def shapeIso (S : OAI.Grothendieck.Shape) :
    globularPresheafReindex.{0}.obj S.realize ≅ (shapeOfOAI S).realize :=
  (realizeData S.2).1

/-- OpenAI's shape category to the statement's: reindexing conjugated by the realization
isomorphisms. -/
def shapeFunctor : OAI.Grothendieck.Shape ⥤ HomotopyHypothesis.Grothendieck.Shape where
  obj := shapeOfOAI
  map {S T} g := show (shapeOfOAI S).realize ⟶ (shapeOfOAI T).realize from
    (shapeIso S).inv ≫ globularPresheafReindex.{0}.map (show S.realize ⟶ T.realize from g) ≫
      (shapeIso T).hom
  map_id S := by
    change (shapeIso S).inv ≫ globularPresheafReindex.{0}.map (𝟙 _) ≫ (shapeIso S).hom = 𝟙 _
    simp
  map_comp {R S T} f g := by
    change (shapeIso R).inv ≫ globularPresheafReindex.{0}.map
        ((show R.realize ⟶ S.realize from f) ≫ (show S.realize ⟶ T.realize from g)) ≫
        (shapeIso T).hom =
      ((shapeIso R).inv ≫ globularPresheafReindex.{0}.map f ≫ (shapeIso S).hom) ≫
        ((shapeIso S).inv ≫ globularPresheafReindex.{0}.map g ≫ (shapeIso T).hom)
    simp

theorem shapeFunctor_map (S T : OAI.Grothendieck.Shape) (g : S ⟶ T) :
    (show (shapeOfOAI S).realize ⟶ (shapeOfOAI T).realize from shapeFunctor.map g) =
      (shapeIso S).inv ≫ globularPresheafReindex.{0}.map (show S.realize ⟶ T.realize from g) ≫
        (shapeIso T).hom := rfl

/-- The shape functor is fully faithful. -/
def shapeFunctorFullyFaithful : shapeFunctor.FullyFaithful where
  preimage {S T} f := show S.realize ⟶ T.realize from
    globularPresheafEquiv.{0}.fullyFaithfulFunctor.preimage
      ((shapeIso S).hom ≫ (show (shapeOfOAI S).realize ⟶ (shapeOfOAI T).realize from f) ≫
        (shapeIso T).inv)
  map_preimage {S T} f := by
    change (shapeOfOAI S).realize ⟶ (shapeOfOAI T).realize at f
    change (shapeIso S).inv ≫ globularPresheafReindex.{0}.map
        (globularPresheafEquiv.{0}.fullyFaithfulFunctor.preimage _) ≫ (shapeIso T).hom = f
    rw [Functor.FullyFaithful.map_preimage]
    simp
  preimage_map {S T} g := by
    apply globularPresheafEquiv.{0}.fullyFaithfulFunctor.map_injective
    change globularPresheafEquiv.{0}.functor.map
        (globularPresheafEquiv.{0}.fullyFaithfulFunctor.preimage _) = _
    rw [Functor.FullyFaithful.map_preimage]
    change (shapeIso S).hom ≫ ((shapeIso S).inv ≫ globularPresheafReindex.{0}.map _ ≫
      (shapeIso T).hom) ≫ (shapeIso T).inv = _
    simp

theorem shapeFunctor_face {m n : ℕ} (h : m < n) (b : Bool) :
    shapeFunctor.map (OAI.Grothendieck.Shape.face h b) =
      HomotopyHypothesis.Grothendieck.Shape.face h b := by
  change (diskIso.{0} m).inv ≫
      globularPresheafReindex.{0}.map (OAI.Grothendieck.GlobularPresheaf.face h b) ≫
      (diskIso.{0} n).hom = HomotopyHypothesis.Grothendieck.GlobularPresheaf.face h b
  rw [diskIso_face, Iso.inv_hom_id_assoc]

theorem shapeFunctor_seam (S : OAI.Grothendieck.Shape) {b : ℕ} (hl : b < S.1) :
    shapeFunctor.map (S.seam hl) = (shapeOfOAI S).seam hl := by
  change (diskIso.{0} b).inv ≫ globularPresheafReindex.{0}.map
      (OAI.Grothendieck.GlobularPresheaf.face hl true ≫ S.2.lastInclusion) ≫
      (realizeData S.2).1.hom =
    HomotopyHypothesis.Grothendieck.GlobularPresheaf.face hl true ≫
      (tableOfOAI S.2).lastInclusion
  rw [Functor.map_comp, Category.assoc, (realizeData S.2).2, ← Category.assoc
    (globularPresheafReindex.{0}.map _), diskIso_face]
  simp

theorem shapeFunctor_inl (S : OAI.Grothendieck.Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    shapeFunctor.map (S.inl b h hl hr) = (shapeOfOAI S).inl b h hl hr := by
  change (realizeData S.2).1.inv ≫ globularPresheafReindex.{0}.map
      (pushout.inl (OAI.Grothendieck.GlobularPresheaf.face hl true ≫ S.2.lastInclusion)
        (OAI.Grothendieck.GlobularPresheaf.face hr false)) ≫
      (realizeData (.attach S.2 b h hl hr)).1.hom = _
  rw [realizeData_attach_inl]
  exact Iso.inv_hom_id_assoc _ _

theorem shapeFunctor_inr (S : OAI.Grothendieck.Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    shapeFunctor.map (S.inr b h hl hr) = (shapeOfOAI S).inr b h hl hr := by
  change (diskIso.{0} h).inv ≫ globularPresheafReindex.{0}.map
      (OAI.Grothendieck.Table.lastInclusion (.attach S.2 b h hl hr)) ≫
      (realizeData (.attach S.2 b h hl hr)).1.hom = _
  rw [(realizeData (.attach S.2 b h hl hr)).2, Iso.inv_hom_id_assoc]
  rfl

end HomotopyHypothesis.Bridge.Statement
