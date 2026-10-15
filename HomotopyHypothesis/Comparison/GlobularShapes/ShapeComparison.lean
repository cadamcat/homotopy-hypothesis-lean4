import OAI.CategoryTheory.Globular.CutoffExistence
import OAI.CategoryTheory.Globular.LinearShape
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.ShapeComparisonStatement
universe u v u₁

open CategoryTheory Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck HomotopyHypothesis.Henry
open HomotopyHypothesis.FiniteCategory.Lifting

namespace HomotopyHypothesis.Comparison.GlobularShapes

private structure PushoutComparison {C : Type u} [Category.{v} C]
    {Z₁ X₁ Y₁ P₁ Z₂ X₂ Y₂ P₂ : C}
    {f₁ : Z₁ ⟶ X₁} {g₁ : Z₁ ⟶ Y₁} {i₁ : X₁ ⟶ P₁} {j₁ : Y₁ ⟶ P₁}
    {f₂ : Z₂ ⟶ X₂} {g₂ : Z₂ ⟶ Y₂} {i₂ : X₂ ⟶ P₂} {j₂ : Y₂ ⟶ P₂}
    (eZ : Z₁ ≅ Z₂) (eX : X₁ ≅ X₂) (eY : Y₁ ≅ Y₂) where
  iso : P₁ ≅ P₂
  inl_hom : i₁ ≫ iso.hom = eX.hom ≫ i₂
  inr_hom : j₁ ≫ iso.hom = eY.hom ≫ j₂

private noncomputable def pushoutComparison
    {C : Type u} [Category.{v} C]
    {Z₁ X₁ Y₁ P₁ Z₂ X₂ Y₂ P₂ : C}
    {f₁ : Z₁ ⟶ X₁} {g₁ : Z₁ ⟶ Y₁} {i₁ : X₁ ⟶ P₁} {j₁ : Y₁ ⟶ P₁}
    {f₂ : Z₂ ⟶ X₂} {g₂ : Z₂ ⟶ Y₂} {i₂ : X₂ ⟶ P₂} {j₂ : Y₂ ⟶ P₂}
    (sq₁ : IsPushout f₁ g₁ i₁ j₁) (sq₂ : IsPushout f₂ g₂ i₂ j₂)
    (eZ : Z₁ ≅ Z₂) (eX : X₁ ≅ X₂) (eY : Y₁ ≅ Y₂)
    (hf : f₁ ≫ eX.hom = eZ.hom ≫ f₂)
    (hg : g₁ ≫ eY.hom = eZ.hom ≫ g₂) :
    PushoutComparison (f₁ := f₁) (g₁ := g₁) (i₁ := i₁) (j₁ := j₁)
      (f₂ := f₂) (g₂ := g₂) (i₂ := i₂) (j₂ := j₂) eZ eX eY := by
  have hfi : f₂ ≫ eX.inv = eZ.inv ≫ f₁ := by
    calc
      f₂ ≫ eX.inv = eZ.inv ≫ (eZ.hom ≫ f₂) ≫ eX.inv := by simp [Category.assoc]
      _ = eZ.inv ≫ (f₁ ≫ eX.hom) ≫ eX.inv := by rw [← hf]
      _ = eZ.inv ≫ f₁ := by simp [Category.assoc]
  have hgi : g₂ ≫ eY.inv = eZ.inv ≫ g₁ := by
    calc
      g₂ ≫ eY.inv = eZ.inv ≫ (eZ.hom ≫ g₂) ≫ eY.inv := by simp [Category.assoc]
      _ = eZ.inv ≫ (g₁ ≫ eY.hom) ≫ eY.inv := by rw [← hg]
      _ = eZ.inv ≫ g₁ := by simp [Category.assoc]
  let inl' := eX.hom ≫ i₂
  let inr' := eY.hom ≫ j₂
  have hsq₂ : IsPushout f₁ g₁ inl' inr' :=
    sq₂.of_iso eZ.symm eX.symm eY.symm (Iso.refl P₂) hfi hgi
      (by simp [inl', Category.assoc]) (by simp [inr', Category.assoc])
  let iso := sq₁.isoIsPushout X₁ Y₁ hsq₂
  exact ⟨iso, IsPushout.inl_isoIsPushout_hom X₁ Y₁ sq₁ hsq₂,
    IsPushout.inr_isoIsPushout_hom X₁ Y₁ sq₁ hsq₂⟩

private structure ComparisonData {Y : Type u₁} [Category.{v} Y]
    (F G : Shape ⥤ Y) (e : ∀ n, F.obj (Shape.globe n) ≅ G.obj (Shape.globe n))
    (T : Shape) where
  iso : F.obj T ≅ G.obj T
  cell_naturality : ∀ {n} (f : Shape.globe n ⟶ T),
    F.map f ≫ iso.hom = (e n).hom ≫ G.map f

private theorem globe_face_naturality
    {X : Type u} [Category.{v} X] {Y : Type u₁} [Category.{v} Y]
    (R : ShapeInterpretation X) (S : ShapeInterpretation Y) (p : X ⥤ Y)
    (e : ∀ n, (R.functor ⋙ p).obj (Shape.globe n) ≅ S.functor.obj (Shape.globe n))
    (hs : ∀ n, p.map (R.functor.map (Shape.source n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.source n))
    (ht : ∀ n, p.map (R.functor.map (Shape.target n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.target n))
    {m n : ℕ} (h : m < n) (side : Bool) :
    (R.functor ⋙ p).map (Shape.face h side) ≫ (e n).hom =
      (e m).hom ≫ S.functor.map (Shape.face h side) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hm : m = n
    · subst m
      cases side
      · simpa only [Functor.comp_map, Shape.source] using hs n
      · simpa only [Functor.comp_map, Shape.target] using ht n
    · have hm' : m < n := by omega
      have hcomp : Shape.face h side = Shape.face hm' side ≫ Shape.source n := by
        simpa only [Shape.source] using
          (Shape.face_comp hm' (Nat.lt_succ_self n) side false).symm
      have hsrc : (R.functor ⋙ p).map (Shape.source n) ≫ (e (n + 1)).hom =
          (e n).hom ≫ S.functor.map (Shape.source n) := by
        simpa only [Functor.comp_map, Shape.source] using hs n
      calc
        (R.functor ⋙ p).map (Shape.face h side) ≫ (e (n + 1)).hom =
            (R.functor ⋙ p).map (Shape.face hm' side ≫ Shape.source n) ≫
              (e (n + 1)).hom := by rw [hcomp]
        _ = ((R.functor ⋙ p).map (Shape.face hm' side) ≫
            (R.functor ⋙ p).map (Shape.source n)) ≫ (e (n + 1)).hom := by
              rw [Functor.map_comp]
        _ = (R.functor ⋙ p).map (Shape.face hm' side) ≫
            ((R.functor ⋙ p).map (Shape.source n) ≫ (e (n + 1)).hom) := by
              simp [Category.assoc]
        _ = (R.functor ⋙ p).map (Shape.face hm' side) ≫
            ((e n).hom ≫ S.functor.map (Shape.source n)) := by
              rw [hsrc]
        _ = ((R.functor ⋙ p).map (Shape.face hm' side) ≫ (e n).hom) ≫
            S.functor.map (Shape.source n) := by simp [Category.assoc]
        _ = ((e m).hom ≫ S.functor.map (Shape.face hm' side)) ≫
            S.functor.map (Shape.source n) := by rw [ih hm']
        _ = (e m).hom ≫
            (S.functor.map (Shape.face hm' side) ≫ S.functor.map (Shape.source n)) := by
              simp [Category.assoc]
        _ = (e m).hom ≫ S.functor.map
            (Shape.face hm' side ≫ Shape.source n) := by rw [← Functor.map_comp]
        _ = (e m).hom ≫ S.functor.map (Shape.face h side) := by rw [← hcomp]

private theorem globe_map_naturality
    {X : Type u} [Category.{v} X] {Y : Type u₁} [Category.{v} Y]
    (R : ShapeInterpretation X) (S : ShapeInterpretation Y) (p : X ⥤ Y)
    (e : ∀ n, (R.functor ⋙ p).obj (Shape.globe n) ≅ S.functor.obj (Shape.globe n))
    (hs : ∀ n, p.map (R.functor.map (Shape.source n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.source n))
    (ht : ∀ n, p.map (R.functor.map (Shape.target n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.target n))
    {m n : ℕ} (f : Shape.globe m ⟶ Shape.globe n) :
    (R.functor ⋙ p).map f ≫ (e n).hom = (e m).hom ≫ S.functor.map f := by
  cases hfa : (uliftYonedaEquiv f).down with
  | id =>
    have he : uliftYonedaEquiv f = ULift.up (𝟙 (Globe.mk m)) := by
      apply ULift.ext
      exact hfa
    have hiden : uliftYonedaEquiv (𝟙 (Shape.globe m)) = ULift.up (𝟙 (Globe.mk m)) := rfl
    have hf : f = 𝟙 (Shape.globe m) := by
      exact uliftYonedaEquiv.injective (he.trans hiden.symm)
    rw [hf]
    simp
  | face h side =>
    have he : uliftYonedaEquiv f = ULift.up (Globe.face h side) := by
      apply ULift.ext
      exact hfa
    have hface : uliftYonedaEquiv (Shape.face h side) = ULift.up (Globe.face h side) := rfl
    have hf : f = Shape.face h side := by
      exact uliftYonedaEquiv.injective (he.trans hface.symm)
    rw [hf]
    exact globe_face_naturality R S p e hs ht h side

private theorem globeMap_factors_attach (T : Shape) (b h : ℕ)
    (hl : b < T.1) (hr : b < h) {k : ℕ}
    (f : Shape.globe k ⟶ Shape.attach T b h hl hr) :
    (∃ g : Shape.globe k ⟶ T, f = g ≫ Shape.inl T b h hl hr) ∨
      (∃ g : Shape.globe k ⟶ Shape.globe h,
        f = g ≫ Shape.inr T b h hl hr) := by
  let D := span (Shape.realization.map (T.seam hl))
    (Shape.realization.map (Shape.face hr false))
  let sq := Shape.realization_pushout T b h hl hr
  let x : (Shape.attach T b h hl hr).realize.obj (op (Globe.mk k)) := uliftYonedaEquiv f
  obtain ⟨j, y, hy⟩ := FunctorToTypes.jointly_surjective D (op (Globe.mk k))
    sq.isColimit x
  cases j with
  | none =>
    left
    let y' := (Shape.realization.map (T.seam hl)).app (op (Globe.mk k)) y
    refine ⟨Shape.cellArrow T (op (Globe.mk k)) y', ?_⟩
    have hzero : (sq.cocone.ι.app WalkingSpan.zero).app (op (Globe.mk k)) y =
        ((D.map WalkingSpan.Hom.fst ≫ sq.cocone.ι.app WalkingSpan.left).app
          (op (Globe.mk k))) y := by
      have h : sq.cocone.ι.app WalkingSpan.zero =
          D.map WalkingSpan.Hom.fst ≫ sq.cocone.ι.app WalkingSpan.left :=
        (sq.cocone.ι.naturality WalkingSpan.Hom.fst).symm
      exact congrArg (fun q => q.app (op (Globe.mk k)) y) h
    have hzero' : (sq.cocone.ι.app WalkingSpan.zero).app (op (Globe.mk k)) y =
        (sq.cocone.ι.app WalkingSpan.left).app (op (Globe.mk k)) y' := by
      simpa only [D, span_map_fst, NatTrans.comp_app, types_comp_apply, y'] using hzero
    have hx : x = (Shape.inl T b h hl hr).app (op (Globe.mk k)) y' := by
      rw [hy, hzero']
      rfl
    calc
      f = (Shape.attach T b h hl hr).cellArrow (op (Globe.mk k)) x :=
        (Equiv.symm_apply_apply uliftYonedaEquiv f).symm
      _ = (T.attach b h hl hr).cellArrow (op (Globe.mk k))
          ((Shape.inl T b h hl hr).app (op (Globe.mk k)) y') := by rw [hx]
      _ = T.cellArrow (op (Globe.mk k)) y' ≫ Shape.inl T b h hl hr :=
        Shape.cellArrow_naturality (Shape.inl T b h hl hr) (op (Globe.mk k)) y'
  | some j =>
    cases j with
    | left =>
      left
      refine ⟨Shape.cellArrow T (op (Globe.mk k)) y, ?_⟩
      have hx : x = (Shape.inl T b h hl hr).app (op (Globe.mk k)) y := by
        change x = (sq.cocone.ι.app WalkingSpan.left).app (op (Globe.mk k)) y
        exact hy
      calc
        f = (Shape.attach T b h hl hr).cellArrow (op (Globe.mk k)) x :=
          (Equiv.symm_apply_apply uliftYonedaEquiv f).symm
        _ = (T.attach b h hl hr).cellArrow (op (Globe.mk k))
            ((Shape.inl T b h hl hr).app (op (Globe.mk k)) y) := by rw [hx]
        _ = T.cellArrow (op (Globe.mk k)) y ≫ Shape.inl T b h hl hr :=
          Shape.cellArrow_naturality (Shape.inl T b h hl hr) (op (Globe.mk k)) y
    | right =>
      right
      refine ⟨Shape.cellArrow (Shape.globe h) (op (Globe.mk k)) y, ?_⟩
      have hx : x = (Shape.inr T b h hl hr).app (op (Globe.mk k)) y := by
        change x = (sq.cocone.ι.app WalkingSpan.right).app (op (Globe.mk k)) y
        exact hy
      calc
        f = (Shape.attach T b h hl hr).cellArrow (op (Globe.mk k)) x :=
          (Equiv.symm_apply_apply uliftYonedaEquiv f).symm
        _ = (T.attach b h hl hr).cellArrow (op (Globe.mk k))
            ((Shape.inr T b h hl hr).app (op (Globe.mk k)) y) := by rw [hx]
        _ = (Shape.globe h).cellArrow (op (Globe.mk k)) y ≫ Shape.inr T b h hl hr :=
          Shape.cellArrow_naturality (Shape.inr T b h hl hr) (op (Globe.mk k)) y

private theorem mappedShapePushout
    {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    {Y : Type u₁} [Category.{v} Y] [CategoryWithCofibrations Y]
    (R : ShapeInterpretation X) (p : X ⥤ Y) (hp : IsCofibrationMorphism p)
    (hR : ∀ (T : Shape) (b : ℕ) (hb : b < T.1),
      cofibrations X (R.functor.map (T.seam hb)))
    (T : Shape) (b h : ℕ) (hl : b < T.1) (hr : b < h) :
    IsPushout ((R.functor ⋙ p).map (T.seam hl))
      ((R.functor ⋙ p).map (Shape.face hr false))
      ((R.functor ⋙ p).map (Shape.inl T b h hl hr))
      ((R.functor ⋙ p).map (Shape.inr T b h hl hr)) := by
  exact hp.map_isPushout _ _ _ _ (R.sums T b h hl hr) (hR T b hl)

private noncomputable def attachmentComparison
    {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    {Y : Type u₁} [Category.{v} Y] [CategoryWithCofibrations Y]
    (R : ShapeInterpretation X) (S : ShapeInterpretation Y) (p : X ⥤ Y)
    (hp : IsCofibrationMorphism p)
    (hR : ∀ (T : Shape) (b : ℕ) (hb : b < T.1),
      cofibrations X (R.functor.map (T.seam hb)))
    (e : ∀ n, (R.functor ⋙ p).obj (Shape.globe n) ≅ S.functor.obj (Shape.globe n))
    (hs : ∀ n, p.map (R.functor.map (Shape.source n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.source n))
    (ht : ∀ n, p.map (R.functor.map (Shape.target n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.target n))
    (T : Shape) (b h : ℕ) (hl : b < T.1) (hr : b < h)
    (prev : ComparisonData (R.functor ⋙ p) S.functor e T) :=
  pushoutComparison (mappedShapePushout R p hp hR T b h hl hr)
    (S.sums T b h hl hr) (e b) prev.iso (e h)
    (prev.cell_naturality (T.seam hl))
    (globe_map_naturality R S p e hs ht (Shape.face hr false))

private noncomputable def tableComparisonData
    {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    {Y : Type u₁} [Category.{v} Y] [CategoryWithCofibrations Y]
    (R : ShapeInterpretation X) (S : ShapeInterpretation Y) (p : X ⥤ Y)
    (hp : IsCofibrationMorphism p)
    (hR : ∀ (T : Shape) (b : ℕ) (hb : b < T.1),
      cofibrations X (R.functor.map (T.seam hb)))
    (e : ∀ n, (R.functor ⋙ p).obj (Shape.globe n) ≅ S.functor.obj (Shape.globe n))
    (hs : ∀ n, p.map (R.functor.map (Shape.source n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.source n))
    (ht : ∀ n, p.map (R.functor.map (Shape.target n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.target n)) :
    ∀ {n : ℕ} (T : Table n),
      ComparisonData (R.functor ⋙ p) S.functor e ⟨n, T⟩
  | _, .globe n =>
      { iso := e n
        cell_naturality := by
          intro k f
          exact globe_map_naturality R S p e hs ht f }
  | _, @Table.attach last T b h hl hr => by
      let prev := tableComparisonData R S p hp hR e hs ht T
      let old : Shape := ⟨last, T⟩
      let c := attachmentComparison R S p hp hR e hs ht old b h hl hr prev
      exact
        { iso := c.iso
          cell_naturality := by
            intro k f
            rcases globeMap_factors_attach old b h hl hr f with ⟨g, rfl⟩ | ⟨g, rfl⟩
            · calc
                (R.functor ⋙ p).map (g ≫ Shape.inl old b h hl hr) ≫ c.iso.hom =
                    (R.functor ⋙ p).map g ≫
                      ((R.functor ⋙ p).map (Shape.inl old b h hl hr) ≫ c.iso.hom) := by
                        simp [Category.assoc]
                _ = (R.functor ⋙ p).map g ≫ (prev.iso.hom ≫ S.functor.map
                    (Shape.inl old b h hl hr)) := by rw [c.inl_hom]
                _ = ((R.functor ⋙ p).map g ≫ prev.iso.hom) ≫
                    S.functor.map (Shape.inl old b h hl hr) := by simp [Category.assoc]
                _ = ((e k).hom ≫ S.functor.map g) ≫
                    S.functor.map (Shape.inl old b h hl hr) := by
                      rw [prev.cell_naturality]
                _ = (e k).hom ≫ S.functor.map
                    (g ≫ Shape.inl old b h hl hr) := by
                      calc
                        ((e k).hom ≫ S.functor.map g) ≫
                            S.functor.map (Shape.inl old b h hl hr) =
                          (e k).hom ≫ (S.functor.map g ≫
                            S.functor.map (Shape.inl old b h hl hr)) :=
                              Category.assoc _ _ _
                        _ = (e k).hom ≫ S.functor.map
                            (g ≫ Shape.inl old b h hl hr) := by
                              rw [← S.functor.map_comp]
            · calc
                (R.functor ⋙ p).map (g ≫ Shape.inr old b h hl hr) ≫ c.iso.hom =
                    (R.functor ⋙ p).map g ≫
                      ((R.functor ⋙ p).map (Shape.inr old b h hl hr) ≫ c.iso.hom) := by
                        simp [Category.assoc]
                _ = (R.functor ⋙ p).map g ≫ ((e h).hom ≫ S.functor.map
                    (Shape.inr old b h hl hr)) := by rw [c.inr_hom]
                _ = ((R.functor ⋙ p).map g ≫ (e h).hom) ≫
                    S.functor.map (Shape.inr old b h hl hr) := by simp [Category.assoc]
                _ = ((e k).hom ≫ S.functor.map g) ≫
                    S.functor.map (Shape.inr old b h hl hr) := by
                      rw [globe_map_naturality R S p e hs ht g]
                _ = (e k).hom ≫ S.functor.map
                    (g ≫ Shape.inr old b h hl hr) := by
                      calc
                        ((e k).hom ≫ S.functor.map g) ≫
                            S.functor.map (Shape.inr old b h hl hr) =
                          (e k).hom ≫ (S.functor.map g ≫
                            S.functor.map (Shape.inr old b h hl hr)) :=
                              Category.assoc _ _ _
                        _ = (e k).hom ≫ S.functor.map
                            (g ≫ Shape.inr old b h hl hr) := by
                              rw [← S.functor.map_comp] }

private theorem tableNaturality
    {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    {Y : Type u₁} [Category.{v} Y] [CategoryWithCofibrations Y]
    (R : ShapeInterpretation X) (S : ShapeInterpretation Y) (p : X ⥤ Y)
    (hp : IsCofibrationMorphism p)
    (hR : ∀ (T : Shape) (b : ℕ) (hb : b < T.1),
      cofibrations X (R.functor.map (T.seam hb)))
    (e : ∀ n, (R.functor ⋙ p).obj (Shape.globe n) ≅ S.functor.obj (Shape.globe n))
    (hs : ∀ n, p.map (R.functor.map (Shape.source n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.source n))
    (ht : ∀ n, p.map (R.functor.map (Shape.target n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.target n)) :
    ∀ {n : ℕ} (T : Table n) {U : Shape}
      (f : (⟨n, T⟩ : Shape) ⟶ U),
      (R.functor ⋙ p).map f ≫
          (tableComparisonData R S p hp hR e hs ht U.2).iso.hom =
        (tableComparisonData R S p hp hR e hs ht T).iso.hom ≫ S.functor.map f := by
  intro n T
  induction T with
  | globe n =>
      intro U f
      let dest := tableComparisonData R S p hp hR e hs ht U.2
      have hsphere :
          (tableComparisonData R S p hp hR e hs ht (Table.globe n)).iso = e n := rfl
      rw [hsphere]
      exact dest.cell_naturality f
  | @attach last T b h hl hr ih =>
      intro U f
      let old : Shape := ⟨last, T⟩
      let joined := Shape.attach old b h hl hr
      change (Shape.attach old b h hl hr) ⟶ U at f
      let prev := tableComparisonData R S p hp hR e hs ht T
      let dest := tableComparisonData R S p hp hR e hs ht U.2
      let c := attachmentComparison R S p hp hR e hs ht old b h hl hr prev
      have hcurr :
          (tableComparisonData R S p hp hR e hs ht (Table.attach T b h hl hr)).iso = c.iso := rfl
      have sq := mappedShapePushout R p hp hR old b h hl hr
      apply sq.hom_ext
      · calc
          (R.functor ⋙ p).map (Shape.inl old b h hl hr) ≫
              ((R.functor ⋙ p).map f ≫ dest.iso.hom) =
            ((R.functor ⋙ p).map (Shape.inl old b h hl hr ≫ f)) ≫ dest.iso.hom := by
              calc
                (R.functor ⋙ p).map (Shape.inl old b h hl hr) ≫
                    ((R.functor ⋙ p).map f ≫ dest.iso.hom) =
                  ((R.functor ⋙ p).map (Shape.inl old b h hl hr) ≫
                    (R.functor ⋙ p).map f) ≫ dest.iso.hom := (Category.assoc _ _ _).symm
                _ = (R.functor ⋙ p).map (Shape.inl old b h hl hr ≫ f) ≫ dest.iso.hom :=
                  congrArg (fun q => q ≫ dest.iso.hom)
                    ((R.functor ⋙ p).map_comp (Shape.inl old b h hl hr) f).symm
          _ = prev.iso.hom ≫ S.functor.map (Shape.inl old b h hl hr ≫ f) := by
            exact ih (U := U) (Shape.inl old b h hl hr ≫ f)
          _ = ((R.functor ⋙ p).map (Shape.inl old b h hl hr) ≫ c.iso.hom) ≫
              S.functor.map f := by
              calc
                prev.iso.hom ≫ S.functor.map (Shape.inl old b h hl hr ≫ f) =
                    prev.iso.hom ≫ (S.functor.map (Shape.inl old b h hl hr) ≫
                      S.functor.map f) := by
                        exact congrArg (fun q => prev.iso.hom ≫ q)
                          (S.functor.map_comp (Shape.inl old b h hl hr) f)
                _ = (prev.iso.hom ≫ S.functor.map (Shape.inl old b h hl hr)) ≫
                    S.functor.map f := (Category.assoc _ _ _).symm
                _ = ((R.functor ⋙ p).map (Shape.inl old b h hl hr) ≫ c.iso.hom) ≫
                    S.functor.map f := by rw [← c.inl_hom]
          _ = ((R.functor ⋙ p).map (Shape.inl old b h hl hr) ≫
              (tableComparisonData R S p hp hR e hs ht
                (Table.attach T b h hl hr)).iso.hom) ≫ S.functor.map f := by
                exact congrArg (fun α =>
                  ((R.functor ⋙ p).map (Shape.inl old b h hl hr) ≫ α.hom) ≫
                    S.functor.map f) hcurr.symm
          _ = (R.functor ⋙ p).map (Shape.inl old b h hl hr) ≫
              ((tableComparisonData R S p hp hR e hs ht
                (Table.attach T b h hl hr)).iso.hom ≫ S.functor.map f) :=
                Category.assoc _ _ _
      · calc
          (R.functor ⋙ p).map (Shape.inr old b h hl hr) ≫
              ((R.functor ⋙ p).map f ≫ dest.iso.hom) =
            ((R.functor ⋙ p).map (Shape.inr old b h hl hr ≫ f)) ≫ dest.iso.hom := by
              calc
                (R.functor ⋙ p).map (Shape.inr old b h hl hr) ≫
                    ((R.functor ⋙ p).map f ≫ dest.iso.hom) =
                  ((R.functor ⋙ p).map (Shape.inr old b h hl hr) ≫
                    (R.functor ⋙ p).map f) ≫ dest.iso.hom := (Category.assoc _ _ _).symm
                _ = (R.functor ⋙ p).map (Shape.inr old b h hl hr ≫ f) ≫ dest.iso.hom :=
                  congrArg (fun q => q ≫ dest.iso.hom)
                    ((R.functor ⋙ p).map_comp (Shape.inr old b h hl hr) f).symm
          _ = (e h).hom ≫ S.functor.map (Shape.inr old b h hl hr ≫ f) :=
            dest.cell_naturality (Shape.inr old b h hl hr ≫ f)
          _ = ((R.functor ⋙ p).map (Shape.inr old b h hl hr) ≫ c.iso.hom) ≫
              S.functor.map f := by
              calc
                (e h).hom ≫ S.functor.map (Shape.inr old b h hl hr ≫ f) =
                    (e h).hom ≫ (S.functor.map (Shape.inr old b h hl hr) ≫
                      S.functor.map f) := by
                        exact congrArg (fun q => (e h).hom ≫ q)
                          (S.functor.map_comp (Shape.inr old b h hl hr) f)
                _ = ((e h).hom ≫ S.functor.map (Shape.inr old b h hl hr)) ≫
                    S.functor.map f := (Category.assoc _ _ _).symm
                _ = ((R.functor ⋙ p).map (Shape.inr old b h hl hr) ≫ c.iso.hom) ≫
                    S.functor.map f := by rw [← c.inr_hom]
          _ = ((R.functor ⋙ p).map (Shape.inr old b h hl hr) ≫
              (tableComparisonData R S p hp hR e hs ht
                (Table.attach T b h hl hr)).iso.hom) ≫ S.functor.map f := by
                exact congrArg (fun α =>
                  ((R.functor ⋙ p).map (Shape.inr old b h hl hr) ≫ α.hom) ≫
                    S.functor.map f) hcurr.symm
          _ = (R.functor ⋙ p).map (Shape.inr old b h hl hr) ≫
              ((tableComparisonData R S p hp hR e hs ht
                (Table.attach T b h hl hr)).iso.hom ≫ S.functor.map f) :=
                Category.assoc _ _ _

theorem shapeComparisonStatement_proof
    {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    {Y : Type u₁} [Category.{v} Y] [CategoryWithCofibrations Y]
    (R : ShapeInterpretation X) (S : ShapeInterpretation Y) (p : X ⥤ Y)
    (hp : IsCofibrationMorphism p)
    (hR : ∀ (T : Shape) (b : ℕ) (hb : b < T.1),
      cofibrations X (R.functor.map (T.seam hb)))
    (e : ∀ n, p.obj (R.functor.obj (Shape.globe n)) ≅ S.functor.obj (Shape.globe n))
    (hs : ∀ n, p.map (R.functor.map (Shape.source n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.source n))
    (ht : ∀ n, p.map (R.functor.map (Shape.target n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.target n)) :
    ShapeComparisonStatement R S p hp hR e hs ht := by
  change ∃ α : R.functor ⋙ p ≅ S.functor, ∀ n, α.app (Shape.globe n) = e n
  let isoOn : ∀ T : Shape, (R.functor ⋙ p).obj T ≅ S.functor.obj T :=
    fun T => (tableComparisonData R S p hp hR e hs ht T.2).iso
  let α : R.functor ⋙ p ≅ S.functor := NatIso.ofComponents isoOn (by
    intro T U f
    exact tableNaturality R S p hp hR e hs ht T.2 f)
  refine ⟨α, ?_⟩
  intro n
  change (tableComparisonData R S p hp hR e hs ht (Table.globe n)).iso = e n
  rfl

example {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    {Y : Type u₁} [Category.{v} Y] [CategoryWithCofibrations Y]
    (R : ShapeInterpretation X) (S : ShapeInterpretation Y) (p : X ⥤ Y)
    (hp : IsCofibrationMorphism p)
    (hR : ∀ (T : Shape) (b : ℕ) (hb : b < T.1),
      cofibrations X (R.functor.map (T.seam hb)))
    (e : ∀ n, p.obj (R.functor.obj (Shape.globe n)) ≅ S.functor.obj (Shape.globe n))
    (hs : ∀ n, p.map (R.functor.map (Shape.source n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.source n))
    (ht : ∀ n, p.map (R.functor.map (Shape.target n)) ≫ (e (n + 1)).hom =
      (e n).hom ≫ S.functor.map (Shape.target n)) :
    ShapeComparisonStatement R S p hp hR e hs ht :=
  shapeComparisonStatement_proof R S p hp hR e hs ht

#print axioms shapeComparisonStatement_proof

end HomotopyHypothesis.Comparison.GlobularShapes
