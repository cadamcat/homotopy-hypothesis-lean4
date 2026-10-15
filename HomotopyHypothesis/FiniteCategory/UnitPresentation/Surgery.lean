import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.MorphismProperty.Limits
/-!
# Inserting an extension into a transfinite composition

Let `F : J ⥤ C` be a well-order-continuous functor, `k₀ : J` and `g₀ : F k₀ ⟶ X₀'`. The functor
`G : J ⥤ C` agrees with `F` below `k₀`, and is the pushout `F k ⊔_{F k₀} X₀'` at `k ≥ k₀`. If `k₀`
is not a limit element, `G` is again well-order-continuous, and its colimit is the pushout
`Y ⊔_{F k₀} X₀'` of the colimit `Y` of `F`. If the successor maps of `F` and the map `g₀` belong to a
class of morphisms stable under composition, isomorphisms and cobase change, so do those of `G`.
-/

universe w v u

open CategoryTheory Limits

namespace HomotopyHypothesis.FiniteCategory.UnitPresentation.Surgery

variable {C : Type u} [Category.{v} C] [HasPushouts C] {J : Type w} [LinearOrder J]
  (F : J ⥤ C) (k₀ : J) {X₀' : C} (g₀ : F.obj k₀ ⟶ X₀')

/-- The objects of the inserted functor. -/
noncomputable def obj (k : J) : C :=
  if h : k₀ ≤ k then pushout (F.map (homOfLE h)) g₀ else F.obj k

lemma obj_pos {k : J} (h : k₀ ≤ k) : obj F k₀ g₀ k = pushout (F.map (homOfLE h)) g₀ := dif_pos h

lemma obj_neg {k : J} (h : ¬ k₀ ≤ k) : obj F k₀ g₀ k = F.obj k := dif_neg h

/-- The map between two pushouts above `k₀`. -/
noncomputable def mapPP {k k' : J} (h : k₀ ≤ k) (hkk : k ≤ k') :
    pushout (F.map (homOfLE h)) g₀ ⟶ pushout (F.map (homOfLE (h.trans hkk))) g₀ :=
  pushout.desc (F.map (homOfLE hkk) ≫ pushout.inl _ _) (pushout.inr _ _) (by
    rw [← Category.assoc, ← F.map_comp]
    exact pushout.condition)

@[reassoc (attr := simp)]
lemma inl_mapPP {k k' : J} (h : k₀ ≤ k) (hkk : k ≤ k') :
    pushout.inl _ _ ≫ mapPP F k₀ g₀ h hkk = F.map (homOfLE hkk) ≫ pushout.inl _ _ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_mapPP {k k' : J} (h : k₀ ≤ k) (hkk : k ≤ k') :
    pushout.inr _ _ ≫ mapPP F k₀ g₀ h hkk = pushout.inr _ _ :=
  pushout.inr_desc _ _ _

lemma mapPP_id {k : J} (h : k₀ ≤ k) : mapPP F k₀ g₀ h (le_refl k) = 𝟙 _ := by
  apply pushout.hom_ext <;> simp [homOfLE_refl]

lemma mapPP_comp {k k' k'' : J} (h : k₀ ≤ k) (hkk : k ≤ k') (hkk' : k' ≤ k'') :
    mapPP F k₀ g₀ h hkk ≫ mapPP F k₀ g₀ (h.trans hkk) hkk' =
      mapPP F k₀ g₀ h (hkk.trans hkk') := by
  apply pushout.hom_ext
  · simp only [inl_mapPP, inl_mapPP_assoc]
    rw [← F.map_comp_assoc]
    rfl
  · simp

/-- The maps of the inserted functor. -/
noncomputable def map {k k' : J} (hkk : k ≤ k') : obj F k₀ g₀ k ⟶ obj F k₀ g₀ k' :=
  if h : k₀ ≤ k then
    eqToHom (obj_pos F k₀ g₀ h) ≫ mapPP F k₀ g₀ h hkk ≫
      eqToHom (obj_pos F k₀ g₀ (h.trans hkk)).symm
  else if h' : k₀ ≤ k' then
    eqToHom (obj_neg F k₀ g₀ h) ≫ F.map (homOfLE hkk) ≫ pushout.inl _ _ ≫
      eqToHom (obj_pos F k₀ g₀ h').symm
  else
    eqToHom (obj_neg F k₀ g₀ h) ≫ F.map (homOfLE hkk) ≫ eqToHom (obj_neg F k₀ g₀ h').symm

lemma map_pos {k k' : J} (hkk : k ≤ k') (h : k₀ ≤ k) :
    map F k₀ g₀ hkk = eqToHom (obj_pos F k₀ g₀ h) ≫ mapPP F k₀ g₀ h hkk ≫
      eqToHom (obj_pos F k₀ g₀ (h.trans hkk)).symm := dif_pos h

lemma map_neg_pos {k k' : J} (hkk : k ≤ k') (h : ¬ k₀ ≤ k) (h' : k₀ ≤ k') :
    map F k₀ g₀ hkk = eqToHom (obj_neg F k₀ g₀ h) ≫ F.map (homOfLE hkk) ≫ pushout.inl _ _ ≫
      eqToHom (obj_pos F k₀ g₀ h').symm := by
  rw [map, dif_neg h, dif_pos h']

lemma map_neg_neg {k k' : J} (hkk : k ≤ k') (h : ¬ k₀ ≤ k) (h' : ¬ k₀ ≤ k') :
    map F k₀ g₀ hkk = eqToHom (obj_neg F k₀ g₀ h) ≫ F.map (homOfLE hkk) ≫
      eqToHom (obj_neg F k₀ g₀ h').symm := by
  rw [map, dif_neg h, dif_neg h']

/-- The inserted functor. -/
@[simps]
noncomputable def functor : J ⥤ C where
  obj := obj F k₀ g₀
  map φ := map F k₀ g₀ (leOfHom φ)
  map_id k := by
    by_cases h : k₀ ≤ k
    · rw [map_pos _ _ _ _ h, mapPP_id]
      simp
    · rw [map_neg_neg _ _ _ _ h h]
      simp [homOfLE_refl]
  map_comp {k k' k''} φ ψ := by
    have hkk := leOfHom φ
    have hkk' := leOfHom ψ
    by_cases h : k₀ ≤ k
    · have h' := h.trans hkk
      rw [map_pos _ _ _ _ h, map_pos _ _ _ _ h, map_pos _ _ _ _ h']
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [reassoc_of% (mapPP_comp F k₀ g₀ h hkk hkk')]
    · by_cases h' : k₀ ≤ k'
      · rw [map_neg_pos _ _ _ _ h h', map_pos _ _ _ _ h', map_neg_pos _ _ _ _ h (h'.trans hkk')]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
          inl_mapPP_assoc]
        rw [← F.map_comp_assoc]
        rfl
      · by_cases h'' : k₀ ≤ k''
        · rw [map_neg_neg _ _ _ _ h h', map_neg_pos _ _ _ _ h' h'', map_neg_pos _ _ _ _ h h'']
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          rw [← F.map_comp_assoc]
          rfl
        · rw [map_neg_neg _ _ _ _ h h', map_neg_neg _ _ _ _ h' h'', map_neg_neg _ _ _ _ h h'']
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          rw [← F.map_comp_assoc]
          rfl

/-- The comparison map from `F` to the inserted functor. -/
noncomputable def fromF (k : J) : F.obj k ⟶ obj F k₀ g₀ k :=
  if h : k₀ ≤ k then pushout.inl _ _ ≫ eqToHom (obj_pos F k₀ g₀ h).symm
  else eqToHom (obj_neg F k₀ g₀ h).symm

lemma fromF_pos {k : J} (h : k₀ ≤ k) :
    fromF F k₀ g₀ k = pushout.inl _ _ ≫ eqToHom (obj_pos F k₀ g₀ h).symm := dif_pos h

lemma fromF_neg {k : J} (h : ¬ k₀ ≤ k) :
    fromF F k₀ g₀ k = eqToHom (obj_neg F k₀ g₀ h).symm := dif_neg h

/-- The inclusion of the extension into the inserted functor at `k₀`. -/
noncomputable def fromExt : X₀' ⟶ obj F k₀ g₀ k₀ :=
  pushout.inr _ _ ≫ eqToHom (obj_pos F k₀ g₀ (le_refl k₀)).symm

lemma fromF_naturality {k k' : J} (hkk : k ≤ k') :
    F.map (homOfLE hkk) ≫ fromF F k₀ g₀ k' = fromF F k₀ g₀ k ≫ map F k₀ g₀ hkk := by
  by_cases h : k₀ ≤ k
  · rw [fromF_pos _ _ _ h, fromF_pos _ _ _ (h.trans hkk), map_pos _ _ _ _ h]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [inl_mapPP_assoc]
  · by_cases h' : k₀ ≤ k'
    · rw [fromF_neg _ _ _ h, fromF_pos _ _ _ h', map_neg_pos _ _ _ _ h h']
      simp
    · rw [fromF_neg _ _ _ h, fromF_neg _ _ _ h', map_neg_neg _ _ _ _ h h']
      simp

lemma fromF_k₀ : fromF F k₀ g₀ k₀ = g₀ ≫ fromExt F k₀ g₀ := by
  rw [fromF_pos _ _ _ (le_refl k₀), fromExt, ← Category.assoc, ← pushout.condition]
  simp [homOfLE_refl]

section Cocone

variable {F} {K : Type*} [Preorder K] {Φ : K → J} {hΦ : Monotone Φ}
  (hΦ' : ∀ a b, Φ a ≤ Φ b → a ≤ b) (κ₀ : K) (e₀ : F.obj (Φ κ₀) ⟶ X₀')
  (c : Cocone (hΦ.functor ⋙ F))

/-- The legs of a cocone, typed by its point. -/
def leg (k : K) : F.obj (Φ k) ⟶ c.pt := c.ι.app k

include hΦ' in
@[reassoc]
lemma leg_w {k k' : K} (h : Φ k ≤ Φ k') : F.map (homOfLE h) ≫ leg c k' = leg c k :=
  c.w (homOfLE (hΦ' _ _ h))

/-- The structure maps of the inserted functor to the pushout of the colimit. -/
noncomputable def coconeApp (k : K) :
    obj F (Φ κ₀) e₀ (Φ k) ⟶ pushout (leg c κ₀) e₀ :=
  if h : Φ κ₀ ≤ Φ k then
    eqToHom (obj_pos F (Φ κ₀) e₀ h) ≫
      pushout.desc (leg c k ≫ pushout.inl _ _) (pushout.inr _ _)
        (by rw [← Category.assoc, leg_w hΦ' c h]; exact pushout.condition)
  else eqToHom (obj_neg F (Φ κ₀) e₀ h) ≫ leg c k ≫ pushout.inl _ _

lemma coconeApp_pos {k : K} (h : Φ κ₀ ≤ Φ k) :
    coconeApp hΦ' κ₀ e₀ c k = eqToHom (obj_pos F (Φ κ₀) e₀ h) ≫
      pushout.desc (leg c k ≫ pushout.inl _ _) (pushout.inr _ _)
        (by rw [← Category.assoc, leg_w hΦ' c h]; exact pushout.condition) := dif_pos h

lemma coconeApp_neg {k : K} (h : ¬ Φ κ₀ ≤ Φ k) :
    coconeApp hΦ' κ₀ e₀ c k = eqToHom (obj_neg F (Φ κ₀) e₀ h) ≫ leg c k ≫ pushout.inl _ _ :=
  dif_neg h

/-- The cocone of the inserted functor over the pushout of a cocone of `F`. -/
@[simps]
noncomputable def cocone : Cocone (hΦ.functor ⋙ functor F (Φ κ₀) e₀) where
  pt := pushout (leg c κ₀) e₀
  ι :=
    { app := coconeApp hΦ' κ₀ e₀ c
      naturality {k k'} φ := by
        have hkk := hΦ (leOfHom φ)
        change map F (Φ κ₀) e₀ hkk ≫ coconeApp hΦ' κ₀ e₀ c k' =
          coconeApp hΦ' κ₀ e₀ c k ≫ 𝟙 _
        rw [Category.comp_id]
        by_cases h : Φ κ₀ ≤ Φ k
        · rw [map_pos _ _ _ _ h, coconeApp_pos _ _ _ _ h, coconeApp_pos _ _ _ _ (h.trans hkk)]
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          congr 1
          apply pushout.hom_ext
          · rw [inl_mapPP_assoc, pushout.inl_desc, pushout.inl_desc, ← Category.assoc,
              leg_w hΦ' c hkk]
          · rw [inr_mapPP_assoc, pushout.inr_desc, pushout.inr_desc]
        · by_cases h' : Φ κ₀ ≤ Φ k'
          · rw [map_neg_pos _ _ _ _ h h', coconeApp_neg _ _ _ _ h, coconeApp_pos _ _ _ _ h']
            simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
            rw [pushout.inl_desc, ← Category.assoc (F.map _), leg_w hΦ' c hkk]
          · rw [map_neg_neg _ _ _ _ h h', coconeApp_neg _ _ _ _ h, coconeApp_neg _ _ _ _ h']
            simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
            rw [← Category.assoc (F.map _), leg_w hΦ' c hkk] }

lemma fromF_coconeApp (k : K) :
    fromF F (Φ κ₀) e₀ (Φ k) ≫ coconeApp hΦ' κ₀ e₀ c k = leg c k ≫ pushout.inl _ _ := by
  by_cases h : Φ κ₀ ≤ Φ k
  · rw [fromF_pos _ _ _ h, coconeApp_pos _ _ _ _ h]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [pushout.inl_desc]
  · rw [fromF_neg _ _ _ h, coconeApp_neg _ _ _ _ h]
    simp

lemma fromExt_coconeApp :
    fromExt F (Φ κ₀) e₀ ≫ coconeApp hΦ' κ₀ e₀ c κ₀ = pushout.inr _ _ := by
  rw [fromExt, coconeApp_pos _ _ _ _ (le_refl (Φ κ₀))]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [pushout.inr_desc]

variable {κ₀ e₀}

/-- The legs of a cocone of the inserted functor, typed by `obj`. -/
def legs (s : Cocone (hΦ.functor ⋙ functor F (Φ κ₀) e₀)) (k : K) :
    obj F (Φ κ₀) e₀ (Φ k) ⟶ s.pt := s.ι.app k

lemma legs_w (s : Cocone (hΦ.functor ⋙ functor F (Φ κ₀) e₀)) {k k' : K} (hkk : k ≤ k') :
    map F (Φ κ₀) e₀ (hΦ hkk) ≫ legs s k' = legs s k :=
  s.w (homOfLE hkk)

/-- The cocone of `F` induced by a cocone of the inserted functor. -/
@[simps]
noncomputable def restrictCocone (s : Cocone (hΦ.functor ⋙ functor F (Φ κ₀) e₀)) :
    Cocone (hΦ.functor ⋙ F) where
  pt := s.pt
  ι :=
    { app k := fromF F (Φ κ₀) e₀ (Φ k) ≫ legs s k
      naturality {k k'} φ := by
        change F.map (homOfLE (hΦ (leOfHom φ))) ≫ fromF F (Φ κ₀) e₀ (Φ k') ≫ legs s k' =
          (fromF F (Φ κ₀) e₀ (Φ k) ≫ legs s k) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, fromF_naturality F (Φ κ₀) e₀ (hΦ (leOfHom φ)),
          Category.assoc, legs_w] }

variable {c} in
/-- The map out of the colimit of `F` induced by a cocone of the inserted functor. -/
noncomputable def descF (hc : IsColimit c) (s : Cocone (hΦ.functor ⋙ functor F (Φ κ₀) e₀)) :
    c.pt ⟶ s.pt :=
  hc.desc (restrictCocone s)

variable {c} in
@[reassoc]
lemma leg_descF (hc : IsColimit c) (s : Cocone (hΦ.functor ⋙ functor F (Φ κ₀) e₀)) (k : K) :
    leg c k ≫ descF hc s = fromF F (Φ κ₀) e₀ (Φ k) ≫ legs s k :=
  hc.fac (restrictCocone s) k

variable (κ₀ e₀) in
/-- The pushout cocone is a colimit if the cocone of `F` is. -/
noncomputable def isColimitCocone (hc : IsColimit c) :
    IsColimit (cocone hΦ' κ₀ e₀ c) where
  desc s := pushout.desc (descF hc s)
    (fromExt F (Φ κ₀) e₀ ≫ legs s κ₀) (by
      rw [leg_descF, fromF_k₀, Category.assoc])
  fac s k := by
    change coconeApp hΦ' κ₀ e₀ c k ≫ _ = legs s k
    by_cases h : Φ κ₀ ≤ Φ k
    · rw [coconeApp_pos _ _ _ _ h, Category.assoc,
        ← cancel_epi (eqToHom (obj_pos F (Φ κ₀) e₀ h).symm),
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      apply pushout.hom_ext
      · rw [pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc, leg_descF,
          fromF_pos _ _ _ h, Category.assoc]
      · rw [pushout.inr_desc_assoc, pushout.inr_desc, ← legs_w s (hΦ' _ _ h),
          map_pos _ _ _ _ (le_refl (Φ κ₀)), fromExt]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [inr_mapPP_assoc]
    · rw [coconeApp_neg _ _ _ _ h, Category.assoc, Category.assoc, pushout.inl_desc, leg_descF,
        fromF_neg _ _ _ h, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  uniq s m hm := by
    let m' : pushout (leg c κ₀) e₀ ⟶ s.pt := m
    change m' = _
    have hm' : ∀ k, coconeApp hΦ' κ₀ e₀ c k ≫ m' = legs s k := hm
    clear_value m'
    apply pushout.hom_ext
    · rw [pushout.inl_desc]
      apply hc.hom_ext
      intro k
      change leg c k ≫ _ = leg c k ≫ _
      rw [leg_descF, ← Category.assoc, ← fromF_coconeApp hΦ' κ₀ e₀ c k, Category.assoc, hm']
    · rw [pushout.inr_desc, ← fromExt_coconeApp hΦ' κ₀ e₀ c, Category.assoc, hm']

end Cocone

section Chain

variable [OrderBot J] [SuccOrder J] [WellFoundedLT J] [F.IsWellOrderContinuous]

/-- The cocone of the inserted functor over the pushout of a cocone of `F` (unrestricted). -/
noncomputable def coconeJ (c : Cocone F) : Cocone (functor F k₀ g₀) where
  pt := pushout (c.ι.app k₀) g₀
  ι :=
    { app k := (cocone (hΦ := monotone_id) (fun _ _ h => h) k₀ g₀
        (c.whisker monotone_id.functor)).ι.app k
      naturality {k k'} φ := (cocone (hΦ := monotone_id) (fun _ _ h => h) k₀ g₀
        (c.whisker monotone_id.functor)).ι.naturality φ }

/-- The pushout of the colimit of `F` is the colimit of the inserted functor. -/
noncomputable def isColimitCoconeJ {c : Cocone F} (hc : IsColimit c) :
    IsColimit (coconeJ F k₀ g₀ c) := by
  have : (monotone_id (α := J)).functor.IsEquivalence :=
    Functor.isEquivalence_of_iso (F := 𝟭 J)
      (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))
  have h := isColimitCocone (hΦ := monotone_id) (fun _ _ h => h) k₀ g₀
    (c.whisker monotone_id.functor)
    ((Functor.Final.isColimitWhiskerEquiv (monotone_id (α := J)).functor c).symm hc)
  exact (Functor.Final.isColimitWhiskerEquiv (monotone_id (α := J)).functor _) h

/-- The inserted functor is well-order-continuous when `k₀` is not a limit element. -/
lemma isWellOrderContinuous (hk₀ : ¬ Order.IsSuccLimit k₀) :
    (functor F k₀ g₀).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    have hF := F.isColimitOfIsWellOrderContinuous m hm
    by_cases h : k₀ ≤ m
    · have hlt : k₀ < m := lt_of_le_of_ne h (fun e => hk₀ (e ▸ hm))
      let φ := Set.principalSegIio m
      have hΦ' : ∀ a b : Set.Iio m, φ a ≤ φ b → a ≤ b := fun a b h => (φ.le_iff_le).1 h
      let κ₀ : Set.Iio m := ⟨k₀, hlt⟩
      have hc := isColimitCocone (hΦ := φ.monotone) hΦ' κ₀ g₀ (φ.cocone F) hF
      refine ⟨IsColimit.ofIsoColimit hc (Cocone.ext
        (eqToIso (show pushout (F.map (homOfLE h)) g₀ = obj F k₀ g₀ m from
          (obj_pos F k₀ g₀ h).symm)) ?_)⟩
      intro k
      change coconeApp hΦ' κ₀ g₀ (φ.cocone F) k ≫ eqToHom (obj_pos F k₀ g₀ h).symm =
        map F k₀ g₀ (le_of_lt k.2)
      by_cases hk : k₀ ≤ k.1
      · rw [coconeApp_pos _ _ _ _ hk, map_pos _ _ _ _ hk, Category.assoc]
        rfl
      · rw [coconeApp_neg _ _ _ _ hk, map_neg_pos _ _ _ _ hk h, Category.assoc, Category.assoc]
        rfl
    · let φ := Set.principalSegIio m
      have hk : ∀ k : Set.Iio m, ¬ k₀ ≤ k.1 := fun k hk => h (hk.trans k.2.le)
      let α : φ.monotone.functor ⋙ F ≅ φ.monotone.functor ⋙ functor F k₀ g₀ :=
        NatIso.ofComponents (fun k => eqToIso (obj_neg F k₀ g₀ (hk k)).symm) (by
          intro k k' f
          change F.map (homOfLE (leOfHom f)) ≫ eqToHom (obj_neg F k₀ g₀ (hk k')).symm =
            eqToHom (obj_neg F k₀ g₀ (hk k)).symm ≫ map F k₀ g₀ (leOfHom f)
          rw [map_neg_neg _ _ _ _ (hk k) (hk k')]
          simp)
      refine ⟨(IsColimit.precomposeHomEquiv α _).1
        (IsColimit.ofIsoColimit hF (Cocone.ext (eqToIso (obj_neg F k₀ g₀ h).symm) ?_))⟩
      intro k
      change F.map (homOfLE (le_of_lt k.2)) ≫ eqToHom (obj_neg F k₀ g₀ h).symm =
        eqToHom (obj_neg F k₀ g₀ (hk k)).symm ≫ map F k₀ g₀ (le_of_lt k.2)
      rw [map_neg_neg _ _ _ _ (hk k) h]
      simp

end Chain

lemma isPushout_mapPP {k k' : J} (h : k₀ ≤ k) (hkk : k ≤ k') :
    IsPushout (pushout.inl (F.map (homOfLE h)) g₀) (F.map (homOfLE hkk))
      (mapPP F k₀ g₀ h hkk) (pushout.inl (F.map (homOfLE (h.trans hkk))) g₀) := by
  have e1 : F.map (homOfLE h) ≫ F.map (homOfLE hkk) = F.map (homOfLE (h.trans hkk)) := by
    rw [← F.map_comp]; rfl
  have s : IsPushout (F.map (homOfLE h) ≫ F.map (homOfLE hkk)) g₀
      (pushout.inl (F.map (homOfLE (h.trans hkk))) g₀)
      (pushout.inr (F.map (homOfLE h)) g₀ ≫ mapPP F k₀ g₀ h hkk) := by
    rw [e1, inr_mapPP]
    exact IsPushout.of_hasPushout _ _
  exact (IsPushout.of_left s (inl_mapPP F k₀ g₀ h hkk).symm
    (IsPushout.of_hasPushout _ _)).flip

section Chain

variable [OrderBot J] [SuccOrder J] [WellFoundedLT J] {W : MorphismProperty C}
  [W.IsMultiplicative] [W.RespectsIso] [W.IsStableUnderCobaseChange]

variable {F k₀ g₀} in
lemma map_mem (hF : ∀ (k : J), ¬ IsMax k → W (F.map (homOfLE (Order.le_succ k))))
    (hg₀ : W g₀) (k : J) (hk : ¬ IsMax k) :
    W (map F k₀ g₀ (Order.le_succ k)) := by
  by_cases h : k₀ ≤ k
  · rw [map_pos _ _ _ _ h]
    apply MorphismProperty.RespectsIso.precomp
    apply MorphismProperty.RespectsIso.postcomp
    exact MorphismProperty.of_isPushout (isPushout_mapPP F k₀ g₀ h (Order.le_succ k)) (hF k hk)
  · by_cases h' : k₀ ≤ Order.succ k
    · rw [map_neg_pos _ _ _ _ h h']
      apply MorphismProperty.RespectsIso.precomp
      rw [← Category.assoc]
      apply MorphismProperty.RespectsIso.postcomp
      exact W.comp_mem _ _ (hF k hk)
        (MorphismProperty.of_isPushout (IsPushout.of_hasPushout _ _) hg₀)
    · rw [map_neg_neg _ _ _ _ h h']
      apply MorphismProperty.RespectsIso.precomp
      apply MorphismProperty.RespectsIso.postcomp
      exact hF k hk

/-- **Inserting an extension into a transfinite composition.** If `f : X ⟶ Y` is a transfinite
composition of maps in `W`, `⊥ < k₀` is not a limit element and `g₀ : F k₀ ⟶ X₀'` is in `W`, then
`X ⟶ Y ⊔_{F k₀} X₀'` is a transfinite composition of maps in `W` whose stages below `k₀` are
those of `f`, and whose stages at `k ≥ k₀` are the pushouts `F k ⊔_{F k₀} X₀'`. -/
noncomputable def transfiniteComposition {X Y : C} {f : X ⟶ Y}
    (c : W.TransfiniteCompositionOfShape J f) (k₀ : J) (hk₀ : ¬ Order.IsSuccLimit k₀)
    (hb : ⊥ < k₀) {X₀' : C} (g₀ : c.F.obj k₀ ⟶ X₀') (hg₀ : W g₀) :
    W.TransfiniteCompositionOfShape J (f ≫ pushout.inl (c.incl.app k₀) g₀) where
  F := functor c.F k₀ g₀
  isoBot := eqToIso (obj_neg c.F k₀ g₀ (not_le.mpr hb)) ≪≫ c.isoBot
  isWellOrderContinuous := isWellOrderContinuous c.F k₀ g₀ hk₀
  incl := (coconeJ c.F k₀ g₀ (Cocone.mk Y c.incl)).ι
  isColimit := isColimitCoconeJ c.F k₀ g₀ c.isColimit
  fac := by
    change (c.isoBot.inv ≫ eqToHom (obj_neg c.F k₀ g₀ (not_le.mpr hb)).symm) ≫
      coconeApp (hΦ := monotone_id) (fun _ _ h => h) k₀ g₀
      ((Cocone.mk Y c.incl).whisker monotone_id.functor) ⊥ = _
    rw [coconeApp_neg _ _ _ _ (not_le.mpr hb)]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc]
    congr 1
    exact c.fac
  map_mem k hk := map_mem (fun k hk => c.map_mem k hk) hg₀ k hk

/-- The stages of the inserted chain receive maps in `W` from those of the original chain. -/
lemma exists_stage_map {X Y : C} {f : X ⟶ Y}
    (c : W.TransfiniteCompositionOfShape J f) (k₀ : J) (hk₀ : ¬ Order.IsSuccLimit k₀)
    (hb : ⊥ < k₀) {X₀' : C} (g₀ : c.F.obj k₀ ⟶ X₀') (hg₀ : W g₀) (k : J) :
    ∃ e : c.F.obj k ⟶ (transfiniteComposition c k₀ hk₀ hb g₀ hg₀).F.obj k, W e := by
  refine ⟨fromF c.F k₀ g₀ k, ?_⟩
  by_cases h : k₀ ≤ k
  · rw [fromF_pos _ _ _ h]
    apply MorphismProperty.RespectsIso.postcomp
    exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout _ _) hg₀
  · rw [fromF_neg _ _ _ h]
    have := MorphismProperty.RespectsIso.postcomp W (eqToHom (obj_neg c.F k₀ g₀ h).symm)
      (𝟙 _) (W.id_mem _)
    rw [Category.id_comp] at this
    exact this

end Chain

end HomotopyHypothesis.FiniteCategory.UnitPresentation.Surgery
