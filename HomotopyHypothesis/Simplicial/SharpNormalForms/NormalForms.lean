import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Simplicial.SharpNormalForms

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- Restriction along a semi-simplicial map acts on formal degeneracies by precomposition. -/
theorem sharp_map_mk {X : SemiSSet.{u}} {n n' m : ℕ}
    (θ : Henry.SemiSimplexCategory.mk n' ⟶ Henry.SemiSimplexCategory.mk n)
    (v : Fin (n + 1) → Fin (m + 1))
    (x : X.obj (op (Henry.SemiSimplexCategory.mk m))) :
    (sharp X).map θ.op (sharpMk v x) =
      sharpMk (v ∘ θ.1.toOrderHom) x := by
  let L := Henry.SemiSimplexCategory.toFinFun.op
  let E := L.leftKanExtension X
  change ((E.map (Quiver.Hom.op v) ≫
      E.map (Quiver.Hom.op θ.1.toOrderHom))
      (((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk m))) x)) =
    (E.map (Quiver.Hom.op (v ∘ θ.1.toOrderHom)))
      (((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk m))) x)
  rw [← Functor.map_comp]
  congr 1

/-- Enlarging the simplex represented by a formal degeneracy does not change it. -/
theorem sharp_mk_face {X : SemiSSet.{u}} {n k m : ℕ}
    (ι : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m)
    (v : Fin (n + 1) → Fin (k + 1))
    (x : X.obj (op (Henry.SemiSimplexCategory.mk m))) :
    sharpMk (ι.1.toOrderHom ∘ v) x =
      sharpMk v (X.map ι.op x) := by
  let L := Henry.SemiSimplexCategory.toFinFun.op
  let E := L.leftKanExtension X
  change (E.map (Quiver.Hom.op (ι.1.toOrderHom ∘ v)))
      (((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk m))) x) =
    (E.map (Quiver.Hom.op v))
      (((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk k)))
        ((X.map ι.op) x))
  have hcomp :
      (Quiver.Hom.op (ι.1.toOrderHom ∘ v) :
        Opposite.op (⟨m⟩ : Henry.FinFun) ⟶ Opposite.op ⟨n⟩) =
      (Quiver.Hom.op (ι.1.toOrderHom) :
        Opposite.op (⟨m⟩ : Henry.FinFun) ⟶ Opposite.op ⟨k⟩) ≫
      (Quiver.Hom.op v : Opposite.op (⟨k⟩ : Henry.FinFun) ⟶ Opposite.op ⟨n⟩) := by
    rw [← op_comp]
    rfl
  rw [hcomp, Functor.map_comp]
  have hmap :
      (Quiver.Hom.op (ι.1.toOrderHom) :
        Opposite.op (⟨m⟩ : Henry.FinFun) ⟶ Opposite.op ⟨k⟩) = L.map ι.op := by
    rfl
  have hη :
      ((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk k)))
          ((X.map ι.op) x) =
        (E.map (L.map ι.op))
          (((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk m))) x) := by
    have hn := NatTrans.naturality (L.leftKanExtensionUnit X) ι.op
    have h := congrArg (fun f : X.obj (op (Henry.SemiSimplexCategory.mk m)) ⟶
        E.obj (L.obj (op (Henry.SemiSimplexCategory.mk k))) => f x) hn
    simpa only [Functor.comp_map, ConcreteCategory.comp_apply] using h
  rw [hmap]
  change (E.map (Quiver.Hom.op v))
      ((E.map (L.map ι.op))
        (((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk m))) x)) =
    (E.map (Quiver.Hom.op v))
      (((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk k)))
        ((X.map ι.op) x))
  exact congrArg (E.map (Quiver.Hom.op v)) hη.symm


private def sharpImage {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) : Finset (Fin (m + 1)) :=
  Finset.univ.image v

private theorem sharpImage_card_pos {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    0 < (sharpImage v).card := by
  apply Finset.card_pos.mpr
  refine ⟨v 0, ?_⟩
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

private def sharpImageSize {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) : ℕ :=
  (sharpImage v).card - 1

private theorem sharpImage_card_eq {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    (sharpImage v).card = sharpImageSize v + 1 := by
  dsimp [sharpImageSize]
  exact (Nat.sub_add_cancel (sharpImage_card_pos v)).symm

private noncomputable def sharpImageOrderIso {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) :
    Fin (sharpImageSize v + 1) ≃o sharpImage v :=
  (sharpImage v).orderIsoOfFin (sharpImage_card_eq v)

private noncomputable def sharpImageEmbedding {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) :
    Fin (sharpImageSize v + 1) ↪o Fin (m + 1) :=
  (sharpImageOrderIso v).toOrderEmbedding.trans (OrderEmbedding.subtype _)

private theorem sharpImage_mem {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) (i : Fin (n + 1)) :
    v i ∈ sharpImage v :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private noncomputable def sharpImageFactor {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    Fin (n + 1) → Fin (sharpImageSize v + 1) := fun i =>
  (sharpImageOrderIso v).symm ⟨v i, sharpImage_mem v i⟩

private theorem sharpImage_factor {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (i : Fin (n + 1)) : sharpImageEmbedding v (sharpImageFactor v i) = v i := by
  have h := (sharpImageOrderIso v).apply_symm_apply
    (⟨v i, sharpImage_mem v i⟩ : sharpImage v)
  change ((sharpImageOrderIso v) ((sharpImageOrderIso v).symm ⟨v i, sharpImage_mem v i⟩)).val = _
  exact congrArg Subtype.val h

private theorem sharpImageFactor_surjective {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) :
    Function.Surjective (sharpImageFactor v) := by
  intro j
  have hj : sharpImageEmbedding v j ∈ sharpImage v := by
    exact (sharpImageOrderIso v j).property
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hj
  refine ⟨i, ?_⟩
  have hval : (sharpImageOrderIso v) (sharpImageFactor v i) =
      (sharpImageOrderIso v) j := by
    rw [sharpImageFactor, OrderIso.apply_symm_apply]
    apply Subtype.ext
    simpa [sharpImageEmbedding] using hi
  exact (sharpImageOrderIso v).injective hval


private theorem sharpImageSize_comp {n k m : ℕ}
    (ι : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m)
    (v : Fin (n + 1) → Fin (k + 1)) :
    sharpImageSize (ι.1.toOrderHom ∘ v) = sharpImageSize v := by
  have hi : Function.Injective ι.1.toOrderHom := by
    rw [← SimplexCategory.mono_iff_injective]
    exact ι.2
  unfold sharpImageSize sharpImage
  rw [← Finset.image_image]
  rw [Finset.card_image_of_injective _ hi]

private noncomputable def sharpSemiEmbedding {k m : ℕ}
    (ι : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m) :
    Fin (k + 1) ↪o Fin (m + 1) :=
  OrderEmbedding.ofStrictMono ι.1.toOrderHom
    (ι.1.toOrderHom.monotone.strictMono_of_injective (by
      rw [← SimplexCategory.mono_iff_injective]
      exact ι.2))

private theorem sharpImageEmbedding_comp_cast {n k m : ℕ}
    (ι : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m)
    (v : Fin (n + 1) → Fin (k + 1)) (j : Fin (sharpImageSize (ι.1.toOrderHom ∘ v) + 1)) :
    sharpImageEmbedding (ι.1.toOrderHom ∘ v) j =
      ι.1.toOrderHom (sharpImageEmbedding v
        (Fin.cast (congrArg Nat.succ (sharpImageSize_comp ι v)) j)) := by
  let h := sharpImageSize_comp ι v
  let c : Fin (sharpImageSize (ι.1.toOrderHom ∘ v) + 1) ↪o
      Fin (sharpImageSize v + 1) :=
    (Fin.castOrderIso (congrArg Nat.succ h)).toOrderEmbedding
  let candidate : Fin (sharpImageSize (ι.1.toOrderHom ∘ v) + 1) ↪o Fin (m + 1) :=
    c.trans ((sharpImageEmbedding v).trans (sharpSemiEmbedding ι))
  have hcand (j : Fin (sharpImageSize (ι.1.toOrderHom ∘ v) + 1)) :
      candidate j = ι.1.toOrderHom (sharpImageEmbedding v
        (Fin.cast (congrArg Nat.succ h) j)) := by
    simp [candidate, c, sharpSemiEmbedding]
  have hmem : ∀ j, candidate j ∈ sharpImage (ι.1.toOrderHom ∘ v) := by
    intro j
    rw [hcand]
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp
      (sharpImageOrderIso v (Fin.cast (congrArg Nat.succ h) j)).property
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    change ι.1.toOrderHom (v i) =
      ι.1.toOrderHom ((sharpImageOrderIso v (Fin.cast (congrArg Nat.succ h) j)).val)
    rw [hi]
  have hu := Finset.orderEmbOfFin_unique'
    (sharpImage_card_eq (ι.1.toOrderHom ∘ v)) hmem
  have hu' : candidate = sharpImageEmbedding (ι.1.toOrderHom ∘ v) := by
    change candidate =
      (sharpImage (ι.1.toOrderHom ∘ v)).orderEmbOfFin
        (sharpImage_card_eq (ι.1.toOrderHom ∘ v))
    exact hu
  calc
    sharpImageEmbedding (ι.1.toOrderHom ∘ v) j = candidate j :=
      congrArg (fun e : Fin (sharpImageSize (ι.1.toOrderHom ∘ v) + 1) ↪o
        Fin (m + 1) => e j) hu'.symm
    _ = ι.1.toOrderHom (sharpImageEmbedding v
          (Fin.cast (congrArg Nat.succ h) j)) := hcand j

private theorem sharpImageFactor_comp_cast {n k m : ℕ}
    (ι : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m)
    (v : Fin (n + 1) → Fin (k + 1)) (i : Fin (n + 1)) :
    Fin.cast (congrArg Nat.succ (sharpImageSize_comp ι v))
        (sharpImageFactor (ι.1.toOrderHom ∘ v) i) = sharpImageFactor v i := by
  have hi : Function.Injective ι.1.toOrderHom := by
    rw [← SimplexCategory.mono_iff_injective]
    exact ι.2
  apply (sharpImageEmbedding v).injective
  have hleft : ι.1.toOrderHom (sharpImageEmbedding v
      (Fin.cast (congrArg Nat.succ (sharpImageSize_comp ι v))
        (sharpImageFactor (ι.1.toOrderHom ∘ v) i))) = ι.1.toOrderHom (v i) := by
    calc
      _ = sharpImageEmbedding (ι.1.toOrderHom ∘ v)
            (sharpImageFactor (ι.1.toOrderHom ∘ v) i) :=
          (sharpImageEmbedding_comp_cast ι v _).symm
      _ = (ι.1.toOrderHom ∘ v) i := sharpImage_factor _ _
      _ = ι.1.toOrderHom (v i) := rfl
  exact (hi hleft).trans (sharpImage_factor v i).symm

private noncomputable def sharpImageFace {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    Henry.SemiSimplexCategory.mk (sharpImageSize v) ⟶ Henry.SemiSimplexCategory.mk m := by
  let f : SimplexCategory.mk (sharpImageSize v) ⟶ SimplexCategory.mk m :=
    SimplexCategory.Hom.mk (sharpImageEmbedding v)
  have hf : Mono f := by
    rw [SimplexCategory.mono_iff_injective]
    exact (sharpImageEmbedding v).injective
  exact ⟨f, hf⟩



private theorem sharpSemiEqToOrderHom {r s : ℕ} (h : r = s) :
    (eqToHom (congrArg Henry.SemiSimplexCategory.mk h)).1.toOrderHom =
      (Fin.castOrderIso (congrArg Nat.succ h)).toOrderEmbedding.toOrderHom := by
  change SimplexCategory.Hom.toOrderHom
      (Henry.SemiSimplexCategory.incl.map
        (eqToHom (congrArg Henry.SemiSimplexCategory.mk h))) = _
  rw [eqToHom_map]
  rw [SimplexCategory.eqToHom_toOrderHom]
  simp only [Henry.SemiSimplexCategory.mk]
  rfl

private theorem sharpSemiEqToFun {r s : ℕ} (h : r = s) :
    (eqToHom (congrArg Henry.SemiSimplexCategory.mk h)).1.toOrderHom =
      (Fin.cast (congrArg Nat.succ h) : Fin (r + 1) → Fin (s + 1)) := by
  exact congrArg OrderHom.toFun (sharpSemiEqToOrderHom h)

private theorem sharpImageFace_toOrderHom {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    (sharpImageFace v).1.toOrderHom = (sharpImageEmbedding v).toOrderHom := by
  rfl

private theorem sharpImageFace_comp {n k m : ℕ}
    (ι : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m)
    (v : Fin (n + 1) → Fin (k + 1)) :
    sharpImageFace (n := n) (m := m) (ι.1.toOrderHom ∘ v) =
      eqToHom (congrArg Henry.SemiSimplexCategory.mk (sharpImageSize_comp ι v)) ≫
        sharpImageFace (n := n) (m := k) v ≫ ι := by
  have hsize := sharpImageSize_comp ι v
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext j
  rw [sharpImageFace_toOrderHom]
  rw [OrderEmbedding.toOrderHom_coe]
  rw [sharpImageEmbedding_comp_cast]
  rw [WideSubcategory.comp_def, WideSubcategory.comp_def]
  rw [SimplexCategory.comp_toOrderHom, SimplexCategory.comp_toOrderHom]
  dsimp [OrderHom.comp]
  rw [sharpSemiEqToFun]
  change ι.1.toOrderHom (sharpImageEmbedding v
      (Fin.cast (congrArg Nat.succ hsize) j)) =
    ι.1.toOrderHom (sharpImageEmbedding v
      ((Fin.castOrderIso (congrArg Nat.succ hsize)).toOrderEmbedding j))
  congr 1
  exact hsize


private abbrev SharpSimplexCode (X : SemiSSet.{u}) :=
  Σ A : Henry.SemiSimplexCategory, X.obj (op A)

private abbrev SharpNormalData (X : SemiSSet.{u}) (n : ℕ) :=
  (Fin (n + 1) → ℕ) × SharpSimplexCode X

private def SharpNormalProperty (X : SemiSSet.{u}) (n m : ℕ)
    (p : SharpNormalData X n) : Prop :=
  (∀ i, p.1 i < m + 1) ∧
    (∀ j, j < m + 1 → ∃ i, p.1 i = j) ∧
      p.2.1 = Henry.SemiSimplexCategory.mk m

private def SharpNormalForm (X : SemiSSet.{u}) (n : ℕ) :=
  Σ m : ℕ, {p : SharpNormalData X n // SharpNormalProperty X n m p}

private abbrev SharpIndex (n : ℕ) :=
  CostructuredArrow Henry.SemiSimplexCategory.toFinFun.op (op (⟨n⟩ : Henry.FinFun))

private noncomputable def sharpDiagram (X : SemiSSet.{u}) (n : ℕ) :
    SharpIndex n ⥤ Type u :=
  CostructuredArrow.proj Henry.SemiSimplexCategory.toFinFun.op
    (op (⟨n⟩ : Henry.FinFun)) ⋙ X

private theorem semiSimplex_mk_len (A : Henry.SemiSimplexCategory) :
    Henry.SemiSimplexCategory.mk A.obj.len = A := by
  cases A with
  | mk a => cases a; rfl

private noncomputable def canonicalSemiMap {A B : Henry.SemiSimplexCategory}
    (f : B ⟶ A) :
    Henry.SemiSimplexCategory.mk B.obj.len ⟶ Henry.SemiSimplexCategory.mk A.obj.len :=
  eqToHom (semiSimplex_mk_len B) ≫ f ≫ eqToHom (semiSimplex_mk_len A).symm

private noncomputable def sharpImageFaceInto {n : ℕ} {A : Henry.SemiSimplexCategory}
    (v : Fin (n + 1) → Fin (A.obj.len + 1)) :
    Henry.SemiSimplexCategory.mk (sharpImageSize v) ⟶ A :=
  sharpImageFace v ≫ eqToHom (semiSimplex_mk_len A)

private def sharpStageMap {n : ℕ} (a : SharpIndex n) :
    Fin (n + 1) → Fin (a.left.unop.obj.len + 1) :=
  a.hom.unop


private theorem sharpImageFactor_congr {n m : ℕ}
    {v w : Fin (n + 1) → Fin (m + 1)} (h : v = w) (i : Fin (n + 1)) :
    Fin.cast (congrArg Nat.succ (congrArg sharpImageSize h))
      (sharpImageFactor v i) = sharpImageFactor w i := by
  cases h
  simp


private theorem sharpImageFaceInto_factor {n : ℕ} {A : Henry.SemiSimplexCategory}
    (v : Fin (n + 1) → Fin (A.obj.len + 1)) :
    (sharpImageFaceInto v).1.toOrderHom ∘ sharpImageFactor v = v := by
  funext i
  change sharpImageEmbedding v (sharpImageFactor v i) = v i
  exact sharpImage_factor v i

private theorem sharpImageFaceInto_congr {n : ℕ} {A : Henry.SemiSimplexCategory}
    {v w : Fin (n + 1) → Fin (A.obj.len + 1)} (h : v = w) :
    sharpImageFaceInto v =
      eqToHom (congrArg Henry.SemiSimplexCategory.mk (congrArg sharpImageSize h)) ≫
        sharpImageFaceInto w := by
  cases h
  simp

private theorem canonicalSemiMap_toOrderHom {A B : Henry.SemiSimplexCategory}
    (f : B ⟶ A) :
    (canonicalSemiMap f).1.toOrderHom = f.1.toOrderHom := by
  simp [canonicalSemiMap, SimplexCategory.eqToHom_toOrderHom, Henry.SemiSimplexCategory.mk,
    SimplexCategory.len_mk]

private theorem sharpCanonicalMap_cancel {A B : Henry.SemiSimplexCategory}
    (f : B ⟶ A) :
    canonicalSemiMap f ≫ eqToHom (semiSimplex_mk_len A) =
      eqToHom (semiSimplex_mk_len B) ≫ f := by
  simp [canonicalSemiMap, Category.assoc]

private theorem sharpImageFaceInto_comp {n : ℕ} {A B : Henry.SemiSimplexCategory}
    (f : B ⟶ A) (v : Fin (n + 1) → Fin (B.obj.len + 1)) :
    sharpImageFaceInto (A := A)
        ((canonicalSemiMap f).1.toOrderHom ∘ v) =
      eqToHom (congrArg Henry.SemiSimplexCategory.mk
        (sharpImageSize_comp (canonicalSemiMap f) v)) ≫
        sharpImageFaceInto (A := B) v ≫ f := by
  rw [sharpImageFaceInto, sharpImageFaceInto]
  rw [sharpImageFace_comp (canonicalSemiMap f) v]
  simp only [Category.assoc]
  rw [sharpCanonicalMap_cancel]

private theorem sharpStageMap_comp {n : ℕ} {a b : SharpIndex n}
    (f : a ⟶ b) :
    sharpStageMap a =
      (canonicalSemiMap f.left.unop).1.toOrderHom ∘ sharpStageMap b := by
  have hw := congrArg Quiver.Hom.unop (CostructuredArrow.w f)
  rw [unop_comp] at hw
  have hmap : (Henry.SemiSimplexCategory.toFinFun.op.map f.left).unop =
      Henry.SemiSimplexCategory.toFinFun.map f.left.unop := by
    rfl
  rw [hmap] at hw
  have hpoint : ∀ i : Fin (n + 1),
      sharpStageMap a i = f.left.unop.1.toOrderHom (sharpStageMap b i) := by
    intro i
    have hi := (congrArg (fun g => g i) hw).symm
    change a.hom.unop i =
      f.left.unop.1.toOrderHom (b.hom.unop i) at hi
    simpa [sharpStageMap, Henry.SemiSimplexCategory.toFinFun] using hi
  funext i
  rw [canonicalSemiMap_toOrderHom]
  exact hpoint i

private noncomputable def sharpNormalizeStage {X : SemiSSet.{u}} {n : ℕ}
    (a : SharpIndex n) (x : (sharpDiagram X n).obj a) : SharpNormalForm X n := by
  let v := sharpStageMap a
  let r := sharpImageSize v
  let w := sharpImageFactor v
  let y := X.map (sharpImageFaceInto v).op x
  let p : SharpNormalData X n := (fun i => (w i).val, ⟨Henry.SemiSimplexCategory.mk r, y⟩)
  have hp : SharpNormalProperty X n r p := by
    refine ⟨fun i => (w i).isLt, ?_, rfl⟩
    intro j hj
    obtain ⟨i, hi⟩ := sharpImageFactor_surjective v ⟨j, hj⟩
    exact ⟨i, congrArg Fin.val hi⟩
  exact ⟨r, ⟨p, hp⟩⟩


private theorem sharpImageFaceInto_toOrderHom {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) :
    (sharpImageFaceInto (A := Henry.SemiSimplexCategory.mk m) v).1.toOrderHom =
      (sharpImageEmbedding v).toOrderHom := by
  change SimplexCategory.Hom.toOrderHom
      ((sharpImageFace v).1 ≫
        (eqToHom (semiSimplex_mk_len (Henry.SemiSimplexCategory.mk m))).1) = _
  rw [SimplexCategory.comp_toOrderHom, sharpImageFace_toOrderHom,
    sharpSemiEqToOrderHom]
  simp [Henry.SemiSimplexCategory.mk, SimplexCategory.len_mk, OrderHom.comp]
  all_goals rfl

private theorem sharpSimplexCode_eq_of_map {X : SemiSSet.{u}}
    {A B : Henry.SemiSimplexCategory} (h : A = B)
    (x : X.obj (op B)) (y : X.obj (op A))
    (hy : y = X.map (eqToHom h).op x) :
    (⟨A, y⟩ : SharpSimplexCode X) = ⟨B, x⟩ := by
  cases h
  simp at hy
  subst y
  rfl

private theorem sharpNormalizeStage_map {X : SemiSSet.{u}} {n : ℕ}
    {a b : SharpIndex n} (f : a ⟶ b) (x : (sharpDiagram X n).obj a) :
    sharpNormalizeStage b ((sharpDiagram X n).map f x) = sharpNormalizeStage a x := by
  change X.obj a.left at x
  let ι := canonicalSemiMap f.left.unop
  let v := sharpStageMap b
  have hv := sharpStageMap_comp f
  have hs : sharpImageSize (sharpStageMap a) = sharpImageSize v := by
    rw [hv]
    exact sharpImageSize_comp ι v
  let hobj := congrArg Henry.SemiSimplexCategory.mk hs
  let yA := X.map (sharpImageFaceInto (sharpStageMap a)).op x
  let yB := X.map (sharpImageFaceInto v).op (X.map f.left x)
  have hface1 := sharpImageFaceInto_congr hv
  have hface2 := sharpImageFaceInto_comp f.left.unop (sharpStageMap b)
  let h1 := congrArg Henry.SemiSimplexCategory.mk (congrArg sharpImageSize hv)
  let h2 := congrArg Henry.SemiSimplexCategory.mk (sharpImageSize_comp ι v)
  have hproof : h1.trans h2 = hobj := Subsingleton.elim _ _
  have hface : sharpImageFaceInto (sharpStageMap a) =
      eqToHom hobj ≫ sharpImageFaceInto v ≫ f.left.unop := by
    calc
      sharpImageFaceInto (sharpStageMap a) =
          eqToHom h1 ≫ sharpImageFaceInto
            ((canonicalSemiMap f.left.unop).1.toOrderHom ∘ v) := hface1
      _ = eqToHom h1 ≫
            (eqToHom h2 ≫ sharpImageFaceInto v ≫ f.left.unop) := by
              rw [hface2]
      _ = (eqToHom h1 ≫ eqToHom h2) ≫ sharpImageFaceInto v ≫ f.left.unop := by
            simp only [Category.assoc]
      _ = eqToHom (h1.trans h2) ≫ sharpImageFaceInto v ≫ f.left.unop := by
            rw [eqToHom_trans]
      _ = eqToHom hobj ≫ sharpImageFaceInto v ≫ f.left.unop := by rw [hproof]
  have hy : yA = X.map (eqToHom hobj).op yB := by
    dsimp [yA, yB]
    rw [hface]
    have hop : (eqToHom hobj ≫ sharpImageFaceInto v ≫ f.left.unop).op =
        f.left ≫ (sharpImageFaceInto v).op ≫ (eqToHom hobj).op := by
      simp only [op_comp, Quiver.Hom.op_unop]
      exact Category.assoc _ _ _
    rw [hop]
    simp [Functor.map_comp, ConcreteCategory.comp_apply, Category.assoc]
  have hcode :
      (⟨Henry.SemiSimplexCategory.mk (sharpImageSize (sharpStageMap a)), yA⟩ :
        SharpSimplexCode X) =
      ⟨Henry.SemiSimplexCategory.mk (sharpImageSize v), yB⟩ :=
    sharpSimplexCode_eq_of_map hobj yB yA hy
  have hdata :
      ((fun i => (sharpImageFactor v i).val),
        (⟨Henry.SemiSimplexCategory.mk (sharpImageSize v), yB⟩ : SharpSimplexCode X)) =
      ((fun i => (sharpImageFactor (sharpStageMap a) i).val),
        (⟨Henry.SemiSimplexCategory.mk (sharpImageSize (sharpStageMap a)), yA⟩ :
          SharpSimplexCode X)) := by
    apply Prod.ext
    · funext i
      have hfi1 := congrArg Fin.val (sharpImageFactor_congr hv i)
      have hfi2 := congrArg Fin.val (sharpImageFactor_comp_cast ι v i)
      simpa using hfi2.symm.trans hfi1.symm
    · exact hcode.symm
  dsimp [sharpNormalizeStage]
  apply Sigma.ext hs.symm
  have hp : ∀ p : SharpNormalData X n,
      SharpNormalProperty X n (sharpImageSize v) p ↔
      SharpNormalProperty X n (sharpImageSize (sharpStageMap a)) p := by
    intro p
    simp [SharpNormalProperty, hs]
  exact (Subtype.heq_iff_coe_eq hp).2 hdata



private noncomputable def sharpNormalCocone (X : SemiSSet.{u}) (n : ℕ) :
    Cocone (sharpDiagram X n) where
  pt := SharpNormalForm X n
  ι :=
    { app := fun a => ↾fun x => sharpNormalizeStage a x
      naturality := by
        intro a b f
        ext x
        exact sharpNormalizeStage_map f x }

private noncomputable def sharpNormalDesc (X : SemiSSet.{u}) (n : ℕ) :
    colimit (sharpDiagram X n) ⟶ SharpNormalForm X n :=
  colimit.desc (sharpDiagram X n) (sharpNormalCocone X n)

private theorem sharpNormalDesc_ι (X : SemiSSet.{u}) (n : ℕ)
    (a : SharpIndex n) (x : (sharpDiagram X n).obj a) :
    (sharpNormalDesc X n) (colimit.ι (sharpDiagram X n) a x) =
      sharpNormalizeStage a x := by
  simp [sharpNormalDesc, sharpNormalCocone]


private theorem sharpImage_eq_univ_of_surjective {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (hv : Function.Surjective v) :
    sharpImage v = Finset.univ := by
  ext j
  constructor
  · intro _
    simp
  · intro _
    obtain ⟨i, rfl⟩ := hv j
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private theorem sharpImageSize_eq_of_surjective {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (hv : Function.Surjective v) :
    sharpImageSize v = m := by
  unfold sharpImageSize
  rw [sharpImage_eq_univ_of_surjective v hv]
  simp

private theorem sharpImageEmbedding_eq_cast_of_surjective {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (hv : Function.Surjective v) :
    sharpImageEmbedding v =
      (Fin.castOrderIso (congrArg Nat.succ (sharpImageSize_eq_of_surjective v hv))).toOrderEmbedding := by
  let hs := sharpImageSize_eq_of_surjective v hv
  have hcard : (Finset.univ : Finset (Fin (m + 1))).card = sharpImageSize v + 1 := by
    simp [hs]
  have h₁ : sharpImageEmbedding v =
      Finset.univ.orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique'
    intro i
    simpa [sharpImage_eq_univ_of_surjective v hv] using
      (sharpImageOrderIso v i).property
  have h₂ : (Fin.castOrderIso (congrArg Nat.succ hs)).toOrderEmbedding =
      Finset.univ.orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique'
    intro i
    simp
  exact h₁.trans h₂.symm

private theorem sharpImageFaceInto_eqToHom_of_surjective {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (hv : Function.Surjective v) :
    sharpImageFaceInto (A := Henry.SemiSimplexCategory.mk m) v =
      eqToHom (congrArg Henry.SemiSimplexCategory.mk (sharpImageSize_eq_of_surjective v hv)) := by
  have hs := sharpImageSize_eq_of_surjective v hv
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext'
  rw [sharpImageFaceInto_toOrderHom, sharpSemiEqToOrderHom,
    sharpImageEmbedding_eq_cast_of_surjective v hv]
  exact hs


private noncomputable def sharpIndexOf {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) : SharpIndex n :=
  CostructuredArrow.mk
    (Quiver.Hom.op (show (⟨n⟩ : Henry.FinFun) ⟶
      Henry.SemiSimplexCategory.toFinFun.obj (Henry.SemiSimplexCategory.mk m) from v))


private theorem sharpStageMap_indexOf {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    sharpStageMap (sharpIndexOf v) = v := by
  rfl

private theorem sharpImageFactor_eq_cast_of_surjective {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (hv : Function.Surjective v)
    (i : Fin (n + 1)) :
    Fin.cast (congrArg Nat.succ (sharpImageSize_eq_of_surjective v hv))
      (sharpImageFactor v i) = v i := by
  have h := sharpImage_factor v i
  rw [sharpImageEmbedding_eq_cast_of_surjective v hv] at h
  simpa only [OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply] using h

private theorem sharpImageFactor_val_eq_of_surjective {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (hv : Function.Surjective v)
    (i : Fin (n + 1)) :
    (sharpImageFactor v i).val = (v i).val := by
  have h := sharpImageFactor_eq_cast_of_surjective v hv i
  simpa using congrArg Fin.val h

private theorem sharpNormalizeStage_code_of_surjective {X : SemiSSet.{u}}
    {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) (hv : Function.Surjective v)
    (x : X.obj (op (Henry.SemiSimplexCategory.mk m))) :
    (sharpNormalizeStage (sharpIndexOf v) x).2.1.2 =
      (⟨Henry.SemiSimplexCategory.mk m, x⟩ : SharpSimplexCode X) := by
  have hs := sharpImageSize_eq_of_surjective v hv
  have hobj := congrArg Henry.SemiSimplexCategory.mk hs
  have hy : X.map (sharpImageFaceInto v).op x = X.map (eqToHom hobj).op x := by
    rw [sharpImageFaceInto_eqToHom_of_surjective v hv]
  change (⟨Henry.SemiSimplexCategory.mk (sharpImageSize v),
      X.map (sharpImageFaceInto v).op x⟩ : SharpSimplexCode X) = _
  exact sharpSimplexCode_eq_of_map hobj x _ hy

private noncomputable def sharpColimitIso (X : SemiSSet.{u}) (n : ℕ) :
    (sharp X).obj (op (Henry.SemiSimplexCategory.mk n)) ≅ colimit (sharpDiagram X n) :=
  Henry.SemiSimplexCategory.toFinFun.op.leftKanExtensionObjIsoColimit X
    (op (⟨n⟩ : Henry.FinFun))

private theorem sharpMk_colimit_ι {X : SemiSSet.{u}} {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (x : X.obj (op (Henry.SemiSimplexCategory.mk m))) :
    (sharpColimitIso X n).hom (sharpMk v x) =
      colimit.ι (sharpDiagram X n) (sharpIndexOf v) x := by
  let L := Henry.SemiSimplexCategory.toFinFun.op
  let T := op (⟨n⟩ : Henry.FinFun)
  let idx := sharpIndexOf v
  change ((L.leftKanExtensionUnit X).app idx.left ≫
      (L.leftKanExtension X).map idx.hom ≫
      (L.leftKanExtensionObjIsoColimit X T).hom) x =
    colimit.ι (CostructuredArrow.proj L T ⋙ X) idx x
  exact congrArg (fun g => g x)
    (Functor.ι_leftKanExtensionObjIsoColimit_hom (L := L) (F := X) T idx)


/-- Every formal degeneracy has a representative with surjective vertex map. -/
theorem sharp_exists_normalForm_proof {X : SemiSSet.{u}} {n : ℕ}
    (e : (sharp X).obj (op (Henry.SemiSimplexCategory.mk n))) :
    ∃ (m : ℕ) (v : Fin (n + 1) → Fin (m + 1))
      (x : X.obj (op (Henry.SemiSimplexCategory.mk m))),
      Function.Surjective v ∧ sharpMk v x = e := by
  let F := sharpDiagram X n
  let iso := sharpColimitIso X n
  obtain ⟨a, z, hz⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit F) (iso.hom e)
  let w := sharpStageMap a
  let m := sharpImageSize w
  let v := sharpImageFactor w
  let y := X.map (sharpImageFaceInto w).op z
  have hv := sharpImageFactor_surjective w
  let idx := sharpIndexOf v
  have htriangle :
      Henry.SemiSimplexCategory.toFinFun.op.map (sharpImageFaceInto w).op ≫ idx.hom = a.hom := by
    apply Quiver.Hom.unop_inj
    change (fun i => (sharpImageFaceInto w).1.toOrderHom
        (sharpImageFactor w i)) = fun i => a.hom.unop i
    funext i
    exact congrFun (sharpImageFaceInto_factor w) i
  let g : a ⟶ idx := CostructuredArrow.homMk (sharpImageFaceInto w).op htriangle
  have hgy : F.map g z = y := by
    change X.map g.left z = X.map (sharpImageFaceInto w).op z
    rfl
  have hcol : colimit.ι F idx y = colimit.ι F a z := by
    calc
      colimit.ι F idx y = colimit.ι F idx (F.map g z) := by rw [hgy]
      _ = colimit.ι F a z := by
        exact congrArg (fun q => q z) (colimit.w F g)
  have hcanon :
      (iso.hom (sharpMk v y)) = colimit.ι F idx y := by
    simpa [F, iso, idx, v, y] using sharpMk_colimit_ι v y
  have htarget : iso.hom (sharpMk v y) = iso.hom e := by
    calc
      iso.hom (sharpMk v y) = colimit.ι F idx y := hcanon
      _ = colimit.ι F a z := hcol
      _ = iso.hom e := hz
  have hrep : sharpMk v y = e := by
    have h := congrArg iso.inv htarget
    simpa [iso] using h
  exact ⟨m, v, y, hv, hrep⟩


/-- A surjective vertex map gives the unique nondegenerate representative. -/
theorem sharp_normalForm_unique_proof {X : SemiSSet.{u}} {n m m' : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (v' : Fin (n + 1) → Fin (m' + 1))
    (x : X.obj (op (Henry.SemiSimplexCategory.mk m)))
    (x' : X.obj (op (Henry.SemiSimplexCategory.mk m')))
    (hv : Function.Surjective v) (hv' : Function.Surjective v')
    (h : sharpMk v x = sharpMk v' x') : m = m' ∧ HEq v v' ∧ HEq x x' := by
  let F := sharpDiagram X n
  let iso := sharpColimitIso X n
  let xv : F.obj (sharpIndexOf v) := x
  let xv' : F.obj (sharpIndexOf v') := x'
  have hcol : colimit.ι F (sharpIndexOf v) xv = colimit.ι F (sharpIndexOf v') xv' := by
    calc
      colimit.ι F (sharpIndexOf v) xv = iso.hom (sharpMk v x) := by
        simpa [xv] using (sharpMk_colimit_ι v x).symm
      _ = iso.hom (sharpMk v' x') := congrArg iso.hom h
      _ = colimit.ι F (sharpIndexOf v') xv' := by
        simpa [xv'] using sharpMk_colimit_ι v' x'
  have hnf := congrArg (sharpNormalDesc X n) hcol
  have hnf' : sharpNormalizeStage (sharpIndexOf v) x =
      sharpNormalizeStage (sharpIndexOf v') x' := by
    change (sharpNormalDesc X n)
        (colimit.ι (sharpDiagram X n) (sharpIndexOf v) xv) =
      (sharpNormalDesc X n)
        (colimit.ι (sharpDiagram X n) (sharpIndexOf v') xv') at hnf
    rw [sharpNormalDesc_ι, sharpNormalDesc_ι] at hnf
    simpa [xv, xv'] using hnf
  have hdata := congrArg (fun q : SharpNormalForm X n => q.2.1) hnf'
  dsimp [sharpNormalizeStage] at hdata
  rw [sharpStageMap_indexOf, sharpStageMap_indexOf] at hdata
  have hfun : (fun i => (sharpImageFactor v i).val) =
      (fun i => (sharpImageFactor v' i).val) := congrArg Prod.fst hdata
  have hcode := congrArg Prod.snd hdata
  have hcode' : (⟨Henry.SemiSimplexCategory.mk m, x⟩ : SharpSimplexCode X) =
      ⟨Henry.SemiSimplexCategory.mk m', x'⟩ := by
    calc
      (⟨Henry.SemiSimplexCategory.mk m, x⟩ : SharpSimplexCode X) =
          (sharpNormalizeStage (sharpIndexOf v) x).2.1.2 :=
        (sharpNormalizeStage_code_of_surjective v hv x).symm
      _ = (sharpNormalizeStage (sharpIndexOf v') x').2.1.2 := hcode
      _ = ⟨Henry.SemiSimplexCategory.mk m', x'⟩ :=
        sharpNormalizeStage_code_of_surjective v' hv' x'
  have hm : m = m' := by
    have hobj := congrArg (fun c : SharpSimplexCode X => c.1) hcode'
    simpa [Henry.SemiSimplexCategory.mk, SimplexCategory.len_mk] using
      congrArg (fun A : Henry.SemiSimplexCategory => A.obj.len) hobj
  have hval : ∀ i, (v i).val = (v' i).val := by
    intro i
    calc
      (v i).val = (sharpImageFactor v i).val :=
        (sharpImageFactor_val_eq_of_surjective v hv i).symm
      _ = (sharpImageFactor v' i).val := congrFun hfun i
      _ = (v' i).val := sharpImageFactor_val_eq_of_surjective v' hv' i
  have hvEq : HEq v v' := by
    cases hm
    apply heq_of_eq
    funext i
    apply Fin.ext
    exact hval i
  exact ⟨hm, hvEq, (Sigma.mk.inj_iff.mp hcode').2⟩

#print axioms HomotopyHypothesis.Simplicial.SharpNormalForms.sharp_exists_normalForm_proof
#print axioms HomotopyHypothesis.Simplicial.SharpNormalForms.sharp_normalForm_unique_proof

end HomotopyHypothesis.Simplicial.SharpNormalForms
