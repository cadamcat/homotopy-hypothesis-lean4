import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.PointStructure.Core
universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Realization.PointStructure

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

theorem stdSimplex_support_map {α β : Type u} [DecidableEq β]
    (p : Convexity.StdSimplex ℝ α) (f : α → β) :
    (p.map f).weights.support = p.weights.support.image f := by
  change (p.weights.mapDomain f).support = _
  exact Finsupp.support_mapDomain_of_nonneg p.nonneg f

theorem stdSimplex_support_map_card_of_injective {α β : Type u} [DecidableEq β]
    (p : Convexity.StdSimplex ℝ α) (f : α → β) (hf : Function.Injective f) :
    (p.map f).weights.support.card = p.weights.support.card := by
  rw [stdSimplex_support_map, Finset.card_image_of_injective _ hf]

private def pointSupport {n : ℕ} (p : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Finset (Fin (n + 1)) := p.weights.support

private theorem pointSupport_card_pos {n : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1))) : 0 < (pointSupport p).card := by
  apply Finset.card_pos.mpr
  exact p.support_weights_nonempty

private def pointSupportSize {n : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1))) : ℕ := (pointSupport p).card - 1

private theorem pointSupport_card_eq {n : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (pointSupport p).card = pointSupportSize p + 1 :=
  (Nat.sub_add_cancel (pointSupport_card_pos p)).symm

private noncomputable def pointSupportOrderIso {n : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Fin (pointSupportSize p + 1) ≃o pointSupport p :=
  (pointSupport p).orderIsoOfFin (pointSupport_card_eq p)

private noncomputable def pointSupportEmbedding {n : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Fin (pointSupportSize p + 1) ↪o Fin (n + 1) :=
  (pointSupportOrderIso p).toOrderEmbedding.trans (OrderEmbedding.subtype _)

private noncomputable def pointSupportFace {a : Henry.SemiSimplexCategory}
    (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1))) :
    Henry.SemiSimplexCategory.mk (pointSupportSize p) ⟶ a := by
  let f : SimplexCategory.mk (pointSupportSize p) ⟶ a.1 :=
    SimplexCategory.Hom.mk (pointSupportEmbedding p)
  have hf : Mono f := by
    rw [SimplexCategory.mono_iff_injective]
    exact (pointSupportEmbedding p).injective
  exact ⟨f, hf⟩

private noncomputable def pointSupportCell {X : Henry.SemiSSet.{u}}
    {a : Henry.SemiSimplexCategory} (x : X.obj (op a))
    (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1))) :
    X.obj (op (Henry.SemiSimplexCategory.mk (pointSupportSize p))) :=
  X.map (pointSupportFace p).op x

private noncomputable def semiSimplexOrderEmbedding {a b : Henry.SemiSimplexCategory}
    (ι : a ⟶ b) : Fin (a.obj.len + 1) ↪o Fin (b.obj.len + 1) :=
  OrderEmbedding.ofStrictMono ι.1.toOrderHom
    (ι.1.toOrderHom.monotone.strictMono_of_injective (by
      rw [← SimplexCategory.mono_iff_injective]
      exact ι.2))

private theorem pointSupportSize_map {a b : Henry.SemiSimplexCategory}
    (ι : a ⟶ b) (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1))) :
    pointSupportSize (p.map ι.1.toOrderHom) = pointSupportSize p := by
  have hi : Function.Injective ι.1.toOrderHom := by
    rw [← SimplexCategory.mono_iff_injective]
    exact ι.2
  unfold pointSupportSize pointSupport
  rw [stdSimplex_support_map, Finset.card_image_of_injective _ hi]

private theorem pointSupportEmbedding_map {a b : Henry.SemiSimplexCategory}
    (ι : a ⟶ b) (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1)))
    (j : Fin (pointSupportSize (p.map ι.1.toOrderHom) + 1)) :
    pointSupportEmbedding (p.map ι.1.toOrderHom) j =
      ι.1.toOrderHom (pointSupportEmbedding p
        (Fin.cast (congrArg Nat.succ (pointSupportSize_map ι p)) j)) := by
  let h := pointSupportSize_map ι p
  let c : Fin (pointSupportSize (p.map ι.1.toOrderHom) + 1) ↪o
      Fin (pointSupportSize p + 1) :=
    (Fin.castOrderIso (congrArg Nat.succ h)).toOrderEmbedding
  let candidate : Fin (pointSupportSize (p.map ι.1.toOrderHom) + 1) ↪o
      Fin (b.obj.len + 1) :=
    c.trans ((pointSupportEmbedding p).trans (semiSimplexOrderEmbedding ι))
  have hcand (j : Fin (pointSupportSize (p.map ι.1.toOrderHom) + 1)) :
      candidate j = ι.1.toOrderHom (pointSupportEmbedding p
        (Fin.cast (congrArg Nat.succ h) j)) := by
    simp [candidate, c, semiSimplexOrderEmbedding]
  have hmem : ∀ j, candidate j ∈ pointSupport (p.map ι.1.toOrderHom) := by
    intro j
    change candidate j ∈ (p.map ι.1.toOrderHom).weights.support
    rw [stdSimplex_support_map]
    refine Finset.mem_image.mpr ⟨pointSupportEmbedding p
      (Fin.cast (congrArg Nat.succ h) j), ?_, hcand j⟩
    exact (pointSupportOrderIso p _).property
  have hu := Finset.orderEmbOfFin_unique'
    (pointSupport_card_eq (p.map ι.1.toOrderHom)) hmem
  have hu' : candidate = pointSupportEmbedding (p.map ι.1.toOrderHom) := by
    change candidate =
      (pointSupport (p.map ι.1.toOrderHom)).orderEmbOfFin
        (pointSupport_card_eq (p.map ι.1.toOrderHom))
    exact hu
  calc
    pointSupportEmbedding (p.map ι.1.toOrderHom) j = candidate j := by
      exact congrArg (fun e : Fin (pointSupportSize (p.map ι.1.toOrderHom) + 1) ↪o
        Fin (b.obj.len + 1) => e j) hu'.symm
    _ = ι.1.toOrderHom (pointSupportEmbedding p
          (Fin.cast (congrArg Nat.succ h) j)) := hcand j

private theorem semiSimplexEqToFun {r s : ℕ} (h : r = s) :
    (eqToHom (congrArg Henry.SemiSimplexCategory.mk h)).1.toOrderHom =
      (Fin.cast (congrArg Nat.succ h) : Fin (r + 1) → Fin (s + 1)) := by
  cases h
  rfl

private theorem pointSupportFace_toOrderHom {a : Henry.SemiSimplexCategory}
    (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1))) :
    (pointSupportFace p).1.toOrderHom = (pointSupportEmbedding p).toOrderHom := rfl

private theorem pointSupportFace_comp {a b : Henry.SemiSimplexCategory}
    (ι : a ⟶ b) (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1))) :
    pointSupportFace (p.map ι.1.toOrderHom) =
      eqToHom (congrArg Henry.SemiSimplexCategory.mk (pointSupportSize_map ι p)) ≫
        pointSupportFace p ≫ ι := by
  have hs := pointSupportSize_map ι p
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext j
  rw [pointSupportFace_toOrderHom, OrderEmbedding.toOrderHom_coe,
    pointSupportEmbedding_map, WideSubcategory.comp_def, WideSubcategory.comp_def,
    SimplexCategory.comp_toOrderHom, SimplexCategory.comp_toOrderHom]
  dsimp [OrderHom.comp]
  rw [semiSimplexEqToFun]
  change ι.1.toOrderHom (pointSupportEmbedding p
      (Fin.cast (congrArg Nat.succ hs) j)) =
    ι.1.toOrderHom (pointSupportEmbedding p
      ((Fin.castOrderIso (congrArg Nat.succ hs)).toOrderEmbedding j))
  congr 1
  exact hs

private noncomputable def pointSupportElement {X : Henry.SemiSSet.{u}}
    {a : Henry.SemiSimplexCategory} (x : X.obj (op a))
    (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1))) : X.Elements :=
  Functor.elementsMk X (op (Henry.SemiSimplexCategory.mk (pointSupportSize p)))
    (pointSupportCell x p)

private theorem pointSupportElement_map {X : Henry.SemiSSet.{u}}
    {a b : Henry.SemiSimplexCategory} (ι : a ⟶ b)
    (x : X.obj (op b)) (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1))) :
    pointSupportElement (X.map ι.op x) p =
      pointSupportElement x (p.map ι.1.toOrderHom) := by
  let hs := pointSupportSize_map ι p
  let hobj := congrArg op (congrArg Henry.SemiSimplexCategory.mk hs).symm
  have hface := congrArg Quiver.Hom.op (pointSupportFace_comp ι p)
  simp only [op_comp, eqToHom_op] at hface
  have hmap := congrArg (fun f => X.map f) hface.symm
  have hassoc : (ι.op ≫ (pointSupportFace p).op) ≫ eqToHom hobj =
      ι.op ≫ (pointSupportFace p).op ≫ eqToHom hobj := Category.assoc _ _ _
  have hmapAssoc := congrArg (fun f => X.map f) hassoc
  have hmap' := hmapAssoc.symm.trans hmap
  refine Functor.Elements.ext _ _ hobj ?_
  change X.map (eqToHom hobj) (X.map (pointSupportFace p).op (X.map ι.op x)) =
    X.map (pointSupportFace (p.map ι.1.toOrderHom)).op x
  calc
    _ = X.map (ι.op ≫ (pointSupportFace p).op ≫ eqToHom hobj) x := by
      calc
        _ = ((X.map ι.op ≫ X.map (pointSupportFace p).op) ≫
            X.map (eqToHom hobj)) x := by simp only [ConcreteCategory.comp_apply]
        _ = (X.map (ι.op ≫ (pointSupportFace p).op) ≫
            X.map (eqToHom hobj)) x := by
          exact congrArg (fun f => (f ≫ X.map (eqToHom hobj)) x)
            (X.map_comp ι.op (pointSupportFace p).op).symm
        _ = X.map ((ι.op ≫ (pointSupportFace p).op) ≫ eqToHom hobj) x := by
          exact congrArg (fun f => f x)
            (X.map_comp (ι.op ≫ (pointSupportFace p).op) (eqToHom hobj)).symm
        _ = X.map (ι.op ≫ (pointSupportFace p).op ≫ eqToHom hobj) x := by
          exact congrArg (fun f => X.map f x) (Category.assoc _ _ _)
    _ = X.map (pointSupportFace (p.map ι.1.toOrderHom)).op x := by
      exact ConcreteCategory.congr_hom hmap' x

private theorem pointSupportCell_heq {X : Henry.SemiSSet.{u}}
    {a b : Henry.SemiSimplexCategory}
    (x : X.obj (op a)) (y : X.obj (op b))
    (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1)))
    (q : Convexity.StdSimplex ℝ (Fin (b.obj.len + 1)))
    (h : pointSupportElement x p = pointSupportElement y q) :
    HEq (pointSupportCell x p) (pointSupportCell y q) := by
  change HEq (pointSupportElement x p).val (pointSupportElement y q).val
  let toSigma : X.Elements → Σ a : Henry.SemiSimplexCategoryᵒᵖ, X.obj a :=
    fun e => ⟨e.obj, e.val⟩
  have hs := congrArg toSigma h
  exact (Sigma.mk.inj_iff.mp hs).2

private theorem pointSupportSize_eq_of_element_eq {X : Henry.SemiSSet.{u}}
    {a b : Henry.SemiSimplexCategory}
    (x : X.obj (op a)) (y : X.obj (op b))
    (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1)))
    (q : Convexity.StdSimplex ℝ (Fin (b.obj.len + 1)))
    (h : pointSupportElement x p = pointSupportElement y q) :
    pointSupportSize p = pointSupportSize q := by
  have hlen := congrArg (fun e : X.Elements => e.obj.unop.obj.len) h
  simpa [pointSupportElement] using hlen

private theorem pointSupport_map_eq_image {a b : Henry.SemiSimplexCategory}
    (ι : a ⟶ b) (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1))) :
    pointSupport (p.map ι.1.toOrderHom) =
      (pointSupport p).image ι.1.toOrderHom := by
  unfold pointSupport
  exact stdSimplex_support_map p ι.1.toOrderHom

private def pointSupportRank {n : ℕ} (p : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) : ℕ :=
  (pointSupport p).filter (fun j => j < i) |>.card

private theorem pointSupportRank_eq_orderIso_inv_val {n : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1)))
    {i : Fin (n + 1)} (hi : i ∈ pointSupport p) :
    pointSupportRank p i = ((pointSupportOrderIso p).symm ⟨i, hi⟩).val := by
  let j := (pointSupportOrderIso p).symm ⟨i, hi⟩
  have hji : pointSupportEmbedding p j = i := by
    simp [j, pointSupportEmbedding]
  have hfilter :
      (Finset.Iio j).map (pointSupportEmbedding p).toEmbedding =
        (pointSupport p).filter (fun k => k < i) := by
    ext k
    simp only [Finset.mem_map, Finset.mem_Iio, Finset.mem_filter]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(pointSupportOrderIso p r).property, by
        rw [← hji]
        exact (pointSupportEmbedding p).strictMono hr⟩
    · rintro ⟨hk, hki⟩
      let r := (pointSupportOrderIso p).symm ⟨k, hk⟩
      refine ⟨r, ?_, ?_⟩
      · have hki' : (⟨k, hk⟩ : pointSupport p) < ⟨i, hi⟩ := hki
        exact (pointSupportOrderIso p).symm.strictMono hki'
      · simp [r, pointSupportEmbedding]
  have hcard := congrArg Finset.card hfilter
  rw [Finset.card_map, Fin.card_Iio] at hcard
  simpa [pointSupportRank, j] using hcard.symm

private noncomputable def pointSupportCoordinates {n : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1))) : ℕ →₀ ℝ :=
  p.weights.mapDomain (pointSupportRank p)

private theorem pointSupportRank_map {a b : Henry.SemiSimplexCategory}
    (ι : a ⟶ b) (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1)))
    (i : Fin (a.obj.len + 1)) :
    pointSupportRank (p.map ι.1.toOrderHom) (ι.1.toOrderHom i) =
      pointSupportRank p i := by
  let f := ι.1.toOrderHom
  have hf : Function.Injective f := by
    rw [← SimplexCategory.mono_iff_injective]
    exact ι.2
  have hstrict : StrictMono f := (semiSimplexOrderEmbedding ι).strictMono
  have hsupport : pointSupport (p.map f) = (pointSupport p).image f := by
    unfold pointSupport
    exact stdSimplex_support_map p f
  have hfilter :
      ((pointSupport p).filter (fun j => j < i)).image f =
        (pointSupport (p.map f)).filter (fun j => j < f i) := by
    rw [pointSupport_map_eq_image]
    ext y
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨j, ⟨hj, hji⟩, rfl⟩
      exact ⟨⟨j, hj, rfl⟩, hstrict hji⟩
    · rintro ⟨⟨j, hj, rfl⟩, hy⟩
      exact ⟨j, ⟨hj, hstrict.lt_iff_lt.mp hy⟩, rfl⟩
  have hfilter' :
      ((pointSupport p).filter (fun j => j < i)).image f =
        ((pointSupport p).image f).filter (fun j => j < f i) := by
    simpa only [hsupport] using hfilter
  unfold pointSupportRank
  rw [hsupport, ← hfilter', Finset.card_image_of_injective _ hf]

private theorem pointSupportCoordinates_map {a b : Henry.SemiSimplexCategory}
    (ι : a ⟶ b) (p : Convexity.StdSimplex ℝ (Fin (a.obj.len + 1))) :
    pointSupportCoordinates (p.map ι.1.toOrderHom) = pointSupportCoordinates p := by
  change (p.weights.mapDomain ι.1.toOrderHom).mapDomain
      (pointSupportRank (p.map ι.1.toOrderHom)) =
    p.weights.mapDomain (pointSupportRank p)
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro i _
  exact pointSupportRank_map ι p i

private theorem pointSupport_barycenter {n : ℕ} :
    pointSupport (Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))) =
      Finset.univ := by
  classical
  ext i
  simp only [pointSupport, Finset.mem_univ, iff_true, Finsupp.mem_support_iff]
  rw [Convexity.StdSimplex.weights_barycenter_apply]
  positivity

private theorem pointSupport_map_eq_image_of_full {n m : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hp : pointSupport p = Finset.univ) (v : Fin (n + 1) → Fin (m + 1)) :
    pointSupport (p.map v) = Finset.univ.image v := by
  unfold pointSupport at hp ⊢
  rw [stdSimplex_support_map, hp]

private theorem pointSupportRank_lt_card {n : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1)))
    {i : Fin (n + 1)} (hi : i ∈ pointSupport p) :
    pointSupportRank p i < (pointSupport p).card := by
  have hproper : (pointSupport p).filter (fun j => j < i) ⊂ pointSupport p := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hmem : i ∈ (pointSupport p).filter (fun j => j < i) := by
      simpa [heq] using hi
    exact (lt_irrefl i) (Finset.mem_filter.mp hmem).2
  exact Finset.card_lt_card hproper

private theorem pointSupportRank_lt_size {n : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1)))
    {i : Fin (n + 1)} (hi : i ∈ pointSupport p) :
    pointSupportRank p i < pointSupportSize p + 1 := by
  have hlt := pointSupportRank_lt_card p hi
  rw [← pointSupport_card_eq p]
  exact hlt

private theorem pointSupport_barycenter_map_vertex_mem {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (i : Fin (n + 1)) :
    v i ∈ pointSupport
      ((Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).map v) := by
  rw [pointSupport_map_eq_image_of_full _ pointSupport_barycenter v]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private noncomputable def pointSupportFactor {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) :
    Fin (n + 1) → Fin (pointSupportSize
      ((Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).map v) + 1) :=
  fun i => ⟨pointSupportRank
      ((Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).map v) (v i),
    pointSupportRank_lt_size _ (pointSupport_barycenter_map_vertex_mem v i)⟩

private theorem pointSupportFactor_surjective {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) :
    Function.Surjective (pointSupportFactor v) := by
  let p := (Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).map v
  have hS : pointSupport p = Finset.univ.image v :=
    pointSupport_map_eq_image_of_full _ pointSupport_barycenter v
  intro j
  have hj : (pointSupportOrderIso p j).val ∈ Finset.univ.image v := by
    rw [← hS]
    exact (pointSupportOrderIso p j).property
  obtain ⟨i, -, hvi⟩ := Finset.mem_image.mp hj
  have hmem := pointSupport_barycenter_map_vertex_mem v i
  refine ⟨i, ?_⟩
  apply Fin.ext
  change pointSupportRank p (v i) = j.val
  rw [pointSupportRank_eq_orderIso_inv_val p hmem]
  have hsub : (⟨v i, hmem⟩ : pointSupport p) = pointSupportOrderIso p j := by
    apply Subtype.ext
    exact hvi
  simpa using congrArg (fun z : pointSupport p => ((pointSupportOrderIso p).symm z).val) hsub

private theorem pointSupportEmbedding_factor {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (i : Fin (n + 1)) :
    pointSupportEmbedding
      ((Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).map v)
      (pointSupportFactor v i) = v i := by
  let p := (Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).map v
  have hmem := pointSupport_barycenter_map_vertex_mem v i
  have hfactor : pointSupportFactor v i =
      (pointSupportOrderIso p).symm ⟨v i, hmem⟩ := by
    apply Fin.ext
    exact pointSupportRank_eq_orderIso_inv_val p hmem
  rw [hfactor]
  change ((pointSupportOrderIso p).toOrderEmbedding.trans (OrderEmbedding.subtype _))
      ((pointSupportOrderIso p).symm ⟨v i, hmem⟩) = v i
  simp

private theorem sharpMk_eq_supportFactor {X : Henry.SemiSSet.{u}} {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ X) :
    Henry.SemiSSet.sharpMk v (uliftYonedaEquiv x) =
      Henry.SemiSSet.sharpMk (pointSupportFactor v)
        (pointSupportCell (uliftYonedaEquiv x)
          ((Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).map v)) := by
  let p := (Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).map v
  let ι := pointSupportFace (a := Henry.SemiSimplexCategory.mk m) p
  have hcomp : ι.1.toOrderHom ∘ pointSupportFactor v = v := by
    funext i
    change pointSupportEmbedding p (pointSupportFactor v i) = v i
    exact pointSupportEmbedding_factor v i
  calc
    Henry.SemiSSet.sharpMk v (uliftYonedaEquiv x) =
        Henry.SemiSSet.sharpMk (ι.1.toOrderHom ∘ pointSupportFactor v)
          (uliftYonedaEquiv x) := by
      exact congrArg (fun w => Henry.SemiSSet.sharpMk w (uliftYonedaEquiv x)) hcomp.symm
    _ = Henry.SemiSSet.sharpMk (pointSupportFactor v)
          (X.map ι.op (uliftYonedaEquiv x)) :=
      sharp_mk_face ι (pointSupportFactor v) (uliftYonedaEquiv x)
    _ = Henry.SemiSSet.sharpMk (pointSupportFactor v)
          (pointSupportCell (uliftYonedaEquiv x) p) := rfl

private theorem pointSupportRank_eq_of_support_eq {n : ℕ}
    (p q : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (h : pointSupport p = pointSupport q) :
    pointSupportRank p = pointSupportRank q := by
  funext i
  simp only [pointSupportRank, h]

private theorem sharpMk_eq_of_heq_supportData {X : Henry.SemiSSet.{u}}
    {n k k' : ℕ}
    (v : Fin (n + 1) → Fin (k + 1))
    (v' : Fin (n + 1) → Fin (k' + 1))
    (x : X.obj (op (Henry.SemiSimplexCategory.mk k)))
    (x' : X.obj (op (Henry.SemiSimplexCategory.mk k')))
    (hk : k = k')
    (hv : ∀ i, (v i).val = (v' i).val)
    (hx : HEq x x') :
    Henry.SemiSSet.sharpMk v x = Henry.SemiSSet.sharpMk v' x' := by
  cases hk
  have hv' : v = v' := by
    funext i
    exact Fin.ext (hv i)
  cases hv'
  have hx' : x = x' := eq_of_heq hx
  cases hx'
  rfl

private noncomputable def supportProbe {n : ℕ} (i : Fin (n + 1)) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) :=
  Convexity.convexCombPair (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)
    (by norm_num) (Convexity.StdSimplex.single i)
      (Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1)))

private theorem supportProbe_weights {n : ℕ} (i : Fin (n + 1)) :
    (supportProbe i).weights =
      (1 / 2 : ℝ) • (Convexity.StdSimplex.single i).weights +
        (1 / 2 : ℝ) •
          (Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).weights := by
  simp [supportProbe]

private theorem pointSupport_supportProbe {n : ℕ} (i : Fin (n + 1)) :
    pointSupport (supportProbe i) = Finset.univ := by
  classical
  ext j
  simp only [pointSupport, Finset.mem_univ, iff_true, Finsupp.mem_support_iff]
  rw [supportProbe_weights]
  by_cases hji : j = i
  · subst j
    simp [Finsupp.add_apply, Finsupp.smul_apply,
      Convexity.StdSimplex.weights_single, Convexity.StdSimplex.weights_barycenter_apply]
    positivity
  · simp [Finsupp.add_apply, Finsupp.smul_apply, hji,
      Convexity.StdSimplex.weights_single, Convexity.StdSimplex.weights_barycenter_apply]
    positivity

private theorem pointSupportRank_eq_val_of_univ {n : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (hp : pointSupport p = Finset.univ) (i : Fin (n + 1)) :
    pointSupportRank p i = i.val := by
  unfold pointSupportRank
  rw [hp]
  have hs : (Finset.univ : Finset (Fin (n + 1))).filter (fun j => j < i) = Finset.Iio i := by
    ext j
    simp
  rw [hs]
  exact Fin.card_Iio i

private theorem pointSupport_map_surjective {n m : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (v : Fin (n + 1) → Fin (m + 1)) (hp : pointSupport p = Finset.univ)
    (hv : Function.Surjective v) : pointSupport (p.map v) = Finset.univ := by
  have hs : pointSupport (p.map v) = (pointSupport p).image v := by
    unfold pointSupport
    exact stdSimplex_support_map p v
  rw [hs, hp, Finset.image_univ_of_surjective hv]

private theorem pointSupportCoordinates_mapVertex {n m : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1))) (v : Fin (n + 1) → Fin (m + 1)) :
    pointSupportCoordinates (p.map v) =
      p.weights.mapDomain (fun i => pointSupportRank (p.map v) (v i)) := by
  change (p.weights.mapDomain v).mapDomain (pointSupportRank (p.map v)) = _
  rw [← Finsupp.mapDomain_comp]
  rfl

private theorem pointSupportCoordinates_mapVertex_of_surjective {n m : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 1))) (v : Fin (n + 1) → Fin (m + 1))
    (hp : pointSupport p = Finset.univ) (hv : Function.Surjective v) :
    pointSupportCoordinates (p.map v) = p.weights.mapDomain (fun i => (v i).val) := by
  rw [pointSupportCoordinates_mapVertex]
  have hfull := pointSupport_map_surjective p v hp hv
  congr 1
  funext i
  exact pointSupportRank_eq_val_of_univ (p.map v) hfull (v i)

private theorem function_eq_of_barycenter_probes {n : ℕ}
    (f g : Fin (n + 1) → ℕ)
    (hbase : ((Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).weights).mapDomain f =
      ((Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))).weights).mapDomain g)
    (hprobe : ∀ i, (supportProbe i).weights.mapDomain f =
      (supportProbe i).weights.mapDomain g) : f = g := by
  funext i
  by_contra hne
  have hp := hprobe i
  simp only [supportProbe_weights, Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    Finsupp.mapDomain_single, Convexity.StdSimplex.weights_single] at hp
  rw [hbase] at hp
  have hs : (1 / 2 : ℝ) • Finsupp.single (f i) (1 : ℝ) =
      (1 / 2 : ℝ) • Finsupp.single (g i) (1 : ℝ) := add_right_cancel hp
  have hv := congrArg (fun z : ℕ →₀ ℝ => z (f i)) hs
  have hne' : g i ≠ f i := Ne.symm hne
  simp [hne'] at hv

private noncomputable def diagramSupportLabel (X : Henry.SemiSSet.{u})
    (j : X.Elementsᵒᵖ) :
    (realizationElementsDiagram X ⋙ (forget TopCat)).obj j → X.Elements :=
  fun p => pointSupportElement j.unop.val (ULift.down p)

private noncomputable def supportCellCocone (X : Henry.SemiSSet.{u}) :
    Cocone (realizationElementsDiagram X ⋙ (forget TopCat)) where
  pt := X.Elements
  ι :=
    { app := fun j => ↾(diagramSupportLabel X j)
      naturality := by
        intro j j' f
        ext p
        let e := j.unop
        let e' := j'.unop
        let ι : e.obj.unop ⟶ e'.obj.unop := f.unop.hom.unop
        have hx : X.map ι.op e'.val = e.val := by
          change X.map f.unop.hom e'.val = e.val
          exact f.unop.map_val
        have hp :
            ULift.down ((realizationElementsDiagram X ⋙ (forget TopCat)).map f p) =
              (ULift.down p).map ι.1.toOrderHom := by
          simp [realizationElementsDiagram, Functor.comp_map, ι]
          rfl
        change pointSupportElement e'.val
            (ULift.down ((realizationElementsDiagram X ⋙ (forget TopCat)).map f p)) =
          pointSupportElement e.val (ULift.down p)
        rw [hp, ← hx]
        exact (pointSupportElement_map ι e'.val (ULift.down p)).symm }

theorem supportElement_eq_of_colimit_eq {X : Henry.SemiSSet.{u}}
    {j j' : X.Elementsᵒᵖ}
    {p : (realizationElementsDiagram X ⋙ (forget TopCat)).obj j}
    {p' : (realizationElementsDiagram X ⋙ (forget TopCat)).obj j'}
    (h : colimit.ι (realizationElementsDiagram X ⋙ (forget TopCat)) j p =
      colimit.ι (realizationElementsDiagram X ⋙ (forget TopCat)) j' p') :
    pointSupportElement j.unop.val (ULift.down p) =
      pointSupportElement j'.unop.val (ULift.down p') := by
  let C := supportCellCocone X
  have hfac (k : X.Elementsᵒᵖ)
      (q : (realizationElementsDiagram X ⋙ (forget TopCat)).obj k) :
      (ConcreteCategory.hom
        (colimit.desc (realizationElementsDiagram X ⋙ (forget TopCat)) C))
          ((ConcreteCategory.hom
            (colimit.ι (realizationElementsDiagram X ⋙ (forget TopCat)) k)) q) =
        (ConcreteCategory.hom (C.ι.app k)) q :=
    ConcreteCategory.congr_hom (colimit.ι_desc C k) q
  have h' := congrArg (fun z =>
      (ConcreteCategory.hom (colimit.desc (realizationElementsDiagram X ⋙ (forget TopCat)) C)) z) h
  change (ConcreteCategory.hom (C.ι.app j)) p =
    (ConcreteCategory.hom (C.ι.app j')) p'
  exact (hfac j p).symm.trans (h'.trans (hfac j' p'))

private noncomputable def diagramSupportDataLabel (X : Henry.SemiSSet.{u})
    (j : X.Elementsᵒᵖ) :
    (realizationElementsDiagram X ⋙ (forget TopCat)).obj j →
      X.Elements × (ℕ →₀ ℝ) :=
  fun p => (pointSupportElement j.unop.val (ULift.down p),
    pointSupportCoordinates (ULift.down p))

private noncomputable def supportDataCocone (X : Henry.SemiSSet.{u}) :
    Cocone (realizationElementsDiagram X ⋙ (forget TopCat)) where
  pt := X.Elements × (ℕ →₀ ℝ)
  ι :=
    { app := fun j => ↾(diagramSupportDataLabel X j)
      naturality := by
        intro j j' f
        ext p
        let e := j.unop
        let e' := j'.unop
        let ι : e.obj.unop ⟶ e'.obj.unop := f.unop.hom.unop
        have hx : X.map ι.op e'.val = e.val := by
          change X.map f.unop.hom e'.val = e.val
          exact f.unop.map_val
        have hp :
            ULift.down ((realizationElementsDiagram X ⋙ (forget TopCat)).map f p) =
              (ULift.down p).map ι.1.toOrderHom := by
          simp [realizationElementsDiagram, Functor.comp_map, ι]
          rfl
        have hc := pointSupportElement_map ι e'.val (ULift.down p)
        have hq := pointSupportCoordinates_map ι (ULift.down p)
        change (pointSupportElement e'.val
              (ULift.down ((realizationElementsDiagram X ⋙ (forget TopCat)).map f p)),
            pointSupportCoordinates
              (ULift.down ((realizationElementsDiagram X ⋙ (forget TopCat)).map f p))) =
          (pointSupportElement e.val (ULift.down p), pointSupportCoordinates (ULift.down p))
        apply Prod.ext
        · rw [hp, ← hx]
          exact hc.symm
        · rw [hp]
          exact hq }

theorem supportData_eq_of_colimit_eq {X : Henry.SemiSSet.{u}}
    {j j' : X.Elementsᵒᵖ}
    {p : (realizationElementsDiagram X ⋙ (forget TopCat)).obj j}
    {p' : (realizationElementsDiagram X ⋙ (forget TopCat)).obj j'}
    (h : colimit.ι (realizationElementsDiagram X ⋙ (forget TopCat)) j p =
      colimit.ι (realizationElementsDiagram X ⋙ (forget TopCat)) j' p') :
    (pointSupportElement j.unop.val (ULift.down p), pointSupportCoordinates (ULift.down p)) =
      (pointSupportElement j'.unop.val (ULift.down p'),
        pointSupportCoordinates (ULift.down p')) := by
  let C := supportDataCocone X
  have hfac (k : X.Elementsᵒᵖ)
      (q : (realizationElementsDiagram X ⋙ (forget TopCat)).obj k) :
      (ConcreteCategory.hom
        (colimit.desc (realizationElementsDiagram X ⋙ (forget TopCat)) C))
          ((ConcreteCategory.hom
            (colimit.ι (realizationElementsDiagram X ⋙ (forget TopCat)) k)) q) =
        (ConcreteCategory.hom (C.ι.app k)) q :=
    ConcreteCategory.congr_hom (colimit.ι_desc C k) q
  have h' := congrArg (fun z =>
      (ConcreteCategory.hom (colimit.desc (realizationElementsDiagram X ⋙ (forget TopCat)) C)) z) h
  change (ConcreteCategory.hom (C.ι.app j)) p =
    (ConcreteCategory.hom (C.ι.app j')) p'
  exact (hfac j p).symm.trans (h'.trans (hfac j' p'))

noncomputable def realizationElementsTypeIso (X : Henry.SemiSSet.{u}) :
    (Henry.SemiSSet.realization.{u}.obj X : Type u) ≅
      colimit (realizationElementsDiagram X ⋙ (forget TopCat)) :=
  Functor.mapIso (forget TopCat) (realizationElementsColimitIso X) ≪≫
    preservesColimitIso (forget TopCat) (realizationElementsDiagram X)

theorem simplexChar_typeColimit {X : Henry.SemiSSet.{u}} {n : ℕ}
    (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ X) :
    (forget TopCat).map (Henry.SemiSSet.simplexChar.{u} y) ≫
        (realizationElementsTypeIso X).hom =
      colimit.ι (realizationElementsDiagram X ⋙ (forget TopCat))
        (op (simplexElement y)) := by
  change ((forget TopCat).map (simplexChar y) ≫
      (forget TopCat).map (realizationElementsColimitIso X).hom) ≫
      (preservesColimitIso (forget TopCat) (realizationElementsDiagram X)).hom = _
  rw [← Functor.map_comp, simplexChar_colimit]
  exact ι_preservesColimitIso_hom (forget TopCat) (realizationElementsDiagram X)
    (op (simplexElement y))

theorem colimit_point_eq_of_realization_map_eq {X : Henry.SemiSSet.{u}} {n m m' : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ X)
    (v' : Fin (n + 1) → Fin (m' + 1))
    (x' : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m') ⟶ X)
    (h : Henry.SemiSSet.vertexMap.{u} v ≫ Henry.SemiSSet.simplexChar x =
      Henry.SemiSSet.vertexMap.{u} v' ≫ Henry.SemiSSet.simplexChar x')
    (p : (Henry.SemiSSet.toTop.{u}.obj (Henry.SemiSimplexCategory.mk n) : Type u)) :
    colimit.ι (realizationElementsDiagram X ⋙ (forget TopCat))
        (op (simplexElement x)) ((forget TopCat).map (Henry.SemiSSet.vertexMap v) p) =
      colimit.ι (realizationElementsDiagram X ⋙ (forget TopCat))
        (op (simplexElement x')) ((forget TopCat).map (Henry.SemiSSet.vertexMap v') p) := by
  have hcomp {k : ℕ} (w : Fin (n + 1) → Fin (k + 1))
      (z : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk k) ⟶ X) :
      (forget TopCat).map (Henry.SemiSSet.vertexMap.{u} w ≫
        Henry.SemiSSet.simplexChar z) ≫ (realizationElementsTypeIso X).hom =
        (forget TopCat).map (Henry.SemiSSet.vertexMap w) ≫
          colimit.ι (realizationElementsDiagram X ⋙ (forget TopCat))
            (op (simplexElement z)) := by
    rw [Functor.map_comp, Category.assoc, simplexChar_typeColimit]
  have hp := congrArg (fun f :
      (forget TopCat).obj (Henry.SemiSSet.toTop.{u}.obj
          (Henry.SemiSimplexCategory.mk n)) ⟶
        (forget TopCat).obj (Henry.SemiSSet.realization.{u}.obj X) => f p)
      (congrArg (forget TopCat).map h)
  have hp' := congrArg (fun z => (realizationElementsTypeIso X).hom z) hp
  have hl := congrArg (fun f :
      (forget TopCat).obj (Henry.SemiSSet.toTop.{u}.obj
          (Henry.SemiSimplexCategory.mk n)) ⟶
        colimit (realizationElementsDiagram X ⋙ (forget TopCat)) => f p)
      (hcomp v x)
  have hr := congrArg (fun f :
      (forget TopCat).obj (Henry.SemiSSet.toTop.{u}.obj
          (Henry.SemiSimplexCategory.mk n)) ⟶
        colimit (realizationElementsDiagram X ⋙ (forget TopCat)) => f p)
      (hcomp v' x')
  exact hl.symm.trans (hp'.trans hr)

private theorem pointSupportCoordinates_eq_of_vertexMap_eq
    {X : Henry.SemiSSet.{u}} {n m m' : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ X)
    (v' : Fin (n + 1) → Fin (m' + 1))
    (x' : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m') ⟶ X)
    (h : Henry.SemiSSet.vertexMap.{u} v ≫ Henry.SemiSSet.simplexChar x =
      Henry.SemiSSet.vertexMap.{u} v' ≫ Henry.SemiSSet.simplexChar x')
    (p : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    pointSupportCoordinates (p.map v) = pointSupportCoordinates (p.map v') := by
  have hcol := colimit_point_eq_of_realization_map_eq v x v' x' h (ULift.up p)
  have hdata := supportData_eq_of_colimit_eq hcol
  have hcoord := congrArg Prod.snd hdata
  have hv : ULift.down ((forget TopCat).map (Henry.SemiSSet.vertexMap v) (ULift.up p)) =
      Convexity.StdSimplex.map v p := rfl
  have hv' : ULift.down ((forget TopCat).map (Henry.SemiSSet.vertexMap v') (ULift.up p)) =
      Convexity.StdSimplex.map v' p := rfl
  rw [hv, hv'] at hcoord
  exact hcoord

theorem colimit_relation_of_realization_map_eq {X : Henry.SemiSSet.{u}} {n m m' : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ X)
    (v' : Fin (n + 1) → Fin (m' + 1))
    (x' : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m') ⟶ X)
    (h : Henry.SemiSSet.vertexMap.{u} v ≫ Henry.SemiSSet.simplexChar x =
      Henry.SemiSSet.vertexMap.{u} v' ≫ Henry.SemiSSet.simplexChar x')
    (p : (Henry.SemiSSet.toTop.{u}.obj (Henry.SemiSimplexCategory.mk n) : Type u)) :
    Relation.EqvGen (realizationElementsDiagram X ⋙ (forget TopCat)).ColimitTypeRel
      ⟨op (simplexElement x), (forget TopCat).map (Henry.SemiSSet.vertexMap v) p⟩
      ⟨op (simplexElement x'), (forget TopCat).map (Henry.SemiSSet.vertexMap v') p⟩ := by
  apply CategoryTheory.Limits.Types.colimit_eq
  exact colimit_point_eq_of_realization_map_eq v x v' x' h p

theorem sharpMk_eq_of_vertexMap_core {X : Henry.SemiSSet.{u}} {n m m' : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ X)
    (v' : Fin (n + 1) → Fin (m' + 1))
    (x' : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m') ⟶ X)
    (h : Henry.SemiSSet.vertexMap.{u} v ≫ Henry.SemiSSet.simplexChar x =
      Henry.SemiSSet.vertexMap.{u} v' ≫ Henry.SemiSSet.simplexChar x') :
    Henry.SemiSSet.sharpMk v (uliftYonedaEquiv x) =
      Henry.SemiSSet.sharpMk v' (uliftYonedaEquiv x') := by
  let b : Convexity.StdSimplex ℝ (Fin (n + 1)) :=
    Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))
  have hcol := colimit_point_eq_of_realization_map_eq v x v' x' h (ULift.up b)
  have hdata := supportData_eq_of_colimit_eq hcol
  have hv : ULift.down ((forget TopCat).map (Henry.SemiSSet.vertexMap v) (ULift.up b)) =
      Convexity.StdSimplex.map v b := rfl
  have hv' : ULift.down ((forget TopCat).map (Henry.SemiSSet.vertexMap v') (ULift.up b)) =
      Convexity.StdSimplex.map v' b := rfl
  rw [hv, hv'] at hdata
  have helem : pointSupportElement (uliftYonedaEquiv x) (b.map v) =
      pointSupportElement (uliftYonedaEquiv x') (b.map v') := by
    simpa [b, simplexElement] using congrArg Prod.fst hdata
  have hsize := pointSupportSize_eq_of_element_eq
    (uliftYonedaEquiv x) (uliftYonedaEquiv x') (b.map v) (b.map v') helem
  have hface := pointSupportCell_heq
    (uliftYonedaEquiv x) (uliftYonedaEquiv x') (b.map v) (b.map v') helem
  let f : Fin (n + 1) → ℕ := fun i => pointSupportRank (b.map v) (v i)
  let g : Fin (n + 1) → ℕ := fun i => pointSupportRank (b.map v') (v' i)
  have hbaseCoord := pointSupportCoordinates_eq_of_vertexMap_eq v x v' x' h b
  have hbase : b.weights.mapDomain f = b.weights.mapDomain g := by
    simpa only [pointSupportCoordinates_mapVertex, f, g] using hbaseCoord
  have hprobe : ∀ i, (supportProbe i).weights.mapDomain f =
      (supportProbe i).weights.mapDomain g := by
    intro i
    have hc := pointSupportCoordinates_eq_of_vertexMap_eq v x v' x' h (supportProbe i)
    have hrv : pointSupportRank ((supportProbe i).map v) = pointSupportRank (b.map v) := by
      apply pointSupportRank_eq_of_support_eq
      rw [pointSupport_map_eq_image_of_full _ (pointSupport_supportProbe i) v,
        pointSupport_map_eq_image_of_full _ (pointSupport_barycenter) v]
    have hrv' : pointSupportRank ((supportProbe i).map v') = pointSupportRank (b.map v') := by
      apply pointSupportRank_eq_of_support_eq
      rw [pointSupport_map_eq_image_of_full _ (pointSupport_supportProbe i) v',
        pointSupport_map_eq_image_of_full _ (pointSupport_barycenter) v']
    rw [pointSupportCoordinates_mapVertex, pointSupportCoordinates_mapVertex,
      hrv, hrv'] at hc
    simpa only [f, g] using hc
  have hfun := function_eq_of_barycenter_probes f g hbase hprobe
  have hfactor : ∀ i, (pointSupportFactor v i).val = (pointSupportFactor v' i).val := by
    intro i
    change f i = g i
    exact congrFun hfun i
  calc
    Henry.SemiSSet.sharpMk v (uliftYonedaEquiv x) =
        Henry.SemiSSet.sharpMk (pointSupportFactor v)
          (pointSupportCell (uliftYonedaEquiv x) (b.map v)) :=
      sharpMk_eq_supportFactor v x
    _ = Henry.SemiSSet.sharpMk (pointSupportFactor v')
          (pointSupportCell (uliftYonedaEquiv x') (b.map v')) :=
      sharpMk_eq_of_heq_supportData (pointSupportFactor v) (pointSupportFactor v')
        (pointSupportCell (uliftYonedaEquiv x) (b.map v))
        (pointSupportCell (uliftYonedaEquiv x') (b.map v')) hsize hfactor hface
    _ = Henry.SemiSSet.sharpMk v' (uliftYonedaEquiv x') :=
      (sharpMk_eq_supportFactor v' x').symm

end HomotopyHypothesis.Realization.PointStructure

namespace HomotopyHypothesis.Henry.Packages

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

theorem sharpMk_eq_of_vertexMap_proof {X : SemiSSet.{u}} {n m m' : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (x : stdSimplex.obj (SemiSimplexCategory.mk m) ⟶ X)
    (v' : Fin (n + 1) → Fin (m' + 1))
    (x' : stdSimplex.obj (SemiSimplexCategory.mk m') ⟶ X)
    (h : vertexMap v ≫ simplexChar x = vertexMap v' ≫ simplexChar x') :
    sharpMk v (uliftYonedaEquiv x) = sharpMk v' (uliftYonedaEquiv x') :=
  HomotopyHypothesis.Realization.PointStructure.sharpMk_eq_of_vertexMap_core v x v' x' h

#print axioms sharpMk_eq_of_vertexMap_proof

end HomotopyHypothesis.Henry.Packages
