import Mathlib.Topology.CompactOpen
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Packages.Approximation.SharpMkEqOfVertexMap
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.KanApproximation.Part1
import HomotopyHypothesis.Approximation.Topological.Projection
/-!
# Gluing over pushouts

Simplicial maps and finite semi-simplicial sets can be analyzed simplexwise, while homotopies glue
across pushouts of spaces.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Gluing.Simplicial

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological

theorem simplexChar_on_simplexMap {n n' : ℕ}
    (θ : Henry.SemiSimplexCategory.mk n' ⟶ Henry.SemiSimplexCategory.mk n) :
    simplexChar (Henry.SemiSSet.stdSimplex.{u}.map θ) =
      toTop.{u}.map θ ≫ (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk n) := by
  unfold simplexChar
  change (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk n') ≫
      (Henry.SemiSSet.stdSimplex.{u} ⋙ Henry.SemiSSet.realization.{u}).map θ =
    toTop.{u}.map θ ≫ (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk n)
  exact ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).naturality θ).symm

theorem simplexChar_stdSimplex_map {Y : SemiSSet.{u}} {n n' : ℕ}
    (θ : Henry.SemiSimplexCategory.mk n' ⟶ Henry.SemiSimplexCategory.mk n)
    (y : stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ Y) :
    simplexChar (Henry.SemiSSet.stdSimplex.{u}.map θ ≫ y) =
      toTop.{u}.map θ ≫ simplexChar y := by
  calc
    simplexChar (Henry.SemiSSet.stdSimplex.{u}.map θ ≫ y) =
        simplexChar (Henry.SemiSSet.stdSimplex.{u}.map θ) ≫ Henry.SemiSSet.realization.{u}.map y :=
          simplexChar_comp _ _
    _ = (toTop.{u}.map θ ≫
          (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
          (Henry.SemiSimplexCategory.mk n)) ≫ Henry.SemiSSet.realization.{u}.map y := by
        rw [simplexChar_on_simplexMap.{u} θ]
        rfl
    _ = toTop.{u}.map θ ≫ simplexChar y := by
        rw [simplexChar]
        exact Category.assoc _ _ _

theorem vertexMap_comp {n n' m : ℕ}
    (θ : Henry.SemiSimplexCategory.mk n' ⟶ Henry.SemiSimplexCategory.mk n)
    (v : Fin (n + 1) → Fin (m + 1)) :
    toTop.map θ ≫ vertexMap v = vertexMap (v ∘ θ.1.toOrderHom) := by
  rw [toTop_map_eq_affineMap]
  exact affineMap_comp _ _

set_option maxHeartbeats 500000 in
theorem sharp_face {X : SemiSSet.{u}} {n n' m : ℕ}
    (θ : Henry.SemiSimplexCategory.mk n' ⟶ Henry.SemiSimplexCategory.mk n)
    (v : Fin (n + 1) → Fin (m + 1))
    (x : X.obj (op (Henry.SemiSimplexCategory.mk m))) :
    (sharp X).map θ.op (sharpMk v x) = sharpMk (v ∘ θ.1.toOrderHom) x := by
  let v₀ : Quiver.Hom (Opposite.op (⟨m⟩ : FinFun)) (Opposite.op (⟨n⟩ : FinFun)) :=
    Quiver.Hom.op (show (⟨n⟩ : FinFun) ⟶ ⟨m⟩ from v)
  let θ₀ : Quiver.Hom (Opposite.op (⟨n⟩ : FinFun)) (Opposite.op (⟨n'⟩ : FinFun)) :=
    Quiver.Hom.op (show (⟨n'⟩ : FinFun) ⟶ ⟨n⟩ from θ.1.toOrderHom)
  let vθ : Quiver.Hom (Opposite.op (⟨m⟩ : FinFun)) (Opposite.op (⟨n'⟩ : FinFun)) :=
    Quiver.Hom.op (show (⟨n'⟩ : FinFun) ⟶ ⟨m⟩ from v ∘ θ.1.toOrderHom)
  let b : (SemiSimplexCategory.toFinFun.op.leftKanExtension X).obj
      (Opposite.op (⟨m⟩ : FinFun)) := by
    simpa [sharp, toSharp, SemiSimplexCategory.toFinFun, SimplexCategory.len_mk] using
      ((toSharp X).app (op (Henry.SemiSimplexCategory.mk m)) x)
  have hcomp : v₀ ≫ θ₀ = vθ := by
    apply Quiver.Hom.op_inj
    rfl
  dsimp [sharp, sharpMk, toSharp, SemiSimplexCategory.toFinFun]
  change (SemiSimplexCategory.toFinFun.op.leftKanExtension X).map θ₀
      ((SemiSimplexCategory.toFinFun.op.leftKanExtension X).map v₀ b) =
    (SemiSimplexCategory.toFinFun.op.leftKanExtension X).map vθ b
  calc
    (SemiSimplexCategory.toFinFun.op.leftKanExtension X).map θ₀
        ((SemiSimplexCategory.toFinFun.op.leftKanExtension X).map v₀ b) =
        (SemiSimplexCategory.toFinFun.op.leftKanExtension X).map (v₀ ≫ θ₀)
          b := by
            rw [← (SemiSimplexCategory.toFinFun.op.leftKanExtension X).map_comp_apply]
    _ = (SemiSimplexCategory.toFinFun.op.leftKanExtension X).map vθ
          b := by rw [hcomp]

theorem isSimplicial_of_forall_proof {Y X : SemiSSet.{u}}
    (f : realization.obj Y ⟶ realization.obj X)
    (hf : ∀ (n : ℕ) (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ Y),
      ∃ (m : ℕ) (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ X)
        (v : Fin (n + 1) → Fin (m + 1)),
        simplexChar y ≫ f = vertexMap v ≫ simplexChar x) :
    IsSimplicial f := by
  classical
  let data (n : ℕ) (y : Y.obj (op (Henry.SemiSimplexCategory.mk n))) :=
    hf n (uliftYonedaEquiv.symm y)
  let chosenM (n : ℕ) (y : Y.obj (op (Henry.SemiSimplexCategory.mk n))) : ℕ :=
    Classical.choose (data n y)
  let chosenX (n : ℕ) (y : Y.obj (op (Henry.SemiSimplexCategory.mk n))) :
      stdSimplex.obj (Henry.SemiSimplexCategory.mk (chosenM n y)) ⟶ X :=
    Classical.choose (Classical.choose_spec (data n y))
  let chosenV (n : ℕ) (y : Y.obj (op (Henry.SemiSimplexCategory.mk n))) :
      Fin (n + 1) → Fin (chosenM n y + 1) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (data n y)))
  have chosen_spec (n : ℕ) (y : Y.obj (op (Henry.SemiSimplexCategory.mk n))) :
      simplexChar (uliftYonedaEquiv.symm y) ≫ f =
        vertexMap (chosenV n y) ≫ simplexChar (chosenX n y) :=
    Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (data n y)))
  let φ : Y ⟶ sharp X := {
    app := fun j => by
      cases j with
      | op j =>
        cases j with
        | mk j =>
          cases j with
          | mk n =>
            exact TypeCat.ofHom fun y =>
              sharpMk (chosenV n y) (uliftYonedaEquiv (chosenX n y))
    naturality := by
      intro i j θ
      cases i with
      | op i =>
        cases i with
        | mk i =>
          cases i with
          | mk n =>
            cases j with
            | op j =>
              cases j with
              | mk j =>
                cases j with
                | mk n' =>
                  ext y
                  let face : Henry.SemiSimplexCategory.mk n' ⟶ Henry.SemiSimplexCategory.mk n := θ.unop
                  change sharpMk (chosenV n' (Y.map θ y))
                      (uliftYonedaEquiv (chosenX n' (Y.map θ y))) =
                    (sharp X).map θ
                      (sharpMk (chosenV n y) (uliftYonedaEquiv (chosenX n y)))
                  change sharpMk (chosenV n' (Y.map θ y))
                      (uliftYonedaEquiv (chosenX n' (Y.map θ y))) =
                    (sharp X).map face.op
                      (sharpMk (chosenV n y) (uliftYonedaEquiv (chosenX n y)))
                  rw [sharp_face (X := X) (θ := face) (v := chosenV n y)
                    (x := uliftYonedaEquiv (chosenX n y))]
                  have hface : uliftYonedaEquiv.symm (Y.map θ y) =
                      Henry.SemiSSet.stdSimplex.map face ≫ uliftYonedaEquiv.symm y := by
                    exact uliftYonedaEquiv_symm_map θ y
                  have hleft := chosen_spec n' (Y.map θ y)
                  rw [hface] at hleft
                  have hright := chosen_spec n y
                  apply (Packages.sharpMk_eq_of_vertexMap
                    (v := chosenV n y ∘ face.1.toOrderHom)
                    (x := chosenX n y)
                    (v' := chosenV n' (Y.map θ y))
                    (x' := chosenX n' (Y.map θ y)) ?_).symm
                  calc
                    vertexMap (chosenV n y ∘ face.1.toOrderHom) ≫
                        simplexChar (chosenX n y) =
                          toTop.map face ≫ vertexMap (chosenV n y) ≫
                            simplexChar (chosenX n y) := by
                              rw [← vertexMap_comp, Category.assoc]
                    _ = toTop.map face ≫ simplexChar (uliftYonedaEquiv.symm y) ≫ f := by
                          rw [← hright]
                    _ = simplexChar (Henry.SemiSSet.stdSimplex.map face ≫
                          uliftYonedaEquiv.symm y) ≫ f := by
                          rw [simplexChar_stdSimplex_map]
                          exact (Category.assoc _ _ _).symm
                    _ = vertexMap (chosenV n' (Y.map θ y)) ≫
                          simplexChar (chosenX n' (Y.map θ y)) := hleft
  }
  refine ⟨φ, ?_⟩
  intro n y
  obtain ⟨m, x, v, hy⟩ := hf n y
  refine ⟨m, x, v, ?_, hy⟩
  dsimp [φ]
  change sharpMk (chosenV n (uliftYonedaEquiv y))
      (uliftYonedaEquiv (chosenX n (uliftYonedaEquiv y))) = sharpMk v (uliftYonedaEquiv x)
  apply (Packages.sharpMk_eq_of_vertexMap
    (v := v) (x := x)
    (v' := chosenV n (uliftYonedaEquiv y))
    (x' := chosenX n (uliftYonedaEquiv y)) ?_).symm
  calc
    vertexMap v ≫ simplexChar x = simplexChar y ≫ f := hy.symm
    _ = simplexChar (uliftYonedaEquiv.symm (uliftYonedaEquiv y)) ≫ f := by
      rw [Equiv.symm_apply_apply]
    _ = vertexMap (chosenV n (uliftYonedaEquiv y)) ≫
          simplexChar (chosenX n (uliftYonedaEquiv y)) := chosen_spec n (uliftYonedaEquiv y)

#print axioms isSimplicial_of_forall_proof

theorem exists_homotopy_of_isPushout_proof {A B C D T : TopCat.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {k : C ⟶ D}
    (sq : IsPushout f g h k) (u₀ u₁ : D ⟶ T)
    (HB : ContinuousMap.Homotopy (h ≫ u₀).hom (h ≫ u₁).hom)
    (HC : ContinuousMap.Homotopy (k ≫ u₀).hom (k ≫ u₁).hom)
    (hBC : ∀ (t : unitInterval) (a : A), HB (t, f a) = HC (t, g a)) :
    ∃ H : ContinuousMap.Homotopy u₀.hom u₁.hom,
      (∀ (t : unitInterval) (b : B), H (t, h b) = HB (t, b)) ∧
        ∀ (t : unitInterval) (c : C), H (t, k c) = HC (t, c) := by
  let HB' : C(B × unitInterval, T) :=
    HB.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩
  let HC' : C(C × unitInterval, T) :=
    HC.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩
  let HBc : C(B, C(unitInterval, T)) := HB'.curry
  let HCc : C(C, C(unitInterval, T)) := HC'.curry
  let iB : B ⟶ TopCat.of C(unitInterval, T) := TopCat.ofHom HBc
  let iC : C ⟶ TopCat.of C(unitInterval, T) := TopCat.ofHom HCc
  have hBC' : f ≫ iB = g ≫ iC := by
    apply TopCat.ext
    intro a
    apply ContinuousMap.ext
    intro t
    change HBc (f a) t = HCc (g a) t
    simpa [HBc, HCc, HB', HC', ContinuousMap.curry_apply] using hBC t a
  let q : D ⟶ TopCat.of C(unitInterval, T) := sq.desc iB iC hBC'
  have hqB : h ≫ q = iB := by
    simpa [q] using sq.inl_desc iB iC hBC'
  have hqC : k ≫ q = iC := by
    simpa [q] using sq.inr_desc iB iC hBC'
  have hqB_eval (b : B) (t : unitInterval) : q (h b) t = HB (t, b) := by
    have hq := ConcreteCategory.congr_hom hqB b
    change q (h b) = HBc b at hq
    change q (h b) t = HB (t, b)
    rw [hq]
    simp [HBc, HB', ContinuousMap.curry_apply]
  have hqC_eval (c : C) (t : unitInterval) : q (k c) t = HC (t, c) := by
    have hq := ConcreteCategory.congr_hom hqC c
    change q (k c) = HCc c at hq
    change q (k c) t = HC (t, c)
    rw [hq]
    simp [HCc, HC', ContinuousMap.curry_apply]
  let Hmap : C(unitInterval × D, T) :=
    (ContinuousMap.uncurry q.hom).comp ⟨Prod.swap, continuous_swap⟩
  have Hmap_apply (t : unitInterval) (d : D) : Hmap (t, d) = q d t := rfl
  let Hzero : D ⟶ T := TopCat.ofHom ⟨
    (fun d => Hmap (0, d)), Hmap.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let Hone : D ⟶ T := TopCat.ofHom ⟨
    (fun d => Hmap (1, d)), Hmap.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hz : Hzero = u₀ := by
    apply sq.hom_ext
    · ext b
      change Hmap (0, h b) = u₀ (h b)
      rw [Hmap_apply, hqB_eval]
      simpa using HB.map_zero_left b
    · ext c
      change Hmap (0, k c) = u₀ (k c)
      rw [Hmap_apply, hqC_eval]
      simpa using HC.map_zero_left c
  have ho : Hone = u₁ := by
    apply sq.hom_ext
    · ext b
      change Hmap (1, h b) = u₁ (h b)
      rw [Hmap_apply, hqB_eval]
      simpa using HB.map_one_left b
    · ext c
      change Hmap (1, k c) = u₁ (k c)
      rw [Hmap_apply, hqC_eval]
      simpa using HC.map_one_left c
  refine ⟨⟨Hmap, ?_, ?_⟩, ?_, ?_⟩
  · intro d
    exact ConcreteCategory.congr_hom hz d
  · intro d
    exact ConcreteCategory.congr_hom ho d
  · intro t b
    change Hmap (t, h b) = HB (t, b)
    rw [Hmap_apply, hqB_eval]
  · intro t c
    change Hmap (t, k c) = HC (t, c)
    rw [Hmap_apply, hqC_eval]

#print axioms exists_homotopy_of_isPushout_proof

theorem pushout_simplex_cases_proof {A B C D : SemiSSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {k : C ⟶ D}
    (sq : IsPushout f g h k) (n : ℕ)
    (d : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ D) :
    (∃ b, b ≫ h = d) ∨ ∃ c, c ≫ k = d := by
  let i := op (Henry.SemiSimplexCategory.mk n)
  let ev := (evaluation Henry.SemiSimplexCategoryᵒᵖ (Type u)).obj i
  let c : PushoutCocone f g := PushoutCocone.mk h k sq.w
  have hc : IsColimit (ev.mapCocone c) := isColimitOfPreserves ev sq.isColimit
  obtain ⟨j, z, hz⟩ := Types.jointly_surjective_of_isColimit hc (uliftYonedaEquiv d)
  cases j with
  | none =>
      have hz' : h.app i (f.app i z) = uliftYonedaEquiv d := by
        change (ev.map (f ≫ h)) z = uliftYonedaEquiv d at hz
        rw [ev.map_comp_apply] at hz
        change h.app i (f.app i z) = uliftYonedaEquiv d at hz
        exact hz
      left
      refine ⟨uliftYonedaEquiv.symm (f.app i z), ?_⟩
      apply uliftYonedaEquiv.injective
      rw [uliftYonedaEquiv_comp]
      simpa only [Equiv.apply_symm_apply] using hz'
  | some side =>
      cases side with
      | left =>
          have hz' : h.app i z = uliftYonedaEquiv d := by
            change (ev.map h) z = uliftYonedaEquiv d at hz
            change h.app i z = uliftYonedaEquiv d at hz
            exact hz
          left
          refine ⟨uliftYonedaEquiv.symm z, ?_⟩
          apply uliftYonedaEquiv.injective
          rw [uliftYonedaEquiv_comp]
          simpa only [Equiv.apply_symm_apply] using hz'
      | right =>
          have hz' : k.app i z = uliftYonedaEquiv d := by
            change (ev.map k) z = uliftYonedaEquiv d at hz
            change k.app i z = uliftYonedaEquiv d at hz
            exact hz
          right
          refine ⟨uliftYonedaEquiv.symm z, ?_⟩
          apply uliftYonedaEquiv.injective
          rw [uliftYonedaEquiv_comp]
          simpa only [Equiv.apply_symm_apply] using hz'

#print axioms pushout_simplex_cases_proof

theorem isFinite_of_isPushout_proof {A B C D : SemiSSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {k : C ⟶ D}
    (sq : IsPushout f g h k) (hB : B.IsFinite) (hC : C.IsFinite) : D.IsFinite := by
  classical
  constructor
  · intro n
    let i := op (Henry.SemiSimplexCategory.mk n)
    letI : Finite (B.obj i) := hB.1 n
    letI : Finite (C.obj i) := hC.1 n
    apply Finite.of_surjective (Sum.elim (h.app i) (k.app i))
    intro dVal
    rcases pushout_simplex_cases_proof sq n (uliftYonedaEquiv.symm dVal) with
      ⟨b, hb⟩ | ⟨c, hc⟩
    · refine ⟨Sum.inl (uliftYonedaEquiv b), ?_⟩
      have hh := congrArg uliftYonedaEquiv hb
      simpa [i, uliftYonedaEquiv_comp, Equiv.apply_symm_apply] using hh
    · refine ⟨Sum.inr (uliftYonedaEquiv c), ?_⟩
      have hh := congrArg uliftYonedaEquiv hc
      simpa [i, uliftYonedaEquiv_comp, Equiv.apply_symm_apply] using hh
  · obtain ⟨NB, hNB⟩ := hB.2
    obtain ⟨NC, hNC⟩ := hC.2
    refine ⟨max NB NC, ?_⟩
    intro n hn
    let i := op (Henry.SemiSimplexCategory.mk n)
    let hBN : IsEmpty (B.obj i) := hNB n (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hn)
    let hCN : IsEmpty (C.obj i) := hNC n (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hn)
    refine ⟨fun dVal => ?_⟩
    rcases pushout_simplex_cases_proof sq n (uliftYonedaEquiv.symm dVal) with
      ⟨b, _⟩ | ⟨c, _⟩
    · exact hBN.false (uliftYonedaEquiv b)
    · exact hCN.false (uliftYonedaEquiv c)

#print axioms isFinite_of_isPushout_proof

theorem mono_of_isPushout_proof {A B C D : SemiSSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {k : C ⟶ D}
    (sq : IsPushout f g h k) [Mono f] : Mono k := by
  rw [NatTrans.mono_iff_mono_app]
  intro i
  let ev := (evaluation Henry.SemiSimplexCategoryᵒᵖ (Type u)).obj i
  let cEval := ev.mapCocone sq.cocone
  have hc : IsColimit cEval := isColimitOfPreserves ev sq.isColimit
  let cp : PushoutCocone ((span f g ⋙ ev).map WalkingSpan.Hom.fst)
      ((span f g ⋙ ev).map WalkingSpan.Hom.snd) :=
    PushoutCocone.mk (cEval.ι.app WalkingSpan.left) (cEval.ι.app WalkingSpan.right)
      ((cEval.ι.naturality WalkingSpan.Hom.fst).trans
        (cEval.ι.naturality WalkingSpan.Hom.snd).symm)
  have hc' : IsColimit cp :=
    IsColimit.equivOfNatIsoOfIso _ _ _ (PushoutCocone.isoMk cEval) hc
  haveI : Mono ((span f g ⋙ ev).map WalkingSpan.Hom.fst) := by
    change Mono (ev.map f)
    infer_instance
  have hk : Mono (ev.map k) := by
    change Mono cp.inr
    exact Types.pushoutCocone_inr_mono_of_isColimit hc'
  change Mono (ev.map k)
  exact hk

#print axioms mono_of_isPushout_proof

end HomotopyHypothesis.Gluing.Simplicial
