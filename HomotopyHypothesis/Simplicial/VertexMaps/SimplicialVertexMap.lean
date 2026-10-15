import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.SimplicialVertexMapStatement
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Coherence of global vertex maps into simplicial complexes

Compatible local affine vertex formulas for a continuous map into an ordered
simplicial complex, agreeing on 0-simplices via a global vertex map, induce
a coherent simplicial map into the formal degeneracies.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Simplicial.VertexMaps

open Henry Henry.SemiSSet Approximation.Zeeman

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

/-- Factoring a vertex map through its image face does not change the formal simplex. -/
theorem sharpMk_eq_of_vertex_eq {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {n m m' : ℕ} (v : Fin (n + 1) → Fin (m + 1)) (x : K.obj (op (Henry.SemiSimplexCategory.mk m)))
    (v' : Fin (n + 1) → Fin (m' + 1)) (x' : K.obj (op (Henry.SemiSimplexCategory.mk m')))
    (hv : ∀ i, vertex x (v i) = vertex x' (v' i)) :
    sharpMk v x = sharpMk v' x' := by
  classical
  let s : Finset (Fin (m + 1)) := Finset.univ.image v
  have hs_ne : s.Nonempty := ⟨v 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩⟩
  have hs_pos : 0 < s.card := Finset.Nonempty.card_pos hs_ne
  obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 := ⟨s.card - 1, by omega⟩
  let e : Fin (k + 1) ↪o Fin (m + 1) := s.orderEmbOfFin hk
  let iso : Fin (k + 1) ≃o s := s.orderIsoOfFin hk
  let ι : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m :=
    ⟨SimplexCategory.Hom.mk e.toOrderHom, by
      change Mono (show SimplexCategory.mk k ⟶ SimplexCategory.mk m from
        SimplexCategory.Hom.mk e.toOrderHom)
      rw [SimplexCategory.mono_iff_injective]
      exact e.injective⟩
  let v_im : Fin (n + 1) → Fin (k + 1) := fun i =>
    iso.symm ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have he_v_im (i : Fin (n + 1)) : e (v_im i) = v i := by
    change (iso (iso.symm ⟨v i, _⟩)).val = v i
    rw [OrderIso.apply_symm_apply]
  have h_comp : ι.1.toOrderHom ∘ v_im = v := by
    funext i
    exact he_v_im i
  have hv_im_surj : Function.Surjective v_im := by
    intro j
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (iso j).property
    refine ⟨i, ?_⟩
    dsimp [v_im]
    have : (⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ : s) = iso j := Subtype.ext hi
    rw [this, OrderIso.symm_apply_apply]

  let s' : Finset (Fin (m' + 1)) := Finset.univ.image v'
  have hs'_ne : s'.Nonempty := ⟨v' 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩⟩
  have hs'_pos : 0 < s'.card := Finset.Nonempty.card_pos hs'_ne
  obtain ⟨k', hk'⟩ : ∃ k', s'.card = k' + 1 := ⟨s'.card - 1, by omega⟩
  let e' : Fin (k' + 1) ↪o Fin (m' + 1) := s'.orderEmbOfFin hk'
  let iso' : Fin (k' + 1) ≃o s' := s'.orderIsoOfFin hk'
  let ι' : Henry.SemiSimplexCategory.mk k' ⟶ Henry.SemiSimplexCategory.mk m' :=
    ⟨SimplexCategory.Hom.mk e'.toOrderHom, by
      change Mono (show SimplexCategory.mk k' ⟶ SimplexCategory.mk m' from
        SimplexCategory.Hom.mk e'.toOrderHom)
      rw [SimplexCategory.mono_iff_injective]
      exact e'.injective⟩
  let v'_im : Fin (n + 1) → Fin (k' + 1) := fun i =>
    iso'.symm ⟨v' i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have he'_v'_im (i : Fin (n + 1)) : e' (v'_im i) = v' i := by
    change (iso' (iso'.symm ⟨v' i, _⟩)).val = v' i
    rw [OrderIso.apply_symm_apply]
  have h_comp' : ι'.1.toOrderHom ∘ v'_im = v' := by
    funext i
    exact he'_v'_im i
  have hv'_im_surj : Function.Surjective v'_im := by
    intro j
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (iso' j).property
    refine ⟨i, ?_⟩
    dsimp [v'_im]
    have : (⟨v' i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ : s') = iso' j := Subtype.ext hi
    rw [this, OrderIso.symm_apply_apply]

  let x_im := K.map ι.op x
  let x'_im := K.map ι'.op x'

  have hx_im_v (i : Fin (n + 1)) : vertex x_im (v_im i) = vertex x (v i) := by
    dsimp [x_im]
    rw [vertex_map]
    change vertex x (e (v_im i)) = vertex x (v i)
    rw [he_v_im i]

  have hx'_im_v' (i : Fin (n + 1)) : vertex x'_im (v'_im i) = vertex x' (v' i) := by
    dsimp [x'_im]
    rw [vertex_map]
    change vertex x' (e' (v'_im i)) = vertex x' (v' i)
    rw [he'_v'_im i]

  have hS_eq : Finset.univ.image (vertex x ∘ v) = Finset.univ.image (vertex x' ∘ v') := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, by rw [hv i]⟩
    · rintro ⟨i, rfl⟩
      refine ⟨i, by rw [hv i]⟩

  have hcard_s : s.card = (Finset.univ.image (vertex x ∘ v)).card := by
    have h_im : Finset.univ.image (vertex x ∘ v) = s.image (vertex x) := by
      ext a
      simp only [s, Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨v i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [h_im, Finset.card_image_of_injective s (vertex_injective hK x)]

  have hcard_s' : s'.card = (Finset.univ.image (vertex x' ∘ v')).card := by
    have h_im : Finset.univ.image (vertex x' ∘ v') = s'.image (vertex x') := by
      ext a
      simp only [s', Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨v' i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [h_im, Finset.card_image_of_injective s' (vertex_injective hK x')]

  have hkk' : k = k' := by
    have : k + 1 = k' + 1 := by
      rw [← hk, ← hk', hcard_s, hcard_s', hS_eq]
    omega

  cases hkk'

  have hrange_x_im : Set.range (vertex x_im) = Set.range (vertex x'_im) := by
    calc
      Set.range (vertex x_im) = Set.range (vertex x_im ∘ v_im) := by
        rw [Function.Surjective.range_comp hv_im_surj]
      _ = Set.range (fun i => vertex x (v i)) := by
        congr 1; funext i; exact hx_im_v i
      _ = Set.range (fun i => vertex x' (v' i)) := by
        congr 1; funext i; exact hv i
      _ = Set.range (vertex x'_im ∘ v'_im) := by
        congr 1; funext i; exact (hx'_im_v' i).symm
      _ = Set.range (vertex x'_im) := by
        rw [Function.Surjective.range_comp hv'_im_surj]

  have hx_eq : x_im = x'_im := simplex_eq_of_vertex_range_eq hK hrange_x_im

  have hv_eq : v_im = v'_im := by
    funext i
    apply vertex_injective hK x_im
    rw [hx_im_v i, hv i, ← hx'_im_v' i, hx_eq]

  calc
    sharpMk v x = sharpMk (ι.1.toOrderHom ∘ v_im) x := by rw [h_comp]
    _ = sharpMk v_im x_im := sharp_mk_face ι v_im x
    _ = sharpMk v'_im x'_im := by rw [hx_eq, hv_eq]
    _ = sharpMk (ι'.1.toOrderHom ∘ v'_im) x' := (sharp_mk_face ι' v'_im x').symm
    _ = sharpMk v' x' := by rw [h_comp']

/-- A global vertex map and compatible affine simplex formulas give a coherent simplicial map. -/
theorem simplicialVertexMapStatement_proof : SimplicialVertexMapStatement.{u} := by
  intro W K hK F q hF
  classical
  let data (n : ℕ) (y : W.obj (op (Henry.SemiSimplexCategory.mk n))) :=
    hF n (uliftYonedaEquiv.symm y)
  let chosenM (n : ℕ) (y : W.obj (op (Henry.SemiSimplexCategory.mk n))) : ℕ :=
    Classical.choose (data n y)
  let chosenX (n : ℕ) (y : W.obj (op (Henry.SemiSimplexCategory.mk n))) :
      Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk (chosenM n y)) ⟶ K :=
    Classical.choose (Classical.choose_spec (data n y))
  let chosenV (n : ℕ) (y : W.obj (op (Henry.SemiSimplexCategory.mk n))) :
      Fin (n + 1) → Fin (chosenM n y + 1) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (data n y)))
  have chosen_vertex (n : ℕ) (y : W.obj (op (Henry.SemiSimplexCategory.mk n))) (i : Fin (n + 1)) :
      vertex (uliftYonedaEquiv (chosenX n y)) (chosenV n y i) =
        q (vertex y i) := by
    have hq := (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (data n y)))).1 i
    rw [hq]
    congr 2
    exact Equiv.apply_symm_apply uliftYonedaEquiv y
  have chosen_char (n : ℕ) (y : W.obj (op (Henry.SemiSimplexCategory.mk n))) :
      simplexChar (uliftYonedaEquiv.symm y) ≫ F =
        vertexMap (chosenV n y) ≫ simplexChar (chosenX n y) :=
    (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (data n y)))).2
  let φ : W ⟶ sharp K := {
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
                  change sharpMk (chosenV n' (W.map face.op y))
                      (uliftYonedaEquiv (chosenX n' (W.map face.op y))) =
                    (sharp K).map face.op
                      (sharpMk (chosenV n y) (uliftYonedaEquiv (chosenX n y)))
                  rw [sharp_map_mk face (chosenV n y) (uliftYonedaEquiv (chosenX n y))]
                  apply (sharpMk_eq_of_vertex_eq hK (chosenV n y ∘ face.1.toOrderHom)
                    (uliftYonedaEquiv (chosenX n y))
                    (chosenV n' (W.map face.op y))
                    (uliftYonedaEquiv (chosenX n' (W.map face.op y))) ?_).symm
                  intro k
                  dsimp
                  rw [chosen_vertex n y (face.1.toOrderHom k)]
                  rw [chosen_vertex n' (W.map face.op y) k]
                  rw [vertex_map face y k]
  }
  refine ⟨φ, ?_⟩
  intro n y
  let y_obj := uliftYonedaEquiv y
  refine ⟨chosenM n y_obj, chosenX n y_obj, chosenV n y_obj, ⟨rfl, ?_⟩⟩
  have hc := chosen_char n y_obj
  rw [Equiv.symm_apply_apply] at hc
  exact hc

example : SimplicialVertexMapStatement.{u} :=
  simplicialVertexMapStatement_proof

#print axioms simplicialVertexMapStatement_proof

end HomotopyHypothesis.Simplicial.VertexMaps
