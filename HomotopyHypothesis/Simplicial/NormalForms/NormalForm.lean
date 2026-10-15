import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteRealization.Proofs
import HomotopyHypothesis.Gluing.Simplicial.Glue
import HomotopyHypothesis.Simplicial.SharpNormalForms.NormalForms
import HomotopyHypothesis.Approximation.Topological.Complex
/-!
# Faces and realizations of normal forms

The surjective representatives of a formal degeneracy behave naturally under faces, and their
affine realizations do not depend on the chosen representative.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Simplicial.NormalForms

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological

private def imageSet {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) : Finset (Fin (m + 1)) :=
  Finset.univ.image v

private theorem imageSet_card_pos {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    0 < (imageSet v).card := by
  apply Finset.card_pos.mpr
  refine ⟨v 0, ?_⟩
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

private def imageSize {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) : ℕ :=
  (imageSet v).card - 1

private theorem imageSet_card_eq {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    (imageSet v).card = imageSize v + 1 := by
  dsimp [imageSize]
  exact (Nat.sub_add_cancel (imageSet_card_pos v)).symm

private noncomputable def imageOrderIso {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    Fin (imageSize v + 1) ≃o imageSet v :=
  (imageSet v).orderIsoOfFin (imageSet_card_eq v)

private noncomputable def imageEmbedding {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    Fin (imageSize v + 1) ↪o Fin (m + 1) :=
  (imageOrderIso v).toOrderEmbedding.trans (OrderEmbedding.subtype _)

private theorem imageSet_mem {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (i : Fin (n + 1)) : v i ∈ imageSet v :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private noncomputable def imageFactor {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    Fin (n + 1) → Fin (imageSize v + 1) := fun i =>
  (imageOrderIso v).symm ⟨v i, imageSet_mem v i⟩

private theorem image_factor {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (i : Fin (n + 1)) : imageEmbedding v (imageFactor v i) = v i := by
  have h := (imageOrderIso v).apply_symm_apply
    (⟨v i, imageSet_mem v i⟩ : imageSet v)
  change ((imageOrderIso v) ((imageOrderIso v).symm ⟨v i, imageSet_mem v i⟩)).val = _
  exact congrArg Subtype.val h

private theorem imageFactor_surjective {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    Function.Surjective (imageFactor v) := by
  intro j
  have hj : imageEmbedding v j ∈ imageSet v := by
    exact (imageOrderIso v j).property
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hj
  refine ⟨i, ?_⟩
  have hval : imageOrderIso v (imageFactor v i) = imageOrderIso v j := by
    rw [imageFactor, OrderIso.apply_symm_apply]
    apply Subtype.ext
    simpa [imageEmbedding] using hi
  exact (imageOrderIso v).injective hval

private noncomputable def imageFace {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    Henry.SemiSimplexCategory.mk (imageSize v) ⟶ Henry.SemiSimplexCategory.mk m := by
  let f : SimplexCategory.mk (imageSize v) ⟶ SimplexCategory.mk m :=
    SimplexCategory.Hom.mk (imageEmbedding v)
  have hf : Mono f := by
    rw [SimplexCategory.mono_iff_injective]
    exact (imageEmbedding v).injective
  exact ⟨f, hf⟩

private theorem sharp_reduce {X : SemiSSet.{u}} {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (x : X.obj (op (Henry.SemiSimplexCategory.mk m))) :
    ∃ (k : ℕ) (q : Fin (n + 1) → Fin (k + 1))
      (ι : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m),
      Function.Surjective q ∧ v = ι.1.toOrderHom ∘ q ∧
        sharpMk v x = sharpMk q (X.map ι.op x) := by
  let k := imageSize v
  let q := imageFactor v
  let ι := imageFace v
  have hq : Function.Surjective q := imageFactor_surjective v
  have hfactor : ι.1.toOrderHom ∘ q = v := by
    funext i
    change imageEmbedding v (imageFactor v i) = v i
    exact image_factor v i
  refine ⟨k, q, ι, hq, hfactor.symm, ?_⟩
  rw [hfactor.symm]
  exact HomotopyHypothesis.Simplicial.SharpNormalForms.sharp_mk_face ι q x

private theorem vertexMap_comp_face {n k m : ℕ}
    (q : Fin (n + 1) → Fin (k + 1))
    (ι : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m) :
    vertexMap q ≫ toTop.map ι = vertexMap (ι.1.toOrderHom ∘ q) := by
  calc
    vertexMap q ≫ toTop.map ι = vertexMap q ≫ vertexMap ι.1.toOrderHom := by
      congr 1
    _ = vertexMap (ι.1.toOrderHom ∘ q) :=
      HomotopyHypothesis.Approximation.FiniteRealization.vertexMap_comp_proof q ι.1.toOrderHom

private theorem vertexMap_reduce {X : SemiSSet.{u}} {n k m : ℕ}
    (q : Fin (n + 1) → Fin (k + 1))
    (ι : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m)
    (x : stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ X) :
    vertexMap (ι.1.toOrderHom ∘ q) ≫ simplexChar x =
      vertexMap q ≫ simplexChar (Henry.SemiSSet.stdSimplex.map ι ≫ x) := by
  calc
    vertexMap (ι.1.toOrderHom ∘ q) ≫ simplexChar x =
        (vertexMap q ≫ toTop.map ι) ≫ simplexChar x := by
          rw [vertexMap_comp_face]
    _ = vertexMap q ≫ (toTop.map ι ≫ simplexChar x) := Category.assoc _ _ _
    _ = vertexMap q ≫ simplexChar (Henry.SemiSSet.stdSimplex.map ι ≫ x) := by
          rw [← HomotopyHypothesis.Gluing.Simplicial.simplexChar_stdSimplex_map]

/-- **Faces of normal forms.** -/
theorem sharp_normalForm_face_proof {X : SemiSSet.{u}} {n n' m m' : ℕ}
    (θ : Henry.SemiSimplexCategory.mk n' ⟶ Henry.SemiSimplexCategory.mk n)
    (v : Fin (n + 1) → Fin (m + 1)) (x : X.obj (op (Henry.SemiSimplexCategory.mk m)))
    (v' : Fin (n' + 1) → Fin (m' + 1))
    (x' : X.obj (op (Henry.SemiSimplexCategory.mk m')))
    (hv' : Function.Surjective v')
    (h : (sharp X).map θ.op (sharpMk v x) = sharpMk v' x') :
    ∃ ι : Henry.SemiSimplexCategory.mk m' ⟶ Henry.SemiSimplexCategory.mk m,
      v ∘ θ.1.toOrderHom = ι.1.toOrderHom ∘ v' ∧ X.map ι.op x = x' := by
  have hface : sharpMk (v ∘ θ.1.toOrderHom) x = sharpMk v' x' := by
    simpa only [HomotopyHypothesis.Simplicial.SharpNormalForms.sharp_map_mk] using h
  obtain ⟨k, q, ι, hq, hfactor, hred⟩ :=
    sharp_reduce (X := X) (v ∘ θ.1.toOrderHom) x
  have hnormal : sharpMk q (X.map ι.op x) = sharpMk v' x' := hred.symm.trans hface
  have hu := HomotopyHypothesis.Simplicial.SharpNormalForms.sharp_normalForm_unique_proof
    q v' (X.map ι.op x) x' hq hv' hnormal
  rcases hu with ⟨hk, hqv, hxx'⟩
  cases hk
  have hqv' : q = v' := eq_of_heq hqv
  have hxx' : X.map ι.op x = x' := eq_of_heq hxx'
  refine ⟨ι, ?_, hxx'⟩
  calc
    v ∘ θ.1.toOrderHom = ι.1.toOrderHom ∘ q := hfactor
    _ = ι.1.toOrderHom ∘ v' := by rw [hqv']

/-- Representatives of one formal simplex give the same affine realization map. -/
theorem vertexMap_simplexChar_eq_of_sharpMk_eq_proof {X : SemiSSet.{u}} {n m m' : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (x : stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ X)
    (v' : Fin (n + 1) → Fin (m' + 1))
    (x' : stdSimplex.obj (Henry.SemiSimplexCategory.mk m') ⟶ X)
    (h : sharpMk v (uliftYonedaEquiv x) = sharpMk v' (uliftYonedaEquiv x')) :
    vertexMap v ≫ simplexChar x = vertexMap v' ≫ simplexChar x' := by
  obtain ⟨k, q, ι, hq, hfactor, hred⟩ :=
    sharp_reduce (X := X) v (uliftYonedaEquiv x)
  obtain ⟨k', q', ι', hq', hfactor', hred'⟩ :=
    sharp_reduce (X := X) v' (uliftYonedaEquiv x')
  let y := X.map ι.op (uliftYonedaEquiv x)
  let y' := X.map ι'.op (uliftYonedaEquiv x')
  have hnormal : sharpMk q y = sharpMk q' y' := by
    calc
      sharpMk q y = sharpMk v (uliftYonedaEquiv x) := hred.symm
      _ = sharpMk v' (uliftYonedaEquiv x') := h
      _ = sharpMk q' y' := hred'
  have hu := HomotopyHypothesis.Simplicial.SharpNormalForms.sharp_normalForm_unique_proof
    q q' y y' hq hq' hnormal
  rcases hu with ⟨hk, hqq', hyy'⟩
  cases hk
  have hqq' : q = q' := eq_of_heq hqq'
  have hyy' : y = y' := eq_of_heq hyy'
  let x₀ : stdSimplex.obj (Henry.SemiSimplexCategory.mk k) ⟶ X :=
    uliftYonedaEquiv.symm y
  let x₀' : stdSimplex.obj (Henry.SemiSimplexCategory.mk k) ⟶ X :=
    uliftYonedaEquiv.symm y'
  have hx₀ : x₀ = Henry.SemiSSet.stdSimplex.map ι ≫ x := by
    dsimp [x₀, y]
    simpa [Henry.SemiSSet.stdSimplex] using
      (uliftYonedaEquiv_symm_map (F := X) ι.op (uliftYonedaEquiv x))
  have hx₀' : x₀' = Henry.SemiSSet.stdSimplex.map ι' ≫ x' := by
    dsimp [x₀', y']
    simpa [Henry.SemiSSet.stdSimplex] using
      (uliftYonedaEquiv_symm_map (F := X) ι'.op (uliftYonedaEquiv x'))
  have hx₀eq : x₀ = x₀' := congrArg uliftYonedaEquiv.symm hyy'
  have hreal : vertexMap v ≫ simplexChar x = vertexMap q ≫ simplexChar x₀ := by
    calc
      vertexMap v ≫ simplexChar x =
          vertexMap (ι.1.toOrderHom ∘ q) ≫ simplexChar x := by rw [hfactor]
      _ = vertexMap q ≫ simplexChar (Henry.SemiSSet.stdSimplex.map ι ≫ x) :=
        vertexMap_reduce q ι x
      _ = vertexMap q ≫ simplexChar x₀ := by rw [← hx₀]
  have hreal' : vertexMap v' ≫ simplexChar x' = vertexMap q' ≫ simplexChar x₀' := by
    calc
      vertexMap v' ≫ simplexChar x' =
          vertexMap (ι'.1.toOrderHom ∘ q') ≫ simplexChar x' := by rw [hfactor']
      _ = vertexMap q' ≫ simplexChar (Henry.SemiSSet.stdSimplex.map ι' ≫ x') :=
        vertexMap_reduce q' ι' x'
      _ = vertexMap q' ≫ simplexChar x₀' := by rw [← hx₀']
  calc
    vertexMap v ≫ simplexChar x = vertexMap q ≫ simplexChar x₀ := hreal
    _ = vertexMap q' ≫ simplexChar x₀' := by rw [hqq', hx₀eq]
    _ = vertexMap v' ≫ simplexChar x' := hreal'.symm

#print axioms HomotopyHypothesis.Simplicial.NormalForms.sharp_normalForm_face_proof
#print axioms HomotopyHypothesis.Simplicial.NormalForms.vertexMap_simplexChar_eq_of_sharpMk_eq_proof

end HomotopyHypothesis.Simplicial.NormalForms
