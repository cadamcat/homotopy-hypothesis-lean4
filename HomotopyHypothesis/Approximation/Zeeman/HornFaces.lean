import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.MixedCells
import HomotopyHypothesis.Approximation.Zeeman.MixedDeletion
import HomotopyHypothesis.Approximation.Zeeman.MixedFaceOrder
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.MixedOriginalPrefix
import HomotopyHypothesis.Approximation.Zeeman.MixedPairInsertionStatement
import HomotopyHypothesis.Approximation.Zeeman.MixedPairing
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Faces excluded from a horn

In an embedded simplex, a horn contains every face except the whole
simplex and the codimension-one face opposite its missing vertex. For a
mixed upper cell, these two excluded simplices are its upper and lower
pair members.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A face outside a horn is the whole simplex or the full omission face. -/
theorem not_horn_face_eq {X : SemiSSet.{u}} {n m : ℕ}
    (x : X.obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk (n + 1))
    (k : Fin (n + 2))
    (hθ : ULift.up θ ∉ (horn.{u} (n + 1) k).obj (op (Henry.SemiSimplexCategory.mk m))) :
    (⟨m, X.map θ.op x⟩ : Simplex X) = ⟨n + 1, x⟩ ∨
      (⟨m, X.map θ.op x⟩ : Simplex X) = ⟨n, X.map (faceOmitting k).op x⟩ := by
  classical
  have hcover (j : Fin (n + 2)) (hj : j ≠ k) : j ∈ Set.range θ.hom.toOrderHom := by
    by_contra hmiss
    exact hθ ⟨j, hj, hmiss⟩
  haveI : Mono θ.hom := θ.property
  by_cases hk : k ∈ Set.range θ.hom.toOrderHom
  · have hsurj : Function.Surjective θ.hom.toOrderHom := by
      intro j
      by_cases hj : j = k
      · exact hj.symm ▸ hk
      · exact hcover j hj
    have hdim : m = n + 1 := by
      have hc := Fintype.card_congr (Equiv.ofBijective θ.hom.toOrderHom
        ⟨SimplexCategory.mono_iff_injective.mp θ.property, hsurj⟩)
      simp only [Fintype.card_fin] at hc
      omega
    exact Or.inl (simplex_eq_of_face_dimension_eq θ rfl hdim)
  · have hmiss (i) : θ.hom.toOrderHom i ≠ k := by
      intro hi
      exact hk ⟨i, hi⟩
    obtain ⟨η, hη⟩ := exists_faceFactorOmitting θ k hmiss
    haveI : Mono η.hom := η.property
    have hsurj : Function.Surjective η.hom.toOrderHom := by
      intro j
      obtain ⟨i, hi⟩ := hcover (k.succAbove j) (Fin.succAbove_ne k j)
      refine ⟨i, ?_⟩
      apply (Fin.succAboveOrderEmb k).injective
      have he := congrArg (fun f => f.hom.toOrderHom i) hη
      change k.succAbove (η.hom.toOrderHom i) = θ.hom.toOrderHom i at he
      exact he.trans hi
    have hdim : m = n := by
      have hc := Fintype.card_congr (Equiv.ofBijective η.hom.toOrderHom
        ⟨SimplexCategory.mono_iff_injective.mp η.property, hsurj⟩)
      simp only [Fintype.card_fin] at hc
      omega
    have hmap : X.map η.op (X.map (faceOmitting k).op x) = X.map θ.op x := by
      have he := congrArg (fun f => X.map f.op x) hη
      rw [op_comp, Functor.map_comp] at he
      exact he
    refine Or.inr ?_
    rw [← hmap]
    exact simplex_eq_of_face_dimension_eq η rfl hdim

/-- Distinct vertices identify face maps from equality of the restricted simplex. -/
theorem faceMap_eq_of_vertex_injective {X : SemiSSet.{u}} {n m : ℕ}
    (x : X.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hx : Function.Injective (vertex x))
    (θ η : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n)
    (h : X.map θ.op x = X.map η.op x) : θ = η := by
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  apply hx
  rw [← vertex_map θ x i, ← vertex_map η x i, h]

/-- In an embedded simplex, a face belongs to the horn precisely when it is neither excluded cell. -/
theorem horn_face_iff_ne {X : SemiSSet.{u}} {n m : ℕ}
    (x : X.obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (hx : Function.Injective (vertex x))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk (n + 1))
    (k : Fin (n + 2)) :
    ULift.up θ ∈ (horn.{u} (n + 1) k).obj (op (Henry.SemiSimplexCategory.mk m)) ↔
      (⟨m, X.map θ.op x⟩ : Simplex X) ≠ ⟨n + 1, x⟩ ∧
      (⟨m, X.map θ.op x⟩ : Simplex X) ≠ ⟨n, X.map (faceOmitting k).op x⟩ := by
  classical
  constructor
  · rintro ⟨j, hjk, hjmiss⟩
    constructor
    · intro he
      have hdim : m = n + 1 := congrArg Sigma.fst he
      subst m
      haveI : Mono θ.hom := θ.property
      have hid : θ = 𝟙 _ := by
        apply WideSubcategory.hom_ext
        exact SimplexCategory.eq_id_of_mono θ.hom
      exact hjmiss ⟨j, by rw [hid]; rfl⟩
    · intro he
      have hdim : m = n := congrArg Sigma.fst he
      subst m
      have he' : X.map θ.op x = X.map (faceOmitting k).op x :=
        eq_of_heq (Sigma.mk.inj he).2
      have heq := faceMap_eq_of_vertex_injective x hx θ (faceOmitting k) he'
      rw [heq] at hjmiss
      have hjrange : j ∈ Set.range (faceOmitting k).hom.toOrderHom := by
        change j ∈ Set.range k.succAbove
        simpa only [Fin.range_succAbove, Set.mem_compl_iff, Set.mem_singleton_iff] using hjk
      exact hjmiss hjrange
  · rintro ⟨hfull, homit⟩
    by_contra hθ
    rcases not_horn_face_eq x θ k hθ with he | he
    · exact hfull he
    · exact homit he

/-- A face of a mixed upper cell lies in its attachment horn exactly when it is neither pair member. -/
theorem mixedUpper_horn_face_iff {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (c : MixedLowerCell K L) {m : ℕ}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk (c.val.1 + 1)) :
    ULift.up θ ∈ (horn.{u} (c.val.1 + 1) c.prefix.last.succ).obj
      (op (Henry.SemiSimplexCategory.mk m)) ↔
      (⟨m, (mixedFlags K L).map θ.op (mixedUpper hI hK c)⟩ :
        Simplex (mixedFlags K L)) ≠ mixedUpperSimplex hI hK c ∧
      (⟨m, (mixedFlags K L).map θ.op (mixedUpper hI hK c)⟩ :
        Simplex (mixedFlags K L)) ≠ c.val := by
  have h := horn_face_iff_ne (mixedUpper hI hK c)
    (mixed_vertex_injective (mixedUpper hI hK c)) θ c.prefix.last.succ
  change _ ↔ _ ∧ (⟨m, (mixedFlags K L).map θ.op (mixedUpper hI hK c)⟩ :
    Simplex (mixedFlags K L)) ≠
      ⟨c.val.1, mixedOmit (mixedUpper hI hK c) c.prefix.last.succ⟩ at h
  rwa [mixedUpper_omit] at h

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.horn_face_iff_ne
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedUpper_horn_face_iff
