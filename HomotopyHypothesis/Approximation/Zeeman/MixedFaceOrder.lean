import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.MixedDeletion
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.MixedOriginalPrefix
import HomotopyHypothesis.Approximation.Zeeman.MixedPairInsertionStatement
import HomotopyHypothesis.Approximation.Zeeman.MixedPairing
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Ordering pairs of mixed cells by faces

Face restriction can only decrease the original-prefix dimension. When
that dimension is unchanged, a lower cell that is a face of an upper
partner factors through its lower partner: its absent prefix barycentre
forces the face map to omit the inserted vertex. These comparisons order
the pairs by prefix dimension and then by lower-cell dimension.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- An injective face map missing a vertex factors through its omission face. -/
theorem exists_faceFactorOmitting {n m : ℕ}
    (θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk (m + 1))
    (k : Fin (m + 2)) (hk : ∀ i, θ.hom.toOrderHom i ≠ k) :
    ∃ η : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk m,
      η ≫ faceOmitting k = θ := by
  let η := SimplexCategory.factor_δ θ.hom k
  have hη : η ≫ SimplexCategory.δ k = θ.hom :=
    SimplexCategory.factor_δ_spec θ.hom k hk
  haveI : Mono θ.hom := θ.property
  have hmono : Mono η := mono_of_mono_fac hη
  refine ⟨⟨η, hmono⟩, ?_⟩
  apply WideSubcategory.hom_ext
  exact hη

/-- A face inclusion between simplices of equal dimension identifies them. -/
theorem simplex_eq_of_face_dimension_eq {K : SemiSSet.{u}} {n m : ℕ}
    {x : K.obj (op (Henry.SemiSimplexCategory.mk n))}
    {y : K.obj (op (Henry.SemiSimplexCategory.mk m))}
    (θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk m)
    (hθ : K.map θ.op y = x) (hn : n = m) :
    (⟨n, x⟩ : Simplex K) = ⟨m, y⟩ := by
  subst m
  haveI : Mono θ.hom := θ.property
  have hid : θ = 𝟙 _ := by
    apply WideSubcategory.hom_ext
    exact SimplexCategory.eq_id_of_mono θ.hom
  rw [hid] at hθ
  simp only [op_id, Functor.map_id_apply] at hθ
  exact congrArg (fun z => (⟨n, z⟩ : Simplex K)) hθ.symm

/-- A face of a mixed flag has its original prefix carried by the larger flag's prefix. -/
theorem mixedOriginalPrefix_faceMap_of_face {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n m : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (b : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk m)))
    (p : MixedOriginalPrefix a) (q : MixedOriginalPrefix b)
    (θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk m)
    (hθ : (mixedFlags K L).map θ.op b = a) :
    ∃! η : Henry.SemiSimplexCategory.mk p.last.val ⟶ Henry.SemiSimplexCategory.mk q.last.val,
      K.map η.op q.face = p.face := by
  apply (vertex_range_subset_iff_existsUnique_faceMap hK p.face q.face).mp
  rintro v ⟨i, rfl⟩
  have he : b.val (θ.hom.toOrderHom ((initialSegmentInclusion p.last).hom.toOrderHom i)) =
      Sum.inl (vertex p.face i) := by
    have he := congrArg (fun z => z.val ((initialSegmentInclusion p.last).hom.toOrderHom i)) hθ
    exact he.trans (p.vertices i)
  have hi := (q.maximal _).mp ⟨vertex p.face i, he⟩
  let j : Fin (q.last.val + 1) :=
    ⟨(θ.hom.toOrderHom ((initialSegmentInclusion p.last).hom.toOrderHom i)).val, by
      have hi' : (θ.hom.toOrderHom
        ((initialSegmentInclusion p.last).hom.toOrderHom i)).val ≤ q.last.val := hi
      omega⟩
  have hj : (initialSegmentInclusion q.last).hom.toOrderHom j =
      θ.hom.toOrderHom ((initialSegmentInclusion p.last).hom.toOrderHom i) := by
    apply Fin.ext
    rfl
  exact ⟨j, Sum.inl.inj ((q.vertices j).symm.trans ((congrArg b.val hj).trans he))⟩

/-- The original-prefix dimension does not increase under face restriction. -/
theorem mixedOriginalPrefix_dim_le_of_face {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n m : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (b : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk m)))
    (p : MixedOriginalPrefix a) (q : MixedOriginalPrefix b)
    (θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk m)
    (hθ : (mixedFlags K L).map θ.op b = a) : p.last.val ≤ q.last.val := by
  obtain ⟨η, _, _⟩ := mixedOriginalPrefix_faceMap_of_face hK a b p q θ hθ
  haveI : Mono η.hom := η.property
  exact SimplexCategory.len_le_of_mono η.hom

/-- At equal prefix dimension, face restriction preserves the original prefix simplex. -/
theorem mixedOriginalPrefix_simplex_eq_of_face_dim_eq {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n m : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (b : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk m)))
    (p : MixedOriginalPrefix a) (q : MixedOriginalPrefix b)
    (θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk m)
    (hθ : (mixedFlags K L).map θ.op b = a) (hd : p.last.val = q.last.val) :
    (⟨p.last.val, p.face⟩ : Simplex K) = ⟨q.last.val, q.face⟩ := by
  obtain ⟨η, hη, _⟩ := mixedOriginalPrefix_faceMap_of_face hK a b p q θ hθ
  exact simplex_eq_of_face_dimension_eq η hη hd

/-- At equal prefix dimension, a lower face of an upper cell is a face of its lower partner. -/
theorem mixedLower_face_upper_factors {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (c d : MixedLowerCell K L)
    (θ : Henry.SemiSimplexCategory.mk c.val.1 ⟶
      Henry.SemiSimplexCategory.mk (d.val.1 + 1))
    (hθ : (mixedFlags K L).map θ.op (mixedUpper hI hK d) = c.val.2)
    (hd : c.prefix.last.val = d.prefix.last.val) :
    ∃ η : Henry.SemiSimplexCategory.mk c.val.1 ⟶ Henry.SemiSimplexCategory.mk d.val.1,
      (mixedFlags K L).map η.op d.val.2 = c.val.2 := by
  have hbary : c.barycenter = d.barycenter := by
    apply congrArg Sum.inr
    apply Subtype.ext
    exact mixedOriginalPrefix_simplex_eq_of_face_dim_eq hK c.val.2
      (mixedUpper hI hK d) c.prefix (mixedUpperPrefix hI hK d) θ hθ hd
  have hmiss (i) : θ.hom.toOrderHom i ≠ d.prefix.last.succ := by
    intro hi
    have he : (mixedUpper hI hK d).val (θ.hom.toOrderHom i) = c.val.2.val i :=
      congrArg (fun z => z.val i) hθ
    rw [hi, mixedUpper_barycenter] at he
    exact c.barycenter_absent ⟨i, he.symm.trans hbary.symm⟩
  obtain ⟨η, hη⟩ := exists_faceFactorOmitting θ d.prefix.last.succ hmiss
  refine ⟨η, ?_⟩
  rw [← hη, op_comp, Functor.map_comp] at hθ
  change (mixedFlags K L).map η.op
    (mixedOmit (mixedUpper hI hK d) d.prefix.last.succ) = c.val.2 at hθ
  rwa [mixedUpper_omit] at hθ

/-- A lower face at equal prefix dimension has no larger dimension; equality identifies its pair. -/
theorem mixedLower_face_upper_dim {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (c d : MixedLowerCell K L)
    (θ : Henry.SemiSimplexCategory.mk c.val.1 ⟶
      Henry.SemiSimplexCategory.mk (d.val.1 + 1))
    (hθ : (mixedFlags K L).map θ.op (mixedUpper hI hK d) = c.val.2)
    (hd : c.prefix.last.val = d.prefix.last.val) :
    c.val.1 ≤ d.val.1 ∧ (c.val.1 = d.val.1 → c = d) := by
  obtain ⟨η, hη⟩ := mixedLower_face_upper_factors hI hK c d θ hθ hd
  haveI : Mono η.hom := η.property
  refine ⟨SimplexCategory.len_le_of_mono η.hom, ?_⟩
  intro he
  apply Subtype.ext
  exact simplex_eq_of_face_dimension_eq η hη he

/-- An upper face has no larger lower-partner dimension; equality identifies its pair. -/
theorem mixedUpper_face_upper_dim {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (c d : MixedLowerCell K L)
    (θ : Henry.SemiSimplexCategory.mk (c.val.1 + 1) ⟶
      Henry.SemiSimplexCategory.mk (d.val.1 + 1))
    (hθ : (mixedFlags K L).map θ.op (mixedUpper hI hK d) = mixedUpper hI hK c) :
    c.val.1 ≤ d.val.1 ∧ (c.val.1 = d.val.1 → c = d) := by
  haveI : Mono θ.hom := θ.property
  have hdim : c.val.1 + 1 ≤ d.val.1 + 1 := SimplexCategory.len_le_of_mono θ.hom
  refine ⟨by omega, ?_⟩
  intro he
  apply mixedUpperSimplex_injective hI hK
  exact simplex_eq_of_face_dimension_eq θ hθ (congrArg (fun n => n + 1) he)

/-- A pair represented by a face of an upper cell precedes that pair in lexicographic order. -/
theorem mixedPair_face_order {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (c d : MixedLowerCell K L)
    (hf : (∃ θ : Henry.SemiSimplexCategory.mk c.val.1 ⟶
        Henry.SemiSimplexCategory.mk (d.val.1 + 1),
        (mixedFlags K L).map θ.op (mixedUpper hI hK d) = c.val.2) ∨
      (∃ θ : Henry.SemiSimplexCategory.mk (c.val.1 + 1) ⟶
        Henry.SemiSimplexCategory.mk (d.val.1 + 1),
        (mixedFlags K L).map θ.op (mixedUpper hI hK d) = mixedUpper hI hK c)) :
    c.prefix.last.val < d.prefix.last.val ∨
      (c.prefix.last.val = d.prefix.last.val ∧ c.val.1 ≤ d.val.1 ∧
        (c.val.1 = d.val.1 → c = d)) := by
  rcases hf with ⟨θ, hθ⟩ | ⟨θ, hθ⟩
  · have hp := mixedOriginalPrefix_dim_le_of_face hK c.val.2 (mixedUpper hI hK d)
      c.prefix (mixedUpperPrefix hI hK d) θ hθ
    rcases lt_or_eq_of_le hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr ⟨hp, mixedLower_face_upper_dim hI hK c d θ hθ hp⟩
  · have hp := mixedOriginalPrefix_dim_le_of_face hK (mixedUpper hI hK c)
      (mixedUpper hI hK d) (mixedUpperPrefix hI hK c) (mixedUpperPrefix hI hK d) θ hθ
    rcases lt_or_eq_of_le hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr ⟨hp, mixedUpper_face_upper_dim hI hK c d θ hθ⟩

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedLower_face_upper_factors
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedPair_face_order
