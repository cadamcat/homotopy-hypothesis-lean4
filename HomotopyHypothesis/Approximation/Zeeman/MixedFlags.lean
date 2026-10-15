import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.HornAttachmentStatement
import HomotopyHypothesis.Approximation.Zeeman.RelativeComplex
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Mixed flags for a relative derived prism

The mixed complex contains original simplices and relative derived
simplices. Its tuples consist of original vertices in an original face,
followed by a strictly nested chain of exterior faces carrying that face.
The original and derived inclusions agree on the fixed subcomplex.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Original vertices and barycentres of faces outside the fixed subcomplex. -/
abbrev MixedVertex (K : SemiSSet.{u}) (L : Subfunctor K) :=
  K.obj (op (Henry.SemiSimplexCategory.mk 0)) ⊕
    {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))}

/-- The order and incidence conditions for consecutive mixed vertices. -/
def MixedVertex.Precedes {K : SemiSSet.{u}} {L : Subfunctor K} :
    MixedVertex K L → MixedVertex K L → Prop
  | .inl _, .inl _ => True
  | .inl v, .inr s => ∃ θ : Henry.SemiSimplexCategory.mk 0 ⟶
      Henry.SemiSimplexCategory.mk s.val.1, K.map θ.op s.val.2 = v
  | .inr _, .inl _ => False
  | .inr s, .inr t => s.val.1 < t.val.1 ∧
      ∃ θ : Henry.SemiSimplexCategory.mk s.val.1 ⟶
        Henry.SemiSimplexCategory.mk t.val.1, K.map θ.op t.val.2 = s.val.2

/-- A mixed flag has distinct vertices and an ordered original face as its prefix. -/
def MixedAdmissible {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : Fin (n + 1) → MixedVertex K L) : Prop :=
  Function.Injective a ∧
    (∀ i j : Fin (n + 1), i < j → MixedVertex.Precedes (a i) (a j)) ∧
    ∀ (m : ℕ) (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n)
      (w : Fin (m + 1) → K.obj (op (Henry.SemiSimplexCategory.mk 0))),
      (∀ i, a (θ.hom.toOrderHom i) = .inl (w i)) →
        ∃ x : K.obj (op (Henry.SemiSimplexCategory.mk m)), ∀ i, vertex x i = w i

private theorem mixedAdmissible_restrict {K : SemiSSet.{u}} {L : Subfunctor K}
    {n m : ℕ} {a : Fin (n + 1) → MixedVertex K L} (ha : MixedAdmissible a)
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    MixedAdmissible (a ∘ θ.hom.toOrderHom) := by
  have hθ : Function.Injective θ.hom.toOrderHom :=
    SimplexCategory.mono_iff_injective.mp θ.property
  refine ⟨ha.1.comp hθ, ?_, ?_⟩
  · intro i j hij
    exact ha.2.1 _ _ (θ.hom.toOrderHom.monotone.strictMono_of_injective hθ hij)
  · intro k η w hw
    exact ha.2.2 k (η ≫ θ) w hw

/-- The semi-simplicial complex of mixed original and derived flags. -/
def mixedFlags (K : SemiSSet.{u}) (L : Subfunctor K) : SemiSSet.{u} where
  obj X := {a : Fin (X.unop.obj.len + 1) → MixedVertex K L // MixedAdmissible a}
  map θ := ↾fun a =>
    ⟨a.val ∘ θ.unop.hom.toOrderHom, mixedAdmissible_restrict a.property θ.unop⟩
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem original_mixedAdmissible {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) {n : ℕ} (x : K.obj (op (Henry.SemiSimplexCategory.mk n))) :
    MixedAdmissible (fun i => Sum.inl (vertex x i) : Fin (n + 1) → MixedVertex K L) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Sum.inl_injective.comp (vertex_injective hK x)
  · intro i j hij
    trivial
  · intro m θ w hw
    exact ⟨K.map θ.op x, fun i => (vertex_map θ x i).trans (Sum.inl.inj (hw i))⟩

/-- The original end of the mixed prism. -/
def mixedOriginalInclusion {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) : K ⟶ mixedFlags K L where
  app X := ↾fun x => ⟨fun i => Sum.inl (vertex x i), original_mixedAdmissible hK L x⟩
  naturality X Y θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    funext i
    exact congrArg Sum.inl (vertex_map θ.unop x i)

/-- A relative derived vertex as a mixed vertex. -/
def relativeToMixedVertex {K : SemiSSet.{u}} {L : Subfunctor K} :
    RelativeVertex K L → MixedVertex K L
  | .inl v => .inl v.val
  | .inr s => .inr s

/-- Relative derived vertices embed into the mixed vertex set. -/
theorem relativeToMixedVertex_injective {K : SemiSSet.{u}} {L : Subfunctor K} :
    Function.Injective (relativeToMixedVertex (K := K) (L := L)) := by
  intro v w h
  cases v <;> cases w <;> simp only [relativeToMixedVertex, Sum.inl.injEq,
    Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at h ⊢
  · exact Subtype.ext h
  · exact h

private theorem derived_mixedAdmissible {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    MixedAdmissible (relativeToMixedVertex ∘ a.val) := by
  classical
  refine ⟨relativeToMixedVertex_injective.comp a.property.1, ?_, ?_⟩
  · intro i j hij
    have h := a.property.2.1 i j hij
    cases hi : a.val i <;> cases hj : a.val j <;>
      simpa only [Function.comp_apply, hi, hj, relativeToMixedVertex,
        MixedVertex.Precedes, RelativeVertex.Precedes] using h
  · intro m θ w hw
    have hz (i : Fin (m + 1)) :
        ∃ z : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0)),
          a.val (θ.hom.toOrderHom i) = .inl z ∧ z.val = w i := by
      have h := hw i
      cases he : a.val (θ.hom.toOrderHom i) with
      | inl v =>
        refine ⟨v, rfl, ?_⟩
        simp only [Function.comp_apply, he, relativeToMixedVertex] at h
        exact Sum.inl.inj h
      | inr s =>
        simp only [Function.comp_apply, he, relativeToMixedVertex, Sum.inr_ne_inl] at h
    choose z hz hv using hz
    obtain ⟨x, hx⟩ := a.property.2.2 m θ z hz
    refine ⟨x.val, ?_⟩
    intro i
    exact (congrArg Subtype.val (hx i)).trans (hv i)

/-- The relative derived end of the mixed prism. -/
def mixedDerivedInclusion {K : SemiSSet.{u}} (L : Subfunctor K) :
    relativeDerived K L ⟶ mixedFlags K L where
  app _ := ↾fun a => ⟨relativeToMixedVertex ∘ a.val, derived_mixedAdmissible a⟩
  naturality _ _ _ := rfl

instance mixedDerivedInclusion_mono {K : SemiSSet.{u}} (L : Subfunctor K) :
    Mono (mixedDerivedInclusion L) := by
  rw [NatTrans.mono_iff_mono_app]
  intro X
  rw [mono_iff_injective]
  intro a b h
  apply Subtype.ext
  funext i
  exact relativeToMixedVertex_injective (congrArg (fun q => q.val i) h)

instance mixedOriginalInclusion_mono {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) : Mono (mixedOriginalInclusion hK L) := by
  rw [NatTrans.mono_iff_mono_app]
  intro X
  rw [mono_iff_injective]
  intro x y h
  apply simplex_eq_of_vertex_eq hK
  funext i
  exact Sum.inl.inj (congrArg (fun q => q.val i) h)

/-- Both ends of the mixed prism retain the same copy of the fixed subcomplex. -/
theorem mixedInclusions_agree {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) :
    relativeDerivedInclusion hK L ≫ mixedDerivedInclusion L =
      L.ι ≫ mixedOriginalInclusion hK L := rfl

/-- A mixed prism over a finite complex has finitely many simplices. -/
theorem mixedFlags_isFinite {K : SemiSSet.{u}} (hK : K.IsFinite) (L : Subfunctor K) :
    (mixedFlags K L).IsFinite := by
  haveI : Finite (Simplex K) := simplex_finite hK
  haveI : Finite (K.obj (op (Henry.SemiSimplexCategory.mk 0))) := hK.1 0
  haveI : Finite (MixedVertex K L) := by
    dsimp only [MixedVertex]
    infer_instance
  letI : Fintype (MixedVertex K L) := Fintype.ofFinite _
  refine ⟨?_, ⟨Fintype.card (MixedVertex K L), ?_⟩⟩
  · intro n
    change Finite {a : Fin (n + 1) → MixedVertex K L // MixedAdmissible a}
    infer_instance
  intro n hn
  refine ⟨fun a => ?_⟩
  have hc := Fintype.card_le_of_injective a.val a.property.1
  simp only [Fintype.card_fin] at hc
  omega

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedDerivedInclusion_mono
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedInclusions_agree
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedFlags_isFinite
