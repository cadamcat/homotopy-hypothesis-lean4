import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# The derived end inside the mixed prism

A mixed flag belongs to the derived end precisely when every subtuple of
original vertices is the ordered vertex tuple of a face in the fixed
subcomplex. In particular, a flag outside that end has an original vertex.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Every original subtuple of a mixed flag is a face of the fixed subcomplex. -/
def MixedOriginalFacesIn {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n))) : Prop :=
  ∀ (m : ℕ) (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n)
    (w : Fin (m + 1) → K.obj (op (Henry.SemiSimplexCategory.mk 0))),
    (∀ i, a.val (θ.hom.toOrderHom i) = .inl (w i)) →
      ∃ x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk m)),
        ∀ i, vertex x.val i = w i

/-- The relative and mixed incidence predicates agree on relative vertices. -/
theorem relativePrecedes_iff_mixed {K : SemiSSet.{u}} {L : Subfunctor K}
    (v w : RelativeVertex K L) :
    RelativeVertex.Precedes v w ↔
      MixedVertex.Precedes (relativeToMixedVertex v) (relativeToMixedVertex w) := by
  cases v <;> cases w <;> rfl

/-- Original vertices of a flag satisfying the fixed-face condition belong to the subcomplex. -/
theorem mixedOriginalVertex_mem_of_facesIn {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : MixedOriginalFacesIn a) (i : Fin (n + 1))
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) (hi : a.val i = .inl w) :
    w ∈ L.obj (op (Henry.SemiSimplexCategory.mk 0)) := by
  obtain ⟨x, hx⟩ := ha 0 (vertexInclusion i) (fun _ => w) (fun _ => hi)
  have h : x.val = w := (vertex_zero x.val).symm.trans (hx 0)
  exact h ▸ x.property

/-- The derived-end image is characterized by its original subtuples. -/
theorem mixedDerived_mem_range_iff {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    a ∈ Set.range ((mixedDerivedInclusion L).app (op (Henry.SemiSimplexCategory.mk n))) ↔
      MixedOriginalFacesIn a := by
  classical
  constructor
  · rintro ⟨b, rfl⟩ m θ w hw
    have hz (i : Fin (m + 1)) :
        ∃ z : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0)),
          b.val (θ.hom.toOrderHom i) = .inl z ∧ z.val = w i := by
      have h := hw i
      cases he : b.val (θ.hom.toOrderHom i) with
      | inl v =>
        refine ⟨v, rfl, ?_⟩
        change relativeToMixedVertex (b.val (θ.hom.toOrderHom i)) = .inl (w i) at h
        simpa only [he, relativeToMixedVertex, Sum.inl.injEq] using h
      | inr s =>
        change relativeToMixedVertex (b.val (θ.hom.toOrderHom i)) = .inl (w i) at h
        simp only [he, relativeToMixedVertex, Sum.inr_ne_inl] at h
    choose z hz hv using hz
    obtain ⟨x, hx⟩ := b.property.2.2 m θ z hz
    exact ⟨x, fun i => (congrArg Subtype.val (hx i)).trans (hv i)⟩
  · intro ha
    have hv (i : Fin (n + 1)) : ∃ v : RelativeVertex K L,
        relativeToMixedVertex v = a.val i := by
      cases he : a.val i with
      | inl w =>
        exact ⟨.inl ⟨w, mixedOriginalVertex_mem_of_facesIn a ha i w he⟩, rfl⟩
      | inr s => exact ⟨.inr s, rfl⟩
    choose b hb using hv
    have had : RelativeAdmissible b := by
      refine ⟨?_, ?_, ?_⟩
      · intro i j hij
        apply a.property.1
        exact (hb i).symm.trans ((congrArg relativeToMixedVertex hij).trans (hb j))
      · intro i j hij
        apply (relativePrecedes_iff_mixed (b i) (b j)).mpr
        rw [hb i, hb j]
        exact a.property.2.1 i j hij
      · intro m θ w hw
        have hs (i : Fin (m + 1)) : a.val (θ.hom.toOrderHom i) = .inl (w i).val :=
          (hb (θ.hom.toOrderHom i)).symm.trans (congrArg relativeToMixedVertex (hw i))
        obtain ⟨x, hx⟩ := ha m θ (fun i => (w i).val) hs
        exact ⟨x, fun i => Subtype.ext (hx i)⟩
    refine ⟨⟨b, had⟩, ?_⟩
    apply Subtype.ext
    funext i
    exact hb i

/-- A mixed flag outside the derived end has a nonempty original prefix. -/
theorem exists_original_of_not_in_derived {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : a ∉ Set.range
      ((mixedDerivedInclusion L).app (op (Henry.SemiSimplexCategory.mk n)))) :
    ∃ (i : Fin (n + 1)) (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))),
      a.val i = .inl w := by
  classical
  by_contra hn
  apply ha
  apply (mixedDerived_mem_range_iff a).mpr
  intro m θ w hw
  exact (hn ⟨θ.hom.toOrderHom 0, w 0, hw 0⟩).elim

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedDerived_mem_range_iff
#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_original_of_not_in_derived
