import Mathlib.Data.Fin.Tuple.Basic
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.LocalEmbedding
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeDistributions
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
/-!
# Cones in relative derived subdivision

Appending an exterior simplex to a tuple of preceding subdivision vertices
preserves admissibility. A retained subtuple of the cone avoids the new
last vertex and therefore factors through the original tuple.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- An admissible tuple extends to a cone on any exterior simplex following all its entries. -/
theorem relativeAdmissible_snoc_exterior {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : Fin (n + 1) → RelativeVertex K L) (ha : RelativeAdmissible a)
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hs : ∀ i, RelativeVertex.Precedes (a i) (.inr s)) :
    RelativeAdmissible (Fin.snoc a (.inr s)) := by
  have hnot : Sum.inr s ∉ Set.range a := by
    rintro ⟨i, hi⟩
    have h := hs i
    rw [hi] at h
    exact (Nat.lt_irrefl s.val.1) h.1
  refine ⟨Fin.snoc_injective_of_injective ha.1 hnot, ?_, ?_⟩
  · intro i j hij
    induction i using Fin.lastCases with
    | last => exact ((not_lt_of_ge (Fin.le_last j)) hij).elim
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hs i
      | cast j =>
        simpa only [Fin.snoc_castSucc] using ha.2.1 i j hij
  · intro k θ w hw
    have havoid (i : Fin (k + 1)) : θ.hom.toOrderHom i ≠ Fin.last (n + 1) := by
      intro hi
      have h := hw i
      rw [hi, Fin.snoc_last] at h
      cases h
    have hlt (i : Fin (k + 1)) : (θ.hom.toOrderHom i).val < n + 1 :=
      Fin.lt_last_iff_ne_last.mpr (havoid i)
    let f : Fin (k + 1) →o Fin (n + 1) :=
      { toFun := fun i => ⟨(θ.hom.toOrderHom i).val, hlt i⟩
        monotone' := fun i j hij => θ.hom.toOrderHom.monotone hij }
    have hf : Function.Injective f := by
      intro i j hij
      apply SimplexCategory.mono_iff_injective.mp θ.property
      exact Fin.ext (congrArg (fun q : Fin (n + 1) => q.val) hij)
    let η : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n :=
      ⟨SimplexCategory.Hom.mk f, by
        change Mono (show SimplexCategory.mk k ⟶ SimplexCategory.mk n from
          SimplexCategory.Hom.mk f)
        rw [SimplexCategory.mono_iff_injective]
        exact hf⟩
    apply ha.2.2 k η w
    intro i
    change a (f i) = .inl (w i)
    have hcast : (f i).castSucc = θ.hom.toOrderHom i := Fin.ext rfl
    simpa only [Fin.snoc_castSucc] using
      (congrArg (Fin.snoc a (.inr s)) hcast).trans (hw i)

/-- The derived simplex obtained by coning an existing tuple to an exterior simplex. -/
def relativeCone {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hs : ∀ i, RelativeVertex.Precedes (a.val i) (.inr s)) :
    (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1))) :=
  ⟨Fin.snoc a.val (.inr s), relativeAdmissible_snoc_exterior a.val a.property s hs⟩

/-- The initial face of a cone is the original derived simplex. -/
theorem relativeCone_prefix {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hs : ∀ i, RelativeVertex.Precedes (a.val i) (.inr s)) :
    (relativeDerived K L).map (initialFace (Nat.le_succ n)).op (relativeCone a s hs) = a := by
  apply Subtype.ext
  funext i
  exact @Fin.snoc_castSucc (n + 1) (fun _ => RelativeVertex K L) (Sum.inr s) a.val i

/-- An exterior simplex gives a single subdivision vertex. -/
def relativeExteriorVertex {K : SemiSSet.{u}} {L : Subfunctor K}
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))}) :
    (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk 0)) :=
  ⟨fun _ => .inr s, by
    change RelativeAdmissible (fun _ : Fin 1 => (Sum.inr s : RelativeVertex K L))
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      omega
    · intro i j hij
      have hi := i.isLt
      have hj := j.isLt
      have hij' : i.val < j.val := hij
      omega
    · intro k θ w hw
      have h := hw 0
      cases h⟩

/-- Affine distributions commute with restriction to a derived face. -/
theorem relativeDistributionAffineMap_face {K : SemiSSet.{u}} {L : Subfunctor K}
    {n m : ℕ} (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    (relativeDistributionAffineMap a).comp (StdSimplex.affineMap θ.hom.toOrderHom) =
      relativeDistributionAffineMap ((relativeDerived K L).map θ.op a) := by
  apply StdSimplex.affineMap_ext
  intro i
  simp only [relativeDistributionAffineMap, ConvexSpace.AffineMap.comp_apply,
    Function.comp_apply, StdSimplex.coe_affineMap, StdSimplex.map_single,
    StdSimplex.affineMapMk_single]
  rfl

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeAdmissible_snoc_exterior
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCone_prefix
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeDistributionAffineMap_face
