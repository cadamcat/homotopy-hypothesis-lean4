import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.CollarMap
import HomotopyHypothesis.Approximation.Zeeman.GlobalStars
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Transport of simplicial restrictions

Precomposition by a semi-simplicial map preserves coherent simpliciality.
A monomorphism identifies its source with its range, so a simplicial
restriction transports to that range. These facts apply to the retained
images of subdivisions and to the collar vertex map.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Characteristic maps commute with postcomposition of simplex maps. -/
theorem simplexChar_comp {A B : SemiSSet.{u}} {n : ℕ}
    (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ A) (ψ : A ⟶ B) :
    simplexChar (y ≫ ψ) = simplexChar y ≫ realization.map ψ := by
  unfold simplexChar realization
  rw [Functor.map_comp, Category.assoc]

/-- Coherent simpliciality is preserved by precomposition with a realized semi-simplicial map. -/
theorem isSimplicial_precomp_realization {A B M : SemiSSet.{u}} (ψ : A ⟶ B)
    (F : realization.obj B ⟶ realization.obj M) (hF : IsSimplicial F) :
    IsSimplicial (realization.map ψ ≫ F) := by
  obtain ⟨φ, hφ⟩ := hF
  refine ⟨ψ ≫ φ, ?_⟩
  intro n y
  obtain ⟨m, x, v, hsharp, htop⟩ := hφ n (y ≫ ψ)
  refine ⟨m, x, v, ?_, ?_⟩
  · change φ.app (op (Henry.SemiSimplexCategory.mk n))
      (ψ.app (op (Henry.SemiSimplexCategory.mk n)) (uliftYonedaEquiv y)) = _
    simpa only [uliftYonedaEquiv_comp] using hsharp
  · calc
      simplexChar y ≫ (realization.map ψ ≫ F) =
          (simplexChar y ≫ realization.map ψ) ≫ F := (Category.assoc _ _ _).symm
      _ = simplexChar (y ≫ ψ) ≫ F :=
        congrArg (fun e => e ≫ F) (simplexChar_comp y ψ).symm
      _ = vertexMap v ≫ simplexChar x := htop

/-- The inverse range identification followed by a monomorphism is its range inclusion. -/
theorem toRange_inv_comp {J W : SemiSSet.{u}} (j : J ⟶ W) [Mono j] :
    (asIso (Subfunctor.toRange j)).inv ≫ j = (Subfunctor.range j).ι := by
  let e := asIso (Subfunctor.toRange j)
  calc
    e.inv ≫ j = e.inv ≫ (e.hom ≫ (Subfunctor.range j).ι) :=
      congrArg (fun p => e.inv ≫ p) (Subfunctor.toRange_ι j).symm
    _ = (e.inv ≫ e.hom) ≫ (Subfunctor.range j).ι := (Category.assoc _ _ _).symm
    _ = (Subfunctor.range j).ι := by rw [e.inv_hom_id, Category.id_comp]

/-- A simplicial restriction along a monomorphism is simplicial on its range subcomplex. -/
theorem isSimplicial_range_restriction {J W M : SemiSSet.{u}} (j : J ⟶ W) [Mono j]
    (F : realization.obj W ⟶ realization.obj M)
    (hF : IsSimplicial (realization.map j ≫ F)) :
    IsSimplicial (realization.map (Subfunctor.range j).ι ≫ F) := by
  let e := asIso (Subfunctor.toRange j)
  have h := isSimplicial_precomp_realization e.inv (realization.map j ≫ F) hF
  have he : realization.map e.inv ≫ (realization.map j ≫ F) =
      realization.map (Subfunctor.range j).ι ≫ F := by
    rw [← Category.assoc, ← Functor.map_comp, toRange_inv_comp]
  rw [he] at h
  exact h

/-- A subdivision transports the original simplicial restriction to its retained image. -/
theorem isSimplicial_subdivision_retained {K M : SemiSSet.{u}} {L : Subfunctor K}
    (S : RelSubdivision K L) (f : realization.obj K ⟶ realization.obj M)
    (hL : IsSimplicial (realization.map L.ι ≫ f)) :
    IsSimplicial (realization.map (Subfunctor.range S.j).ι ≫ S.h.hom ≫ f) := by
  have : Mono S.j := S.mono_j
  apply isSimplicial_range_restriction S.j (S.h.hom ≫ f)
  rw [← Category.assoc, S.hj]
  exact hL

/-- Composing with the collar preserves the original simplicial restriction on its retained image. -/
theorem isSimplicial_collar_retained {K M : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K)
    (f : realization.obj K ⟶ realization.obj M)
    (hL : IsSimplicial (realization.map L.ι ≫ f)) :
    IsSimplicial (realization.map (Subfunctor.range (relativeDerivedInclusion hK L)).ι ≫
      relativeCollarMap hK L ≫ f) := by
  apply isSimplicial_range_restriction (relativeDerivedInclusion hK L) (relativeCollarMap hK L ≫ f)
  rw [← Category.assoc, relativeCollarMap_retained]
  exact hL

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.isSimplicial_precomp_realization
#print axioms HomotopyHypothesis.Approximation.Zeeman.isSimplicial_range_restriction
#print axioms HomotopyHypothesis.Approximation.Zeeman.isSimplicial_subdivision_retained
#print axioms HomotopyHypothesis.Approximation.Zeeman.isSimplicial_collar_retained
