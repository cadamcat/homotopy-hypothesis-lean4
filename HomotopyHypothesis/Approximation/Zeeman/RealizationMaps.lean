import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Descending compatible maps from topological simplices

The adjunction defining realization turns a compatible family of maps from
topological simplices into a map on realization. Characteristic maps determine
that descended map.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The realization adjunction for semi-simplicial sets. -/
noncomputable def realizationAdjunction :
    realization.{u} ⊣ Presheaf.restrictedULiftYoneda.{u, 0, u, 0, u + 1} toTop.{u} :=
  Presheaf.uliftYonedaAdjunction.{u, 0, u, 0, u + 1}
    (Henry.SemiSSet.stdSimplex.{u}.leftKanExtension toTop.{u})
    (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u})

/-- The realization adjunction evaluates a map by its characteristic-map composites. -/
theorem realizationAdjunction_homEquiv_app {Y : SemiSSet.{u}} {T : TopCat.{u}}
    (f : realization.obj Y ⟶ T) {n : ℕ}
    (a : Y.obj (op (Henry.SemiSimplexCategory.mk n))) :
    ((realizationAdjunction.homEquiv Y T) f).app _ a =
      ULift.up (simplexChar (uliftYonedaEquiv.symm a) ≫ f) := by
  have h := Presheaf.uliftYonedaAdjunction_homEquiv_app.{u, 0, u, 0, u + 1}
      (L := Henry.SemiSSet.stdSimplex.{u}.leftKanExtension toTop.{u})
      (α := Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}) f a
  refine h.trans (congrArg ULift.up ?_)
  exact (Category.assoc _ _ _).symm

/-- Descend a compatible family of continuous maps from standard simplices. -/
noncomputable def realizationDesc {Y : SemiSSet.{u}} {T : TopCat.{u}}
    (φ : Y ⟶ (Presheaf.restrictedULiftYoneda.{u, 0, u, 0, u + 1} toTop.{u}).obj T) :
    realization.obj Y ⟶ T :=
  (realizationAdjunction.homEquiv Y T).symm φ

/-- The descended map restricts to the given map on each simplex. -/
theorem simplexChar_realizationDesc {Y : SemiSSet.{u}} {T : TopCat.{u}}
    (φ : Y ⟶ (Presheaf.restrictedULiftYoneda.{u, 0, u, 0, u + 1} toTop.{u}).obj T)
    {n : ℕ} (a : Y.obj (op (Henry.SemiSimplexCategory.mk n))) :
    simplexChar (uliftYonedaEquiv.symm a) ≫ realizationDesc φ =
      (φ.app (op (Henry.SemiSimplexCategory.mk n)) a).down := by
  have h := congrArg (fun ψ => ψ.app (op (Henry.SemiSimplexCategory.mk n)) a)
    ((realizationAdjunction.homEquiv Y T).apply_symm_apply φ)
  rw [realizationAdjunction_homEquiv_app] at h
  exact congrArg ULift.down h

/-- Maps from realization are determined by their composites with characteristic maps. -/
theorem realization_hom_ext {Y : SemiSSet.{u}} {T : TopCat.{u}}
    (f g : realization.obj Y ⟶ T)
    (h : ∀ (n : ℕ) (a : Y.obj (op (Henry.SemiSimplexCategory.mk n))),
      simplexChar (uliftYonedaEquiv.symm a) ≫ f =
        simplexChar (uliftYonedaEquiv.symm a) ≫ g) : f = g := by
  apply (realizationAdjunction.homEquiv Y T).injective
  ext X a
  change ((realizationAdjunction.homEquiv Y T) f).app
    (op (Henry.SemiSimplexCategory.mk X.unop.obj.len)) a =
    ((realizationAdjunction.homEquiv Y T) g).app
      (op (Henry.SemiSimplexCategory.mk X.unop.obj.len)) a
  rw [realizationAdjunction_homEquiv_app, realizationAdjunction_homEquiv_app]
  exact congrArg ULift.up (h X.unop.obj.len a)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.simplexChar_realizationDesc
#print axioms HomotopyHypothesis.Approximation.Zeeman.realization_hom_ext
