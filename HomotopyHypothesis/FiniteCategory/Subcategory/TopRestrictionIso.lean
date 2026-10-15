import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Blueprint.Interfaces.CellularRealization
import HomotopyHypothesis.Blueprint.Interfaces.Restriction
noncomputable section

namespace HomotopyHypothesis.FiniteCategory.Subcategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Blueprint.Packages
open HomotopyHypothesis.Henry

theorem topRestriction_iso_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    (R : OAIRealization C) (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi) :
    Nonempty (topRestriction (cellularRealization hC R L adj) ≅ R.Pi ⋙ restriction hC) := by
  let G := Afin.ι hC ⋙ L
  let source : TopCat.{u} ⥤ (Afin C hC)ᵒᵖ ⥤ Type u :=
    yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj G.op
  let target : TopCat.{u} ⥤ (Afin C hC)ᵒᵖ ⥤ Type u :=
    R.Pi ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Afin.ι hC).op
  let hAdj : ∀ X : TopCat.{u}, source.obj X ≅
      (yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Afin.ι hC).op).obj (R.Pi.obj X) :=
    fun X => NatIso.ofComponents
      (fun A => (adj.homEquiv ((Afin.ι hC).obj A.unop) X).toIso)
      (by
        intro A B f
        ext g
        simpa [source, G] using
          (adj.homEquiv_naturality_left ((Afin.ι hC).map f.unop) g))
  let eta : source ≅ target :=
    NatIso.ofComponents hAdj (by
      intro X Y f
      ext A g
      simpa [hAdj, source, target] using
        (adj.homEquiv_naturality_right
          (g : L.obj ((Afin.ι hC).obj A.unop) ⟶ X) f))
  let P : ObjectProperty ((Afin C hC)ᵒᵖ ⥤ Type u) := IsCompletionPresheaf (Afin C hC)
  refine ⟨?_⟩
  refine NatIso.ofComponents (fun X => P.isoMk (eta.app X)) ?_
  intro X Y f
  apply P.hom_ext
  change source.map f ≫ eta.hom.app Y = eta.hom.app X ≫ target.map f
  exact eta.hom.naturality f

#print axioms topRestriction_iso_proof

end HomotopyHypothesis.FiniteCategory.Subcategory
