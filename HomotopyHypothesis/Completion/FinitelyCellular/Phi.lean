import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Completion.FinitelyCellular.Afin
/-
# The inverse functor from the completion to models.

Restriction along the free functor `C.Obj ⥤ Afin` sends completion presheaves
(which take cofibration pushouts to pullbacks) to models (which take globular
sums to pullbacks), since free shapes send sums to cofibration pushouts.
-/

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Henry

noncomputable section

namespace HomotopyHypothesis.Completion.FinitelyCellular

universe u

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)

/-- The inverse functor `Completion (Afin) ⥤ C.Model`. -/
def Phi : Completion.{u} (Afin C hC) ⥤ C.Model where
  obj P :=
    { presheaf := (FreeAfin hC).op ⋙ P.obj
      sums := fun S b h hl hr => by
        have hpush := (freeAfin_attach_isPushout hC S b h hl hr).flip
        have hcof := freeAfin_face_cofibration hC hr
        exact (P.property.2 _ _ _ _ hpush hcof).flip }
  map η := ((Functor.whiskeringLeft _ _ _).obj (FreeAfin hC).op).map η.hom
  map_id _ := ((Functor.whiskeringLeft _ _ _).obj (FreeAfin hC).op).map_id _
  map_comp _ _ := ((Functor.whiskeringLeft _ _ _).obj (FreeAfin hC).op).map_comp _ _

end HomotopyHypothesis.Completion.FinitelyCellular
