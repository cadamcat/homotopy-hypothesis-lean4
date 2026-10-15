import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.FiniteCategory.Subcategory.AfinMapIsPushout

/-!
# `afin_ι_map_isPushout`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- The inclusion `A_fin ⥤ C.Model` preserves pushouts along finite boundary-cell maps (`A_fin` is
closed under such pushouts in `C.Model`). -/
theorem afin_ι_map_isPushout {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    ∀ ⦃A B X Q : Afin C hC⦄ (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ Q) (j : X ⟶ Q),
      IsPushout i f k j → cofibrations (Afin C hC) i →
      IsPushout ((Afin.ι hC).map i) ((Afin.ι hC).map f) ((Afin.ι hC).map k)
        ((Afin.ι hC).map j) := _root_.HomotopyHypothesis.FiniteCategory.Subcategory.afin_ι_map_isPushout_proof ..
