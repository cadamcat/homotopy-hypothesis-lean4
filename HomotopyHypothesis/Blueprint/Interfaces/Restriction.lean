import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Interfaces.AfinIotaMapInitial
import HomotopyHypothesis.Blueprint.Interfaces.AfinIotaMapIsPushout

/-!
# `restriction`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- The restriction functor `C.Model ⥤ Completion (A_fin)`, `M ↦ (A ↦ Hom(A, M))` (H:993). -/
abbrev restriction {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    C.Model ⥤ Completion.{u} (Afin C hC) :=
  restrictionAlong (Afin.ι hC) (afin_ι_map_initial hC) (afin_ι_map_isPushout hC)
