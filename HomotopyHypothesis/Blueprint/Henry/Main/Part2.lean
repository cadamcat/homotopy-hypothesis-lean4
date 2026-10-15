import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial

/-!
# `HomotopyHypothesis.Blueprint.Henry.Main`, part 2

Lines 78–85 of `HomotopyHypothesis.Blueprint.Henry.Main`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry

section Lemmas

variable {C : Type*} [Category C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  {D : Type*} [Category D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]
  {E : Type*} [Category E] [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]

theorem toTerminalCat_isCylinderMorphism :
    IsCylinderMorphism (toTerminalCat.{u} C) where
  map_cofibration _ _ _ _ := trivial
  map_initial _ _ := ⟨IsInitial.ofUniqueHom (fun _ => PUnit.unit) (fun _ _ => rfl)⟩
  map_isPushout _ _ _ _ _ _ _ _ _ _ := ⟨⟨rfl⟩, ⟨PushoutCocone.IsColimit.mk _ (fun _ => PUnit.unit)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ _ _ => rfl)⟩⟩
  map_weakEquivalence _ _ _ _ := trivial
