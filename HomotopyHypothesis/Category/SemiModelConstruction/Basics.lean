import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelConstruction

open Henry

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

def terminalCompletion : Completion.{w} C :=
  ⟨(Functor.const Cᵒᵖ).obj PUnit, ⟨fun _ _ => ⟨by change Unique PUnit; infer_instance⟩, by
    intro A B X Q i f k j h hi
    exact IsPullback.of_id_fst⟩⟩

def terminalCompletion_isTerminal : IsTerminal (terminalCompletion (C := C)) :=
  IsTerminal.ofUniqueHom
    (fun X => ObjectProperty.homMk
      { app := fun _ => ↾fun _ => PUnit.unit
        naturality := by intros; rfl })
    (by intro X f; ext A a; change (_ : PUnit) = _; exact Subsingleton.elim _ _)

theorem terminal_values_subsingleton {T : Completion.{w} C} (hT : IsTerminal T)
    (A : C) : Subsingleton (T.obj.obj (op A)) := by
  let e := hT.uniqueUpToIso (terminalCompletion_isTerminal (C := C))
  have hcomp (x : T.obj.obj (op A)) :
      e.inv.hom.app (op A) (e.hom.hom.app (op A) x) = x :=
    congrArg (fun t => t.app (op A) x) (ObjectProperty.isoHom_inv_id_hom e)
  refine ⟨fun x y => ?_⟩
  have hxy : e.hom.hom.app (op A) x = e.hom.hom.app (op A) y := by
    change (_ : PUnit) = _
    exact Subsingleton.elim _ _
  rw [← hcomp x, ← hcomp y, hxy]

theorem completion_isFibrant [IsCylinderCategory C] (X : Completion.{w} C) :
    IsFibrantFor (Completion.fibrations C) X := by
  intro T hT A B i hi hwi a b hab
  obtain ⟨r, hir⟩ := IsCylinderCategory.exists_retraction i hi hwi
  refine ⟨X.obj.map r.op a, ?_, ?_⟩
  · change (X.obj.map r.op ≫ X.obj.map i.op) a = a
    rw [← X.obj.map_comp, ← op_comp, hir, op_id, X.obj.map_id]
    rfl
  · haveI := terminal_values_subsingleton hT B
    exact Subsingleton.elim _ _

theorem completion_cofibrations_retracts :
    (Completion.cofibrations.{w} C).IsStableUnderRetracts := by
  unfold Completion.cofibrations
  infer_instance

#print axioms completion_isFibrant
#print axioms completion_cofibrations_retracts

end HomotopyHypothesis.Category.SemiModelConstruction
