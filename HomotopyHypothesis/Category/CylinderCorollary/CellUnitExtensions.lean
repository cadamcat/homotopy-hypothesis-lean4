import HomotopyHypothesis.Category.CylinderCorollary.CellDimensions
import HomotopyHypothesis.Category.CylinderCorollary.IteratedUnits
import HomotopyHypothesis.Category.CylinderCorollary.LowerCells
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model

variable {C : GlobularTheory.{u}}

def unitCellExtension (X : C.Model) (hC : C.IsCoherator) (m n : ℕ) (hm : m ≤ n)
    (a : X.underlying.Cell m) : X.underlying.Cell n :=
  X.eval (unitExtension hC m n hm (C.id (Shape.globe m))) a

theorem unitCellExtension_refl (X : C.Model) (hC : C.IsCoherator) (m : ℕ)
    (a : X.underlying.Cell m) : unitCellExtension X hC m m le_rfl a = a := by
  dsimp only [unitCellExtension]
  rw [unitExtension_refl]
  exact eval_id X (S := Shape.globe m) a

theorem unitCellExtension_face (X : C.Model) (hC : C.IsCoherator)
    (m n : ℕ) (hm : m ≤ n) (side : Bool) (a : X.underlying.Cell m) :
    lowerFace X n (n + 1) (Nat.lt_succ_self n) side
        (unitCellExtension X hC m (n + 1) (Nat.le_trans hm (Nat.le_succ n)) a) =
      unitCellExtension X hC m n hm a := by
  dsimp only [lowerFace, unitCellExtension]
  rw [← eval_comp, unitExtension_face hC m n hm side]

theorem unitCellExtension_generalFace (X : C.Model) (hC : C.IsCoherator)
    (m l n : ℕ) (hm : m ≤ l) (hl : l < n) (side : Bool) (a : X.underlying.Cell m) :
    lowerFace X l n hl side (unitCellExtension X hC m n (by omega) a) =
      unitCellExtension X hC m l hm a := by
  dsimp only [lowerFace, unitCellExtension]
  rw [← eval_comp, unitExtension_generalFace hC m l n hm hl side]

theorem unitCellExtension_lowerFace (X : C.Model) (hC : C.IsCoherator)
    (j m n : ℕ) (hj : j < m) (hm : m ≤ n) (side : Bool) (a : X.underlying.Cell m) :
    lowerFace X j n (by omega) side (unitCellExtension X hC m n hm a) =
      lowerFace X j m hj side a := by
  dsimp only [lowerFace, unitCellExtension]
  rw [← eval_comp, unitExtension_lowerFace hC j m n hj hm side, C.comp_id]

theorem map_unitCellExtension {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator)
    (m n : ℕ) (hm : m ≤ n) (a : X.underlying.Cell m) :
    (underlyingMap f).app n (unitCellExtension X hC m n hm a) =
      unitCellExtension Y hC m n hm ((underlyingMap f).app m a) :=
  map_eval f (unitExtension hC m n hm (C.id (Shape.globe m))) a

theorem eval_unitExtension {S : Shape} (X : C.Model) (hC : C.IsCoherator)
    (m n : ℕ) (hm : m ≤ n) (a : C.Hom (Shape.globe m) S)
    (t : X.presheaf.obj (op (⟨S⟩ : C.Obj))) :
    X.eval (unitExtension hC m n hm a) t = unitCellExtension X hC m n hm (X.eval a t) := by
  have he : C.comp (unitExtension hC m n hm (C.id (Shape.globe m))) a =
      unitExtension hC m n hm a := by
    rw [unitExtension_postcomp, C.id_comp]
  dsimp only [unitCellExtension]
  rw [← he, eval_comp]

#print axioms unitCellExtension_generalFace
#print axioms unitCellExtension_lowerFace
#print axioms map_unitCellExtension
#print axioms eval_unitExtension

end HomotopyHypothesis.Category.CylinderCorollary
