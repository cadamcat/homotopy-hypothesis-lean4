import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

variable {C : GlobularTheory.{u}}

def iteratedUnitOperation {S : Shape} (hC : C.IsCoherator) (m : ℕ)
    (a : C.Hom (Shape.globe m) S) : (d : ℕ) → C.Hom (Shape.globe (m + d)) S
  | 0 => a
  | d + 1 => C.comp (C.unit hC (m + d)) (iteratedUnitOperation hC m a d)

theorem iteratedUnitOperation_face {S : Shape} (hC : C.IsCoherator) (m d : ℕ)
    (side : Bool) (a : C.Hom (Shape.globe m) S) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self (m + d)) side))
        (iteratedUnitOperation hC m a (d + 1)) = iteratedUnitOperation hC m a d := by
  change C.comp (C.base (Shape.face (Nat.lt_succ_self (m + d)) side))
    (C.comp (C.unit hC (m + d)) (iteratedUnitOperation hC m a d)) = _
  rw [← C.assoc]
  cases side
  · change C.comp (C.comp (C.base (Shape.source (m + d))) (C.unit hC (m + d))) _ = _
    rw [C.unit_source, C.id_comp]
  · change C.comp (C.comp (C.base (Shape.target (m + d))) (C.unit hC (m + d))) _ = _
    rw [C.unit_target, C.id_comp]

theorem iteratedUnitOperation_postcomp {S T : Shape} (hC : C.IsCoherator) (m d : ℕ)
    (a : C.Hom (Shape.globe m) S) (q : C.Hom S T) :
    C.comp (iteratedUnitOperation hC m a d) q =
      iteratedUnitOperation hC m (C.comp a q) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [iteratedUnitOperation]
    rw [C.assoc, ih]

def unitExtension {S : Shape} (hC : C.IsCoherator) (m n : ℕ) (hm : m ≤ n)
    (a : C.Hom (Shape.globe m) S) : C.Hom (Shape.globe n) S := by
  have he : m + (n - m) = n := by omega
  exact Eq.ndrec (motive := fun k => C.Hom (Shape.globe k) S)
    (iteratedUnitOperation hC m a (n - m)) he

theorem unitExtension_add {S : Shape} (hC : C.IsCoherator) (m d : ℕ)
    (a : C.Hom (Shape.globe m) S) :
    unitExtension hC m (m + d) (by omega) a = iteratedUnitOperation hC m a d := by
  have hcast (k : ℕ) (he : m + k = m + d) :
      Eq.ndrec (motive := fun n => C.Hom (Shape.globe n) S)
        (iteratedUnitOperation hC m a k) he = iteratedUnitOperation hC m a d := by
    have hk : k = d := by omega
    subst k
    rfl
  unfold unitExtension
  exact hcast _ _

theorem unitExtension_refl {S : Shape} (hC : C.IsCoherator) (m : ℕ)
    (a : C.Hom (Shape.globe m) S) : unitExtension hC m m le_rfl a = a :=
  unitExtension_add hC m 0 a

theorem unitExtension_postcomp {S T : Shape} (hC : C.IsCoherator)
    (m n : ℕ) (hm : m ≤ n) (a : C.Hom (Shape.globe m) S) (q : C.Hom S T) :
    C.comp (unitExtension hC m n hm a) q = unitExtension hC m n hm (C.comp a q) := by
  obtain ⟨d, he⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  subst n
  rw [unitExtension_add, unitExtension_add]
  exact iteratedUnitOperation_postcomp hC m d a q

theorem unitExtension_face {S : Shape} (hC : C.IsCoherator)
    (m n : ℕ) (hm : m ≤ n) (side : Bool) (a : C.Hom (Shape.globe m) S) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
        (unitExtension hC m (n + 1) (Nat.le_trans hm (Nat.le_succ n)) a) =
      unitExtension hC m n hm a := by
  obtain ⟨d, he⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  subst n
  change C.comp (C.base (Shape.face (Nat.lt_succ_self (m + d)) side))
    (unitExtension hC m (m + (d + 1)) _ a) = _
  rw [unitExtension_add, unitExtension_add]
  exact iteratedUnitOperation_face hC m d side a

theorem unitExtension_generalFace {S : Shape} (hC : C.IsCoherator)
    (m l n : ℕ) (hm : m ≤ l) (hl : l < n) (side : Bool)
    (a : C.Hom (Shape.globe m) S) :
    C.comp (C.base (Shape.face hl side))
        (unitExtension hC m n (Nat.le_trans hm (Nat.le_of_lt hl)) a) =
      unitExtension hC m l hm a := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : l = n
    · subst l
      exact unitExtension_face hC m n hm side a
    · have hl' : l < n := by omega
      have hmn : m ≤ n := Nat.le_trans hm (Nat.le_of_lt hl')
      conv_lhs =>
        rw [← shape_face_comp hl' (Nat.lt_succ_self n) side false,
          C.base_comp, C.assoc, unitExtension_face hC m n hmn false a, ih hl']

theorem unitExtension_lowerFace {S : Shape} (hC : C.IsCoherator)
    (j m n : ℕ) (hj : j < m) (hm : m ≤ n) (side : Bool)
    (a : C.Hom (Shape.globe m) S) :
    C.comp (C.base (Shape.face (Nat.lt_of_lt_of_le hj hm) side))
        (unitExtension hC m n hm a) = C.comp (C.base (Shape.face hj side)) a := by
  by_cases he : m = n
  · subst n
    rw [unitExtension_refl]
  · have hmn : m < n := by omega
    conv_lhs =>
      rw [← shape_face_comp hj hmn side false, C.base_comp, C.assoc,
        unitExtension_generalFace hC m m n le_rfl hmn false a, unitExtension_refl]

#print axioms unitExtension_postcomp
#print axioms unitExtension_face
#print axioms unitExtension_generalFace
#print axioms unitExtension_lowerFace

end HomotopyHypothesis.Category.CylinderCorollary
