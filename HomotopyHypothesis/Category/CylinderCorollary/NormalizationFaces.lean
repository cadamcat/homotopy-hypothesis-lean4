import HomotopyHypothesis.Category.CylinderCorollary.DimensionOperations
import HomotopyHypothesis.Category.CylinderCorollary.GeneralPairFaces
import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.InitialNormalization
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

variable {C : GlobularTheory.{u}}

def initialNormalizationAt (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) :
    C.Hom (Shape.globe n) (lowerPairShape i n hi) := by
  have he : i + 1 + (n - (i + 1)) = n := by omega
  exact (Eq.ndrec (motive := fun k => (hk : i < k) →
    C.Hom (Shape.globe k) (lowerPairShape i k hk))
    (fun _ => initialNormalization hC i (n - (i + 1))) he) hi

theorem initialNormalizationAt_add (hC : C.IsCoherator) (i d : ℕ) :
    initialNormalizationAt hC i (i + 1 + d) (by omega) =
      initialNormalization hC i d := by
  have hcast (k : ℕ) (he : i + 1 + k = i + 1 + d) :
      (Eq.ndrec (motive := fun n => (hn : i < n) →
        C.Hom (Shape.globe n) (lowerPairShape i n hn))
        (fun _ => initialNormalization hC i k) he) (by omega) =
        initialNormalization hC i d := by
    have hk : k = d := by omega
    subst k
    rfl
  unfold initialNormalizationAt
  exact hcast _ _

theorem initialNormalizationAt_boundary (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) :
    C.comp (C.base (Shape.face hi side)) (initialNormalizationAt hC i n hi) =
      C.comp (C.base (Shape.face hi side)) (C.base (lowerPairRight i n hi)) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [initialNormalizationAt_add]
  exact initialNormalization_boundary hC i d side

theorem initialNormalizationAt_face (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
        (initialNormalizationAt hC i (n + 1) (Nat.lt_trans hi (Nat.lt_succ_self n))) =
      C.comp (initialNormalizationAt hC i n hi)
        (lowerPairMap C i n (n + 1) hi (Nat.lt_succ_self n) side) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  change C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side))
      (initialNormalizationAt hC i (i + 1 + (d + 1)) _) = _
  rw [initialNormalizationAt_add, initialNormalizationAt_add, lowerPairMap_succ]
  exact initialNormalization_face hC i d side

theorem initialNormalizationAt_generalFace (hC : C.IsCoherator)
    (i m n : ℕ) (hi : i < m) (hm : m < n) (side : Bool) :
    C.comp (C.base (Shape.face hm side))
        (initialNormalizationAt hC i n (Nat.lt_trans hi hm)) =
      C.comp (initialNormalizationAt hC i m hi)
        (lowerPairMap C i m n hi hm side) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : m = n
    · subst m
      exact initialNormalizationAt_face hC i n hi side
    · have hm' : m < n := by omega
      have hni : i < n := Nat.lt_trans hi hm'
      conv_lhs =>
        rw [← shape_face_comp hm' (Nat.lt_succ_self n) side false,
          C.base_comp, C.assoc, initialNormalizationAt_face hC i n hni false,
          ← C.assoc, ih hm']
      rw [C.assoc, lowerPairMap_comp]

#print axioms operationCompositionAt_boundary
#print axioms operationCompositionAt_face
#print axioms operationInverseAt_boundary
#print axioms operationInverseAt_face
#print axioms lowerPairMap_comp
#print axioms initialNormalizationAt_boundary
#print axioms initialNormalizationAt_generalFace

end HomotopyHypothesis.Category.CylinderCorollary
