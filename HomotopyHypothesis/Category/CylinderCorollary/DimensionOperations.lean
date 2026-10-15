import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.InitialNormalization
import HomotopyHypothesis.Category.CylinderCorollary.OperationFaces
import HomotopyHypothesis.Category.CylinderCorollary.TheoryBoundaries
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

variable {C : GlobularTheory.{u}}

def operationCompositionAt {S : Shape} (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (a b : C.Hom (Shape.globe n) S)
    (hab : C.comp (C.base (Shape.face hi true)) a = C.comp (C.base (Shape.face hi false)) b) :
    C.Hom (Shape.globe n) S := by
  have he : i + 1 + (n - (i + 1)) = n := by omega
  exact (Eq.ndrec (motive := fun k => (hk : i < k) →
    (a b : C.Hom (Shape.globe k) S) →
    C.comp (C.base (Shape.face hk true)) a = C.comp (C.base (Shape.face hk false)) b →
      C.Hom (Shape.globe k) S)
    (fun _ => operationComposition hC i (n - (i + 1))) he) hi a b hab

theorem operationCompositionAt_add {S : Shape} (hC : C.IsCoherator) (i d : ℕ)
    (a b : C.Hom (Shape.globe (i + 1 + d)) S)
    (hab : C.comp (C.base (Shape.face (by omega : i < i + 1 + d) true)) a =
      C.comp (C.base (Shape.face (by omega : i < i + 1 + d) false)) b) :
    operationCompositionAt hC i (i + 1 + d) (by omega) a b hab =
      operationComposition hC i d a b hab := by
  have hcast (k : ℕ) (he : i + 1 + k = i + 1 + d) :
      (Eq.ndrec (motive := fun n => (hn : i < n) →
        (a b : C.Hom (Shape.globe n) S) →
        C.comp (C.base (Shape.face hn true)) a = C.comp (C.base (Shape.face hn false)) b →
          C.Hom (Shape.globe n) S)
        (fun _ => operationComposition hC i k) he) (by omega) a b hab =
        operationComposition hC i d a b hab := by
    have hk : k = d := by omega
    subst k
    rfl
  unfold operationCompositionAt
  exact hcast _ _

theorem operationCompositionAt_boundary {S : Shape} (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) (a b : C.Hom (Shape.globe n) S)
    (hab : C.comp (C.base (Shape.face hi true)) a = C.comp (C.base (Shape.face hi false)) b) :
    C.comp (C.base (Shape.face hi side)) (operationCompositionAt hC i n hi a b hab) =
      C.comp (C.base (Shape.face hi side)) (if side then b else a) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [operationCompositionAt_add]
  exact operationComposition_boundary hC i d side a b hab

theorem operationCompositionAt_postcomp {S T : Shape} (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (a b : C.Hom (Shape.globe n) S)
    (hab : C.comp (C.base (Shape.face hi true)) a = C.comp (C.base (Shape.face hi false)) b)
    (q : C.Hom S T) :
    C.comp (operationCompositionAt hC i n hi a b hab) q =
      operationCompositionAt hC i n hi (C.comp a q) (C.comp b q)
        (by rw [← C.assoc, ← C.assoc, hab]) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [operationCompositionAt_add, operationCompositionAt_add]
  exact operationComposition_postcomp hC i d a b hab q

theorem operationCompositionAt_face {S : Shape} (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) (a b : C.Hom (Shape.globe (n + 1)) S)
    (hab : C.comp (C.base (Shape.face (by omega : i < n + 1) true)) a =
      C.comp (C.base (Shape.face (by omega : i < n + 1) false)) b) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
        (operationCompositionAt hC i (n + 1) (by omega) a b hab) =
      operationCompositionAt hC i n hi
        (C.comp (C.base (Shape.face (Nat.lt_succ_self n) side)) a)
        (C.comp (C.base (Shape.face (Nat.lt_succ_self n) side)) b)
        (by simp only [← C.assoc, ← C.base_comp, shape_face_comp]; exact hab) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  change C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side))
      (operationCompositionAt hC i (i + 1 + (d + 1)) _ a b hab) = _
  rw [operationCompositionAt_add, operationCompositionAt_add]
  exact operationComposition_face hC i d side a b hab

def operationInverseAt {S : Shape} (hC : C.IsCoherator) (i n : ℕ) (hi : i < n)
    (a : C.Hom (Shape.globe n) S) : C.Hom (Shape.globe n) S := by
  have he : i + 1 + (n - (i + 1)) = n := by omega
  exact (he ▸ operationInverse (C := C) (S := S) hC i (n - (i + 1))) a

theorem operationInverseAt_add {S : Shape} (hC : C.IsCoherator) (i d : ℕ)
    (a : C.Hom (Shape.globe (i + 1 + d)) S) :
    operationInverseAt hC i (i + 1 + d) (by omega) a = operationInverse hC i d a := by
  have hcast (k : ℕ) (he : i + 1 + k = i + 1 + d) :
      (Eq.ndrec (motive := fun n => C.Hom (Shape.globe n) S → C.Hom (Shape.globe n) S)
        (operationInverse hC i k) he) a = operationInverse hC i d a := by
    have hk : k = d := by omega
    subst k
    rfl
  unfold operationInverseAt
  exact hcast _ _

theorem operationInverseAt_boundary {S : Shape} (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) (a : C.Hom (Shape.globe n) S) :
    C.comp (C.base (Shape.face hi side)) (operationInverseAt hC i n hi a) =
      C.comp (C.base (Shape.face hi (!side))) a := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [operationInverseAt_add]
  exact operationInverse_boundary hC i d side a

theorem operationInverseAt_postcomp {S T : Shape} (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (a : C.Hom (Shape.globe n) S) (q : C.Hom S T) :
    C.comp (operationInverseAt hC i n hi a) q =
      operationInverseAt hC i n hi (C.comp a q) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [operationInverseAt_add, operationInverseAt_add]
  exact operationInverse_postcomp hC i d a q

theorem operationInverseAt_face {S : Shape} (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) (side : Bool) (a : C.Hom (Shape.globe (n + 1)) S) :
    C.comp (C.base (Shape.face (Nat.lt_succ_self n) side))
        (operationInverseAt hC i (n + 1) (by omega) a) =
      operationInverseAt hC i n hi
        (C.comp (C.base (Shape.face (Nat.lt_succ_self n) side)) a) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  change C.comp (C.base (Shape.face (Nat.lt_succ_self (i + 1 + d)) side))
      (operationInverseAt hC i (i + 1 + (d + 1)) _ a) = _
  rw [operationInverseAt_add, operationInverseAt_add]
  exact operationInverse_face hC i d side a

#print axioms operationCompositionAt_boundary
#print axioms operationCompositionAt_face
#print axioms operationInverseAt_boundary
#print axioms operationInverseAt_face

end HomotopyHypothesis.Category.CylinderCorollary
