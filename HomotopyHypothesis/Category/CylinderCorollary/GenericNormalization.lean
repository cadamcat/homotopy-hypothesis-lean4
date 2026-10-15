import HomotopyHypothesis.Category.CylinderCorollary.HigherComposition
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationFamily
import HomotopyHypothesis.Category.CylinderCorollary.NormalizationStep
noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HomotopyHypothesis.Category.CylinderCorollary

universe u

open CategoryTheory
open OAI.Grothendieck

variable {C : GlobularTheory.{u}}

def normalizedFamily (hC : C.IsCoherator) (i : ℕ) :
    (p : ℕ) → NormalizationFamily C i (i + 1 + p) (by omega)
  | 0 => initialNormalizationFamily hC i
  | p + 1 => nextNormalizationFamily hC (normalizedFamily hC i p)

def normalizedEndpoint (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) :
    C.Hom (Shape.globe n) (lowerPairShape i n hi) := by
  have he : i + 1 + (n - (i + 1)) = n := by omega
  exact (Eq.ndrec (motive := fun k => (hk : i < k) →
    C.Hom (Shape.globe k) (lowerPairShape i k hk))
    (fun _ => (normalizedFamily hC i (n - (i + 1))).operation _ le_rfl) he) hi

theorem normalizedEndpoint_add (hC : C.IsCoherator) (i d : ℕ) :
    normalizedEndpoint hC i (i + 1 + d) (by omega) =
      (normalizedFamily hC i d).operation (i + 1 + d) le_rfl := by
  have hcast (k : ℕ) (he : i + 1 + k = i + 1 + d) :
      (Eq.ndrec (motive := fun n => (hn : i < n) →
        C.Hom (Shape.globe n) (lowerPairShape i n hn))
        (fun _ => (normalizedFamily hC i k).operation _ le_rfl) he) (by omega) =
        (normalizedFamily hC i d).operation _ le_rfl := by
    have hk : k = d := by omega
    subst k
    rfl
  unfold normalizedEndpoint
  exact hcast _ _

theorem normalizedEndpoint_parallel (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) :
    C.Parallel n (normalizedEndpoint hC i n hi) (C.base (lowerPairRight i n hi)) := by
  obtain ⟨d, he⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  subst n
  rw [normalizedEndpoint_add]
  exact (normalizedFamily hC i d).parallel

def normalizedEndpointPair (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) :
    C.AdmissiblePair where
  n := n
  arity := lowerPairShape i n hi
  height := by
    change max n n ≤ n + 1
    omega
  source := normalizedEndpoint hC i n hi
  target := C.base (lowerPairRight i n hi)
  parallel := normalizedEndpoint_parallel hC i n hi

def normalizedEndpointHomotopy (hC : C.IsCoherator) (i n : ℕ) (hi : i < n) :
    C.Hom (Shape.globe (n + 1)) (lowerPairShape i n hi) :=
  (hC.2 (normalizedEndpointPair hC i n hi)).choose

theorem normalizedEndpointHomotopy_source (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) :
    C.comp (C.base (Shape.source n)) (normalizedEndpointHomotopy hC i n hi) =
      normalizedEndpoint hC i n hi :=
  (hC.2 (normalizedEndpointPair hC i n hi)).choose_spec.1

theorem normalizedEndpointHomotopy_target (hC : C.IsCoherator)
    (i n : ℕ) (hi : i < n) :
    C.comp (C.base (Shape.target n)) (normalizedEndpointHomotopy hC i n hi) =
      C.base (lowerPairRight i n hi) :=
  (hC.2 (normalizedEndpointPair hC i n hi)).choose_spec.2

#print axioms normalizationStepOperation_boundary
#print axioms normalizationStepOperation_face
#print axioms nextNormalizationFamily
#print axioms normalizedEndpoint_parallel
#print axioms normalizedEndpointHomotopy_source
#print axioms normalizedEndpointHomotopy_target

end HomotopyHypothesis.Category.CylinderCorollary
