import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Barycentric positions in original carriers

A relative subdivision vertex is placed at the barycentre of its source
simplex. For a retained vertex that source is a zero-simplex. The positions
commute with inclusions of carriers because the source face maps are unique.
-/

universe u

open CategoryTheory Limits Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The original simplex whose barycentre represents a subdivision vertex. -/
def RelativeVertex.sourceSimplex {K : SemiSSet.{u}} {L : Subfunctor K}
    (v : RelativeVertex K L) : Simplex K :=
  match v with
  | .inl w => ⟨0, w.val⟩
  | .inr s => s.val

private theorem exists_carriedFaceMap {K : SemiSSet.{u}} {L : Subfunctor K} {m : ℕ}
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) (v : RelativeVertex K L)
    (hv : RelativeVertex.CarriedBy v y) :
    ∃ θ : Henry.SemiSimplexCategory.mk v.sourceSimplex.1 ⟶ Henry.SemiSimplexCategory.mk m,
      K.map θ.op y = v.sourceSimplex.2 := by
  cases v with
  | inl w => exact hv
  | inr s => exact hv

/-- Choose the inclusion of a subdivision vertex's source simplex into a carrier. -/
noncomputable def carriedFaceMap {K : SemiSSet.{u}} {L : Subfunctor K} {m : ℕ}
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) (v : RelativeVertex K L)
    (hv : RelativeVertex.CarriedBy v y) :
    Henry.SemiSimplexCategory.mk v.sourceSimplex.1 ⟶ Henry.SemiSimplexCategory.mk m :=
  Classical.choose (exists_carriedFaceMap y v hv)

/-- The chosen face map restricts the carrier to the source simplex. -/
theorem carriedFaceMap_spec {K : SemiSSet.{u}} {L : Subfunctor K} {m : ℕ}
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) (v : RelativeVertex K L)
    (hv : RelativeVertex.CarriedBy v y) :
    K.map (carriedFaceMap y v hv).op y = v.sourceSimplex.2 :=
  Classical.choose_spec (exists_carriedFaceMap y v hv)

/-- Chosen source face maps agree with composition through a carrier inclusion. -/
theorem carriedFaceMap_comp {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {m k : ℕ}
    {y : K.obj (op (Henry.SemiSimplexCategory.mk m))}
    {z : K.obj (op (Henry.SemiSimplexCategory.mk k))}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : K.map θ.op z = y) (v : RelativeVertex K L)
    (hy : RelativeVertex.CarriedBy v y) (hz : RelativeVertex.CarriedBy v z) :
    carriedFaceMap z v hz = carriedFaceMap y v hy ≫ θ := by
  apply faceMap_unique hK
  · exact carriedFaceMap_spec z v hz
  · rw [op_comp, K.map_comp_apply, hθ, carriedFaceMap_spec]

/-- The barycentric position of a subdivision vertex in an original carrier. -/
noncomputable def relativeVertexPosition {K : SemiSSet.{u}} {L : Subfunctor K} {m : ℕ}
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) (v : RelativeVertex K L)
    (hv : RelativeVertex.CarriedBy v y) : StdSimplex ℝ (Fin (m + 1)) :=
  StdSimplex.map (carriedFaceMap y v hv).hom.toOrderHom
    (StdSimplex.barycenter (K := ℝ) (M := Fin (v.sourceSimplex.1 + 1)))

/-- Barycentric positions commute with inclusions of their original carriers. -/
theorem relativeVertexPosition_face {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {m k : ℕ}
    {y : K.obj (op (Henry.SemiSimplexCategory.mk m))}
    {z : K.obj (op (Henry.SemiSimplexCategory.mk k))}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : K.map θ.op z = y) (v : RelativeVertex K L)
    (hy : RelativeVertex.CarriedBy v y) (hz : RelativeVertex.CarriedBy v z) :
    relativeVertexPosition z v hz =
      StdSimplex.map θ.hom.toOrderHom (relativeVertexPosition y v hy) := by
  unfold relativeVertexPosition
  rw [carriedFaceMap_comp hK θ hθ v hy hz]
  simpa only [WideSubcategory.comp_def, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe] using
    StdSimplex.map_comp
      (StdSimplex.barycenter (K := ℝ) (M := Fin (v.sourceSimplex.1 + 1)))
      (carriedFaceMap y v hy).hom.toOrderHom θ.hom.toOrderHom

/-- A retained subdivision vertex is placed at its old vertex position. -/
theorem relativeVertexPosition_retained {K : SemiSSet.{u}} {L : Subfunctor K} {m : ℕ}
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m)))
    (v : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0)))
    (hv : RelativeVertex.CarriedBy (Sum.inl v : RelativeVertex K L) y) :
    relativeVertexPosition y (.inl v) hv =
      StdSimplex.single ((carriedFaceMap y (.inl v) hv).hom.toOrderHom (0 : Fin 1)) := by
  unfold relativeVertexPosition
  change StdSimplex.map (carriedFaceMap y (.inl v) hv).hom.toOrderHom
    (StdSimplex.barycenter (K := ℝ) (M := Fin 1)) = _
  rw [StdSimplex.barycenter_fin_one]
  exact StdSimplex.map_single (R := ℝ) _ _

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeVertexPosition_face
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeVertexPosition_retained
