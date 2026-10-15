import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.PrismComposition.SubdivisionPrismComposition
import HomotopyHypothesis.Approximation.Zeeman.DerivedSubdivision
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RetainedFull
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionComposition
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionDimension
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Iterated relative derived subdivisions

Composing the pinched collapsing prisms gives a relative subdivision at
every iteration. The retained image is full after the first iteration,
and a dimension bound on the original complex holds at every stage.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The image of the retained map through a composite subdivision is the
retained image of its last step. -/
theorem compositeSubdivisionRetainedMap_range {Y : SemiSSet.{u}} {J : Subfunctor Y}
    (S₁ : RelSubdivision Y J) (S₂ : RelSubdivision S₁.Y' (Subfunctor.range S₁.j)) :
    Subfunctor.range (compositeSubdivisionRetainedMap S₁ S₂) = Subfunctor.range S₂.j := by
  unfold compositeSubdivisionRetainedMap
  rw [Subfunctor.range_comp, Subfunctor.range_toRange, Subfunctor.image_top]

/-- The relative derived subdivision iterated a specified number of times. -/
noncomputable def derivedSubdivisionIterate {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) (r : ℕ) : RelSubdivision K L :=
  (iteratedDerivedSubdivision Approximation.PrismComposition.subdivisionPrismCompositionStatement_proof
    hK hKs L r).val

/-- Every iterated derived subdivision is an ordered simplicial complex. -/
theorem derivedSubdivisionIterate_isSimplicialComplex {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L : Subfunctor K) (r : ℕ) :
    (derivedSubdivisionIterate hK hKs L r).Y'.IsSimplicialComplex :=
  (iteratedDerivedSubdivision Approximation.PrismComposition.subdivisionPrismCompositionStatement_proof
    hK hKs L r).property

/-- Zero iterations leave the original semi-simplicial set. -/
@[simp] theorem derivedSubdivisionIterate_zero_obj {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    (derivedSubdivisionIterate hK hKs L 0).Y' = K := rfl

/-- Each iteration is the relative derived of the preceding stage modulo its retained image. -/
theorem derivedSubdivisionIterate_succ_obj {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L : Subfunctor K) (r : ℕ) :
    (derivedSubdivisionIterate hK hKs L (r + 1)).Y' =
      relativeDerived (derivedSubdivisionIterate hK hKs L r).Y'
        (Subfunctor.range (derivedSubdivisionIterate hK hKs L r).j) := rfl

/-- The retained map at zero iterations is the original subcomplex inclusion. -/
@[simp] theorem derivedSubdivisionIterate_zero_j {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    (derivedSubdivisionIterate hK hKs L 0).j = L.ι := rfl

/-- Retained maps compose through the previous stage's retained image. -/
theorem derivedSubdivisionIterate_succ_j {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L : Subfunctor K) (r : ℕ) :
    (derivedSubdivisionIterate hK hKs L (r + 1)).j =
      Subfunctor.toRange (derivedSubdivisionIterate hK hKs L r).j ≫
        relativeDerivedInclusion (derivedSubdivisionIterate_isSimplicialComplex hK hKs L r)
          (Subfunctor.range (derivedSubdivisionIterate hK hKs L r).j) := rfl

/-- The realization identification is composed with the new relative derived identification. -/
theorem derivedSubdivisionIterate_succ_hom {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L : Subfunctor K) (r : ℕ) :
    (derivedSubdivisionIterate hK hKs L (r + 1)).h.hom =
      (derivedSubdivision (derivedSubdivisionIterate hK hKs L r).finite
        (derivedSubdivisionIterate_isSimplicialComplex hK hKs L r)
        (Subfunctor.range (derivedSubdivisionIterate hK hKs L r).j)).h.hom ≫
          (derivedSubdivisionIterate hK hKs L r).h.hom := rfl

/-- Every positive iteration has a full retained subcomplex. -/
theorem derivedSubdivisionIterate_retained_isFull {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L : Subfunctor K) (r : ℕ) :
    IsFullSubcomplex (Subfunctor.range (derivedSubdivisionIterate hK hKs L (r + 1)).j) := by
  change IsFullSubcomplex (Subfunctor.range (compositeSubdivisionRetainedMap
    (derivedSubdivisionIterate hK hKs L r)
    (derivedSubdivision (derivedSubdivisionIterate hK hKs L r).finite
      (derivedSubdivisionIterate_isSimplicialComplex hK hKs L r)
      (Subfunctor.range (derivedSubdivisionIterate hK hKs L r).j))))
  rw [compositeSubdivisionRetainedMap_range]
  exact derivedSubdivision_retained_isFull (derivedSubdivisionIterate hK hKs L r).finite
    (derivedSubdivisionIterate_isSimplicialComplex hK hKs L r) _

/-- A dimension bound holds at every iterated relative derived stage. -/
theorem derivedSubdivisionIterate_dimensionBound {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L : Subfunctor K) (D : ℕ)
    (hD : ∀ n, D < n → IsEmpty (K.obj (op (Henry.SemiSimplexCategory.mk n)))) (r : ℕ) :
    ∀ n, D < n → IsEmpty
      ((derivedSubdivisionIterate hK hKs L r).Y'.obj (op (Henry.SemiSimplexCategory.mk n))) := by
  induction r with
  | zero => exact hD
  | succ r ih =>
    exact relativeDerived_dimensionBound (derivedSubdivisionIterate_isSimplicialComplex hK hKs L r)
      (Subfunctor.range (derivedSubdivisionIterate hK hKs L r).j) D ih

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.derivedSubdivisionIterate
#print axioms HomotopyHypothesis.Approximation.Zeeman.derivedSubdivisionIterate_retained_isFull
#print axioms HomotopyHypothesis.Approximation.Zeeman.derivedSubdivisionIterate_dimensionBound
