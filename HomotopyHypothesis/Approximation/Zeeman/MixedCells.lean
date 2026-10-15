import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Embedded cells in the mixed relative prism

Injective vertex tuples distinguish face inclusions into a simplex. Thus
the characteristic semi-simplicial map of every mixed tuple is a
monomorphism, as required to attach it along a horn.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A simplex with distinct combinatorial vertices is embedded as a semi-simplicial cell. -/
theorem simplex_mono_of_vertex_injective {K : SemiSSet.{u}} {n : ℕ}
    (x : K.obj (op (Henry.SemiSimplexCategory.mk n))) (hx : Function.Injective (vertex x)) :
    Mono (uliftYonedaEquiv.symm x) := by
  rw [NatTrans.mono_iff_mono_app]
  intro X
  rw [mono_iff_injective]
  intro θ η h
  apply ULift.ext
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  apply hx
  have he : K.map θ.down.op x = K.map η.down.op x := by
    change K.map θ.down.op x = K.map η.down.op x at h
    exact h
  exact (vertex_map θ.down x i).symm.trans
    ((congrArg (fun y => vertex y i) he).trans (vertex_map η.down x i))

/-- The raw vertices of every mixed tuple are distinct. -/
theorem mixed_vertex_injective {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    Function.Injective (vertex a) := by
  intro i j hij
  apply a.property.1
  exact congrArg (fun q => q.val 0) hij

/-- Every mixed simplex defines an embedded semi-simplicial cell. -/
instance mixedSimplex_mono {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    Mono (uliftYonedaEquiv.symm a) :=
  simplex_mono_of_vertex_injective a (mixed_vertex_injective a)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.simplex_mono_of_vertex_injective
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedSimplex_mono
