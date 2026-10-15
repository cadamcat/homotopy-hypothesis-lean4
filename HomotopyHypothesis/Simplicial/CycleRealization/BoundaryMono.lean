import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.Boundary.RealizationGeometry
import HomotopyHypothesis.Simplicial.CycleRealization.BoundaryInjective
import HomotopyHypothesis.Simplicial.CycleRealization.RealizedPoints
universe u

open CategoryTheory Limits Opposite Convexity
open HomotopyHypothesis.Henry
open HomotopyHypothesis.Realization.Boundary

namespace HomotopyHypothesis.Simplicial.CycleRealization

/-- The codimension-one face, regarded as a simplex of the boundary. -/
def faceElement {n : ℕ} (i : Fin (n + 2)) :
    (SemiSSet.boundary.{u} (n + 1)).toFunctor.obj
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) :=
  ⟨ULift.up (face i), i, by
    rintro ⟨a, ha⟩
    exact (Fin.succAbove_ne i a) ha⟩

/-- Ambient barycentric coordinates of a point represented in the boundary. -/
theorem boundary_simplexPoint_coords {n : ℕ}
    {c : HomotopyHypothesis.Henry.SemiSimplexCategory}
    (a : (SemiSSet.boundary.{u} n).toFunctor.obj (op c))
    (s : StdSimplex ℝ (Fin (c.obj.len + 1))) :
    (realization_representable_iso
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).hom.hom
      ((SemiSSet.realization.map (SemiSSet.boundary n).ι).hom (simplexPoint a s)) =
      ULift.up (StdSimplex.map a.val.down.hom.toOrderHom s) := by
  rw [map_simplexPoint]
  exact simplexPoint_representable a.val.down s

/-- A boundary point with a zero coordinate can be represented on the opposite face. -/
theorem boundary_simplexPoint_on_face {n : ℕ}
    {c : HomotopyHypothesis.Henry.SemiSimplexCategory}
    (a : (SemiSSet.boundary.{u} (n + 1)).toFunctor.obj (op c))
    (s : StdSimplex ℝ (Fin (c.obj.len + 1))) (i : Fin (n + 2))
    (hi : (StdSimplex.map a.val.down.hom.toOrderHom s).weights i = 0) :
    ∃ t : StdSimplex ℝ (Fin (n + 1)),
      simplexPoint a s = simplexPoint (faceElement i) t := by
  rcases c with ⟨⟨m⟩⟩
  obtain ⟨k, g, h, r, hfac, hr⟩ := restrict_to_face a.val.down s i hi
  have helem : (SemiSSet.boundary (n + 1)).toFunctor.map g.op a =
      (SemiSSet.boundary (n + 1)).toFunctor.map h.op (faceElement i) := by
    apply Subtype.ext
    apply ULift.ext
    exact hfac
  refine ⟨StdSimplex.map h.hom.toOrderHom r, ?_⟩
  calc
    simplexPoint a s =
        simplexPoint ((SemiSSet.boundary (n + 1)).toFunctor.map g.op a) r := by
      rw [simplexPoint_naturality, hr]
    _ = simplexPoint ((SemiSSet.boundary (n + 1)).toFunctor.map h.op (faceElement i)) r := by
      rw [helem]
    _ = _ := simplexPoint_naturality h (faceElement i) r

/-- Affine maps induced by injective vertex maps are injective on simplex points. -/
theorem stdSimplex_map_injective {A B : Type*} (f : A → B) (hf : Function.Injective f) :
    Function.Injective (StdSimplex.map (R := ℝ) f) := by
  intro s t h
  apply StdSimplex.ext
  ext j
  have hj := congrArg (fun v : StdSimplex ℝ B => v.weights (f j)) h
  simpa only [StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective hf] using hj

/-- Realization of the boundary inclusion is injective. -/
theorem realization_boundary_injective (n : ℕ) :
    Function.Injective (SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} n).ι).hom := by
  intro x y hxy
  obtain ⟨c, a, s, rfl⟩ := exists_simplexPoint (SemiSSet.boundary n).toFunctor x
  obtain ⟨d, b, t, rfl⟩ := exists_simplexPoint (SemiSSet.boundary n).toFunctor y
  cases n with
  | zero =>
    obtain ⟨i, hi⟩ := a.property
    have hvertex : a.val.down.hom.toOrderHom 0 = i := by
      change (_ : Fin 1) = (_ : Fin 1)
      exact Subsingleton.elim _ _
    exact (hi ⟨0, hvertex⟩).elim
  | succ n =>
    have hamb : StdSimplex.map a.val.down.hom.toOrderHom s =
        StdSimplex.map b.val.down.hom.toOrderHom t := by
      have heq := congrArg
        (realization_representable_iso
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (n + 1))).hom.hom hxy
      rw [boundary_simplexPoint_coords, boundary_simplexPoint_coords] at heq
      exact congrArg ULift.down heq
    obtain ⟨i, hi⟩ := a.property
    have hzero : (StdSimplex.map a.val.down.hom.toOrderHom s).weights i = 0 :=
      Finsupp.mapDomain_of_notMem_range s.weights i hi
    obtain ⟨s', hs⟩ := boundary_simplexPoint_on_face a s i hzero
    obtain ⟨t', ht⟩ := boundary_simplexPoint_on_face b t i (hamb ▸ hzero)
    have hface : StdSimplex.map (face i).hom.toOrderHom s' =
        StdSimplex.map (face i).hom.toOrderHom t' := by
      apply ULift.up_injective
      have heq := congrArg
        (realization_representable_iso
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (n + 1))).hom.hom hxy
      rw [hs, ht, boundary_simplexPoint_coords, boundary_simplexPoint_coords] at heq
      exact heq
    have hst : s' = t' := stdSimplex_map_injective _ (Fin.succAboveOrderEmb i).injective hface
    exact hs.trans ((congrArg (simplexPoint (faceElement i)) hst).trans ht.symm)

/-- The realized boundary inclusion is a monomorphism of spaces. -/
theorem realization_boundary_mono (n : ℕ) :
    Mono (SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} n).ι) :=
  (TopCat.mono_iff_injective _).mpr (realization_boundary_injective n)

#print axioms realization_boundary_injective

end HomotopyHypothesis.Simplicial.CycleRealization
