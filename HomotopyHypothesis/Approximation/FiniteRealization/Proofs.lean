import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.Category.TopCat.Limits.Basic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.GlueStatements.IsSimplicialOfForall
import HomotopyHypothesis.Approximation.Topological.KanApproximation.Part1
/-!
# Finiteness and simplicial facts for semi-simplicial realizations
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.FiniteRealization

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological

/-- The simplices of a semi-simplicial set, with their dimensions retained. -/
abbrev TotalSimplex (K : SemiSSet.{u}) :=
  Σ n : ℕ, K.obj (op (Henry.SemiSimplexCategory.mk n))

/-- A finite semi-simplicial set has finitely many simplices in total. -/
theorem totalSimplex_finite {K : SemiSSet.{u}} (hK : K.IsFinite) :
    Finite (TotalSimplex K) := by
  rcases hK with ⟨hfin, N, hN⟩
  letI : ∀ n : ℕ, Finite (K.obj (op (Henry.SemiSimplexCategory.mk n))) := hfin
  have hd (s : TotalSimplex K) : s.1 ≤ N := by
    by_contra hn
    haveI : IsEmpty (K.obj (op (Henry.SemiSimplexCategory.mk s.1))) :=
      hN s.1 (Nat.lt_of_not_ge hn)
    exact isEmptyElim s.2
  let enc : TotalSimplex K →
      Σ n : Fin (N + 1), K.obj (op (Henry.SemiSimplexCategory.mk n.val)) :=
    fun s => ⟨⟨s.1, Nat.lt_succ_of_le (hd s)⟩, s.2⟩
  apply Finite.of_injective enc
  intro s t h
  exact congrArg (fun q : Σ n : Fin (N + 1),
      K.obj (op (Henry.SemiSimplexCategory.mk n.val)) => (⟨q.1.val, q.2⟩ : TotalSimplex K)) h

/-- The characteristic maps form the pointwise realization cocone. -/
noncomputable def realizationCocone (K : SemiSSet.{u}) :
    Cocone (CostructuredArrow.proj Henry.SemiSSet.stdSimplex K ⋙ toTop.{u}) :=
  (Functor.LeftExtension.mk realization
    (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u})).coconeAt K

/-- Realization is the colimit of its topological simplices. -/
noncomputable def realizationCocone_isColimit (K : SemiSSet.{u}) :
    IsColimit (realizationCocone K) :=
  Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
    Henry.SemiSSet.stdSimplex.{u} toTop.{u} K

/-- Every point of a realization has a simplex representative. -/
theorem exists_simplexChar_rep {K : SemiSSet.{u}} (z : realization.obj K) :
    ∃ (n : ℕ) (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ K)
      (t : toTop.obj (Henry.SemiSimplexCategory.mk n)), (simplexChar y).hom t = z := by
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (realizationCocone_isColimit K)) z
  exact ⟨j.left.obj.len, j.hom, t, ht⟩

/-- The realization of a finite semi-simplicial set is compact. -/
theorem compactSpace_realization_of_isFinite'_proof {K : SemiSSet.{u}} (hK : K.IsFinite) :
    CompactSpace (realization.obj K) := by
  haveI : Finite (TotalSimplex K) := totalSimplex_finite hK
  have (s : TotalSimplex K) :
      CompactSpace (toTop.{u}.obj (Henry.SemiSimplexCategory.mk s.1)) := by
    change CompactSpace (ULift.{u} (Convexity.StdSimplex ℝ (Fin (s.1 + 1))))
    infer_instance
  let D := Σ s : TotalSimplex K, toTop.{u}.obj (Henry.SemiSimplexCategory.mk s.1)
  let q : D → realization.obj K := fun p =>
    (simplexChar (uliftYonedaEquiv.symm p.1.2)).hom p.2
  have hq : Continuous q := continuous_sigma fun s =>
    (simplexChar (uliftYonedaEquiv.symm s.2)).hom.continuous
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨n, y, t, ht⟩ := exists_simplexChar_rep z
    refine ⟨⟨⟨n, uliftYonedaEquiv y⟩, t⟩, ?_⟩
    simpa only [q, Equiv.symm_apply_apply] using ht
  exact hsurj.compactSpace hq

/-- A semi-simplicial subset of a finite semi-simplicial set is finite. -/
theorem isFinite_of_mono_proof {A B : SemiSSet.{u}} (i : A ⟶ B) [Mono i]
    (hB : B.IsFinite) : A.IsFinite := by
  constructor
  · intro n
    haveI : Finite (B.obj (op (Henry.SemiSimplexCategory.mk n))) := hB.1 n
    apply Finite.of_injective (i.app (op (Henry.SemiSimplexCategory.mk n)))
    intro x y h
    have hi : Mono (i.app (op (Henry.SemiSimplexCategory.mk n))) :=
      (NatTrans.mono_iff_mono_app (f := i)).mp (inferInstance : Mono i) _
    exact (mono_iff_injective _).mp hi h
  · obtain ⟨N, hN⟩ := hB.2
    refine ⟨N, ?_⟩
    intro n hn
    letI : IsEmpty (B.obj (op (Henry.SemiSimplexCategory.mk n))) := hN n hn
    exact ⟨fun x => isEmptyElim (i.app (op (Henry.SemiSimplexCategory.mk n)) x)⟩

/-- The image of a finite semi-simplicial set is finite. -/
theorem isFinite_range_proof {A B : SemiSSet.{u}} (f : A ⟶ B) (hA : A.IsFinite) :
    SemiSSet.IsFinite (Subfunctor.range f).toFunctor := by
  constructor
  · intro n
    haveI : Finite (A.obj (op (Henry.SemiSimplexCategory.mk n))) := hA.1 n
    apply Finite.of_surjective
      (fun x : A.obj (op (Henry.SemiSimplexCategory.mk n)) =>
        ⟨f.app (op (Henry.SemiSimplexCategory.mk n)) x, ⟨x, rfl⟩⟩)
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · obtain ⟨N, hN⟩ := hA.2
    refine ⟨N, ?_⟩
    intro n hn
    letI : IsEmpty (A.obj (op (Henry.SemiSimplexCategory.mk n))) := hN n hn
    refine ⟨?_⟩
    rintro ⟨y, ⟨x, rfl⟩⟩
    exact isEmptyElim x

/-- The union of two finite semi-simplicial subsets is finite. -/
theorem isFinite_sup_proof {B : SemiSSet.{u}} (S T : Subfunctor B)
    (hS : SemiSSet.IsFinite S.toFunctor) (hT : SemiSSet.IsFinite T.toFunctor) :
    SemiSSet.IsFinite (S ⊔ T).toFunctor := by
  constructor
  · intro n
    let k := op (Henry.SemiSimplexCategory.mk n)
    haveI : Finite (S.toFunctor.obj k) := hS.1 n
    haveI : Finite (T.toFunctor.obj k) := hT.1 n
    change Finite {x : B.obj k // x ∈ (S ⊔ T).obj k}
    rw [Subfunctor.max_obj]
    apply Finite.of_surjective
      (fun x : S.toFunctor.obj k ⊕ T.toFunctor.obj k =>
        match x with
        | Sum.inl x => (⟨x.1, Or.inl x.2⟩ : {x : B.obj k // x ∈ S.obj k ∪ T.obj k})
        | Sum.inr x => (⟨x.1, Or.inr x.2⟩ : {x : B.obj k // x ∈ S.obj k ∪ T.obj k}))
    intro x
    rcases x with ⟨x, hx | hx⟩
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  · obtain ⟨N₁, hN₁⟩ := hS.2
    obtain ⟨N₂, hN₂⟩ := hT.2
    refine ⟨max N₁ N₂, ?_⟩
    intro n hn
    have hn₁ : N₁ < n := lt_of_le_of_lt (Nat.le_max_left _ _) hn
    have hn₂ : N₂ < n := lt_of_le_of_lt (Nat.le_max_right _ _) hn
    have hEmptyS : IsEmpty (S.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) :=
      hN₁ n hn₁
    have hEmptyT : IsEmpty (T.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) :=
      hN₂ n hn₂
    refine ⟨?_⟩
    rintro ⟨x, hx⟩
    rw [Subfunctor.max_obj] at hx
    rcases hx with hx | hx
    · exact False.elim (hEmptyS.false ⟨x, hx⟩)
    · exact False.elim (hEmptyT.false ⟨x, hx⟩)

/-- A semi-simplicial subset with finite levels and a dimension bound is finite. -/
theorem isFinite_of_finite_obj_proof {B : SemiSSet.{u}} (S : Subfunctor B)
    (h₁ : ∀ n : ℕ, (S.obj (op (Henry.SemiSimplexCategory.mk n))).Finite)
    (h₂ : ∃ N : ℕ, ∀ n : ℕ, N < n →
      S.obj (op (Henry.SemiSimplexCategory.mk n)) = ∅) :
    SemiSSet.IsFinite S.toFunctor := by
  constructor
  · intro n
    exact h₁ n
  · obtain ⟨N, hN⟩ := h₂
    refine ⟨N, ?_⟩
    intro n hn
    refine ⟨?_⟩
    rintro ⟨x, hx⟩
    rw [hN n hn] at hx
    exact hx

/-- The realization of a semi-simplicial map is simplicial. -/
theorem isSimplicial_realization_map_proof {Y X : SemiSSet.{u}} (φ : Y ⟶ X) :
    IsSimplicial (realization.map φ) := by
  apply isSimplicial_of_forall
  intro n y
  refine ⟨n, y ≫ φ, id, ?_⟩
  calc
    simplexChar y ≫ realization.map φ = simplexChar (y ≫ φ) :=
      (simplexChar_comp y φ).symm
    _ = vertexMap (id : Fin (n + 1) → Fin (n + 1)) ≫ simplexChar (y ≫ φ) := by
      rw [vertexMap_id]
      rw [Category.id_comp]

/-- Composite of affine vertex maps. -/
theorem vertexMap_comp_proof {n m k : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (w : Fin (m + 1) → Fin (k + 1)) :
    vertexMap.{u} v ≫ vertexMap w = vertexMap (w ∘ v) := by
  ext x
  obtain ⟨x⟩ := x
  apply ULift.ext
  change Convexity.StdSimplex.map (R := ℝ) w
      (Convexity.StdSimplex.map (R := ℝ) v x) =
    Convexity.StdSimplex.map (R := ℝ) (w ∘ v) x
  exact (Convexity.StdSimplex.map_comp x v w).symm

end HomotopyHypothesis.Approximation.FiniteRealization

#print axioms HomotopyHypothesis.Approximation.FiniteRealization.compactSpace_realization_of_isFinite'_proof
#print axioms HomotopyHypothesis.Approximation.FiniteRealization.isFinite_of_mono_proof
#print axioms HomotopyHypothesis.Approximation.FiniteRealization.isFinite_range_proof
#print axioms HomotopyHypothesis.Approximation.FiniteRealization.isFinite_sup_proof
#print axioms HomotopyHypothesis.Approximation.FiniteRealization.isFinite_of_finite_obj_proof
#print axioms HomotopyHypothesis.Approximation.FiniteRealization.isSimplicial_realization_map_proof
#print axioms HomotopyHypothesis.Approximation.FiniteRealization.vertexMap_comp_proof
