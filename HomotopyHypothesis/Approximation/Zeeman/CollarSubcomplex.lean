import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.CollarVertices
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RetainedFull
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# The collar subcomplex and its exterior complement

The collar subcomplex consists of the derived simplices whose chosen image
vertices all lie in the retained subcomplex. The faces of simplices outside
it form an exterior complement. These two subcomplexes cover the derived
complex, and the exterior complement has no retained vertices.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The subcomplex on which all collar vertex choices belong to L. -/
noncomputable def relativeCollarSubcomplex (K : SemiSSet.{u}) (L : Subfunctor K) :
    Subfunctor (relativeDerived K L) where
  obj X a := ∀ i, relativeCollarVertex (a.val i) ∈ L.obj (op (Henry.SemiSimplexCategory.mk 0))
  map f := by
    intro a ha i
    exact ha (f.unop.hom.toOrderHom i)

/-- A simplex with a retained entry lies in the collar subcomplex. -/
theorem relativeCollarSubcomplex_mem_of_retainedEntry {K : SemiSSet.{u}}
    {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : ∃ i v, a.val i = Sum.inl v) :
    a ∈ (relativeCollarSubcomplex K L).obj (op (Henry.SemiSimplexCategory.mk n)) :=
  relativeCollarVertex_mem_of_retainedEntry a ha

/-- The collar subcomplex contains the retained copy of L. -/
theorem retained_le_relativeCollarSubcomplex {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) :
    Subfunctor.range (relativeDerivedInclusion hK L) ≤ relativeCollarSubcomplex K L := by
  intro X a ha
  obtain ⟨x, rfl⟩ := ha
  intro i
  change relativeCollarVertex (Sum.inl (vertex x i) : RelativeVertex K L) ∈ L.obj _
  rw [relativeCollarVertex_retained]
  exact (vertex x i).property

/-- The collar subcomplex is full in the derived complex. -/
theorem relativeCollarSubcomplex_isFull {K : SemiSSet.{u}} (L : Subfunctor K) :
    IsFullSubcomplex (relativeCollarSubcomplex K L) := by
  intro n a ha i
  exact ha i (0 : Fin 1)

/-- All faces of simplices outside a given subcomplex. -/
def exteriorSubcomplex {W : SemiSSet.{u}} (A : Subfunctor W) : Subfunctor W where
  obj X a := ∃ s : Simplex W, s.2 ∉ A.obj (op (Henry.SemiSimplexCategory.mk s.1)) ∧
    ∃ θ : X.unop ⟶ Henry.SemiSimplexCategory.mk s.1, W.map θ.op s.2 = a
  map f := by
    rintro a ⟨s, hs, θ, hθ⟩
    refine ⟨s, hs, f.unop ≫ θ, ?_⟩
    rw [op_comp, CategoryTheory.Functor.map_comp]
    exact congrArg (W.map f) hθ

/-- A subcomplex and its exterior complement cover the whole complex. -/
theorem sup_exteriorSubcomplex {W : SemiSSet.{u}} (A : Subfunctor W) :
    A ⊔ exteriorSubcomplex A = ⊤ := by
  classical
  ext X a
  constructor
  · intro _
    trivial
  · intro _
    by_cases ha : a ∈ A.obj X
    · exact Or.inl ha
    · refine Or.inr ⟨⟨X.unop.obj.len, a⟩, ha, 𝟙 _, ?_⟩
      change W.map (𝟙 X) a = a
      exact congrArg (fun f => f a) (W.map_id X)

/-- A subcomplex of a finite semi-simplicial set is finite. -/
theorem subfunctor_isFinite {W : SemiSSet.{u}} (hW : W.IsFinite) (A : Subfunctor W) :
    Henry.SemiSSet.IsFinite A.toFunctor := by
  refine ⟨?_, ?_⟩
  · intro n
    haveI := hW.1 n
    change Finite {x : W.obj (op (Henry.SemiSimplexCategory.mk n)) // x ∈ A.obj _}
    infer_instance
  · obtain ⟨N, hN⟩ := hW.2
    refine ⟨N, ?_⟩
    intro n hn
    haveI := hN n hn
    exact ⟨fun x => isEmptyElim x.val⟩

/-- The exterior complement of the collar subcomplex. -/
noncomputable def relativeCollarExterior (K : SemiSSet.{u}) (L : Subfunctor K) :
    Subfunctor (relativeDerived K L) :=
  exteriorSubcomplex (relativeCollarSubcomplex K L)

/-- The collar and exterior subcomplexes cover the relative derived complex. -/
theorem relativeCollar_sup_exterior {K : SemiSSet.{u}} (L : Subfunctor K) :
    relativeCollarSubcomplex K L ⊔ relativeCollarExterior K L = ⊤ :=
  sup_exteriorSubcomplex _

/-- No simplex of the exterior complement has a retained entry. -/
theorem relativeCollarExterior_no_retainedEntry {K : SemiSSet.{u}}
    {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : a ∈ (relativeCollarExterior K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    ∀ i, ¬ ∃ v, a.val i = Sum.inl v := by
  obtain ⟨s, hs, θ, hθ⟩ := ha
  rintro i ⟨v, hv⟩
  apply hs
  apply relativeCollarSubcomplex_mem_of_retainedEntry
  exact ⟨θ.hom.toOrderHom i, v, (congrArg (fun b => b.val i) hθ).trans hv⟩

/-- The exterior complement is disjoint from the retained subcomplex. -/
theorem relativeCollarExterior_inf_retained {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) :
    relativeCollarExterior K L ⊓ Subfunctor.range (relativeDerivedInclusion hK L) = ⊥ := by
  ext X a
  constructor
  · rintro ⟨ha, hret⟩
    have hi := (relativeDerivedInclusion_mem_range_iff hK L a).mp hret 0
    exact relativeCollarExterior_no_retainedEntry a ha 0 hi
  · intro h
    exact h.elim

/-- Both collar subcomplexes are finite when the original complex is finite. -/
theorem relativeCollarSubcomplexes_isFinite {K : SemiSSet.{u}}
    (hK : K.IsFinite) (L : Subfunctor K) :
    Henry.SemiSSet.IsFinite (relativeCollarSubcomplex K L).toFunctor ∧
      Henry.SemiSSet.IsFinite (relativeCollarExterior K L).toFunctor :=
  ⟨subfunctor_isFinite (relativeDerived_isFinite hK L) _,
    subfunctor_isFinite (relativeDerived_isFinite hK L) _⟩

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarSubcomplex_isFull
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollar_sup_exterior
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarExterior_inf_retained
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarSubcomplexes_isFinite
