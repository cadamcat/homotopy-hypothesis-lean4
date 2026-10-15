import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismRelative.Boundary
import HomotopyHypothesis.Approximation.Topological.CylinderCellProof.Part1
/-!
# Attaching a simplex along its boundary

A semi-simplicial subset enlarged by one simplex is a pushout of the boundary inclusion.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismRelative

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological

/-- A proper face of a representable has smaller dimension. -/
theorem boundary_face_mem_iff {k n : ℕ}
    (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n) :
    ULift.up.{u, 0} θ ∈ (Henry.SemiSSet.boundary.{u} n).obj
      (op (Henry.SemiSimplexCategory.mk k)) ↔ k ≠ n := by
  classical
  change (∃ j, j ∉ Set.range θ.1.toOrderHom) ↔ k ≠ n
  constructor
  · rintro ⟨j, hj⟩ rfl
    have hθ := semiSimplex_endo_eq_id θ
    exact hj ⟨j, by simp [hθ]⟩
  · intro hkn
    by_contra hnot
    have hs : Function.Surjective θ.1.toOrderHom := by
      intro i
      by_contra hi
      exact hnot ⟨i, hi⟩
    have hle : k ≤ n := by
      simpa only [SimplexCategory.len_mk] using
        (@SimplexCategory.len_le_of_mono _ _ θ.1 θ.2)
    have hge := Fintype.card_le_of_surjective _ hs
    simp only [Fintype.card_fin] at hge
    omega

section Cell

variable {W : SemiSSet.{u}} {A B : Subfunctor W} {n : ℕ}
  (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
  (hfaces : ∀ (k : ℕ)
    (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n),
    k ≠ n → W.map θ.op y ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)))

/-- The boundary of a simplex whose proper faces lie in the subset. -/
noncomputable def cellBoundaryMap :
    (Henry.SemiSSet.boundary.{u} n).toFunctor ⟶ A.toFunctor :=
  Subfunctor.lift ((Henry.SemiSSet.boundary.{u} n).ι ≫ uliftYonedaEquiv.symm y) (by
    intro i z hz
    obtain ⟨s, rfl⟩ := hz
    obtain ⟨⟨⟨k⟩⟩⟩ := i
    exact hfaces k s.1.down ((boundary_face_mem_iff.{u} s.1.down).1 s.2))

/-- The characteristic map of a simplex in a semi-simplicial subset. -/
noncomputable def cellSimplexMap
    (hyB : y ∈ B.obj (op (Henry.SemiSimplexCategory.mk n))) :
    Henry.SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶ B.toFunctor :=
  uliftYonedaEquiv.symm ⟨y, hyB⟩

theorem cellBoundaryMap_comm (h : A ≤ B)
    (hyB : y ∈ B.obj (op (Henry.SemiSimplexCategory.mk n))) :
    cellBoundaryMap y hfaces ≫ Subfunctor.homOfLe h =
      (Henry.SemiSSet.boundary.{u} n).ι ≫ cellSimplexMap y hyB := by
  ext i s
  rfl

/-- Adding a simplex with all proper faces already present is a boundary pushout. -/
theorem isPushout_cellAttachment (h : A ≤ B)
    (hyA : y ∉ A.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hyB : y ∈ B.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hB : ∀ (k : ℕ) (z : W.obj (op (Henry.SemiSimplexCategory.mk k))),
      z ∈ B.obj (op (Henry.SemiSimplexCategory.mk k)) →
        z ∈ A.obj (op (Henry.SemiSimplexCategory.mk k)) ∨
          ∃ hk : k = n, hk ▸ z = y) :
    IsPushout (cellBoundaryMap y hfaces) (Henry.SemiSSet.boundary.{u} n).ι
      (Subfunctor.homOfLe h) (cellSimplexMap y hyB) := by
  classical
  have hcomm := cellBoundaryMap_comm y hfaces h hyB
  apply IsPushout.of_forall_isPushout_app
  intro i
  obtain ⟨⟨⟨k⟩⟩⟩ := i
  apply Types.isPushout_of_isPullback_of_mono'
  · apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨congrArg (fun f => f.app (op (Henry.SemiSimplexCategory.mk k))) hcomm,
      ?_, ?_⟩
    · intro x z hxz
      exact Subtype.ext hxz.2
    · intro a θ hsame
      have hval := congrArg Subtype.val hsame
      change a.1 = W.map θ.down.op y at hval
      have hmem : θ ∈ (Henry.SemiSSet.boundary.{u} n).obj
          (op (Henry.SemiSimplexCategory.mk k)) := by
        apply (boundary_face_mem_iff.{u} θ.down).2
        intro hkn
        subst k
        have hv : a.1 = y := by
          simpa [semiSimplex_endo_eq_id θ.down] using hval
        exact hyA (hv ▸ a.2)
      exact ⟨⟨θ, hmem⟩, Subtype.ext hval.symm, rfl⟩
  · ext z
    simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    rcases hB k z.1 z.2 with hzA | ⟨hk, hzy⟩
    · exact Or.inl ⟨⟨z.1, hzA⟩, Subtype.ext rfl⟩
    · subst k
      refine Or.inr ⟨ULift.up (𝟙 (Henry.SemiSimplexCategory.mk n)), ?_⟩
      apply Subtype.ext
      change W.map (𝟙 (Henry.SemiSimplexCategory.mk n)).op y = z.1
      simpa using hzy.symm
  · intro θ θ' hθ _ _
    have hkn : k = n := by
      by_contra hkn
      have hm := (boundary_face_mem_iff.{u} θ.down).2 hkn
      exact hθ ⟨⟨θ, hm⟩, rfl⟩
    subst k
    apply ULift.ext
    rw [semiSimplex_endo_eq_id θ.down, semiSimplex_endo_eq_id θ'.down]

end Cell

#print axioms isPushout_cellAttachment

end HomotopyHypothesis.Approximation.DerivedPrismRelative
