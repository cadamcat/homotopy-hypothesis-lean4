import Mathlib.CategoryTheory.Limits.Types.Pushouts
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.HornAttachmentStatement
universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Horn.Attachment

/-- An embedded simplex meeting a subfunctor in a horn is adjoined by a horn pushout. -/
theorem hornAttachmentStatement_proof :
    HomotopyHypothesis.Approximation.Zeeman.HornAttachmentStatement := by
  refine fun {C} A n k σ hσ hpre => ?_
  let D := HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
    (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (n + 1))
  let H : Subfunctor D := HomotopyHypothesis.Henry.SemiSSet.horn (n + 1) k
  let B := A ⊔ Subfunctor.range σ
  have hle : Subfunctor.range (H.ι ≫ σ) ≤ A := by
    rw [Subfunctor.range_comp, Subfunctor.range_ι]
    exact (Subfunctor.image_le_iff H σ A).2 (by rw [hpre])
  let a : H.toFunctor ⟶ A.toFunctor := Subfunctor.lift (H.ι ≫ σ) hle
  let i : A.toFunctor ⟶ B.toFunctor := Subfunctor.homOfLe le_sup_left
  let b : D ⟶ B.toFunctor := Subfunctor.lift σ le_sup_right
  have sq : IsPushout H.ι a b i := by
    apply CategoryTheory.IsPushout.of_forall_isPushout_app
    intro X
    have hpull : IsPullback (H.ι.app X) (a.app X) (b.app X) (i.app X) := by
      rw [CategoryTheory.Limits.Types.isPullback_iff]
      constructor
      · ext x
        apply Subtype.ext
        rfl
      constructor
      · intro x y hxy
        apply Subtype.ext
        exact hxy.1
      · intro x y hxy
        have hval : σ.app X x = y.1 := by
          have h := congrArg (fun z : B.obj X => z.1) hxy
          change σ.app X x = y.1 at h
          exact h
        have hyA : σ.app X x ∈ A.obj X := by
          rw [hval]
          exact y.2
        have hyH : x ∈ (A.preimage σ).obj X := by
          change σ.app X x ∈ A.obj X
          exact hyA
        have hyHorn : x ∈ H.obj X := by
          rw [hpre] at hyH
          exact hyH
        refine ⟨⟨x, hyHorn⟩, rfl, ?_⟩
        apply Subtype.ext
        simpa [a] using hval
    have hσinj : Function.Injective (σ.app X) := by
      exact (mono_iff_injective (σ.app X)).mp
        (inferInstance : Mono (σ.app X))
    have hbmono : Mono (b.app X) :=
      (mono_iff_injective (b.app X)).2 (by
        intro x y hxy
        apply hσinj
        have h := congrArg (fun z : B.obj X => z.1) hxy
        change σ.app X x = σ.app X y at h
        exact h)
    have hcover : Set.range (b.app X) ⊔ Set.range (i.app X) = Set.univ := by
      change Set.range (b.app X) ∪ Set.range (i.app X) = Set.univ
      apply Set.eq_univ_iff_forall.mpr
      intro z
      have hz := z.property
      change z.1 ∈ A.obj X ∪ Set.range (σ.app X) at hz
      rcases hz with hzA | ⟨y, hy⟩
      · apply Set.mem_union_right
        refine ⟨⟨z.1, hzA⟩, ?_⟩
        apply Subtype.ext
        rfl
      · apply Set.mem_union_left
        refine ⟨y, ?_⟩
        apply Subtype.ext
        exact hy
    exact CategoryTheory.Limits.Types.isPushout_of_isPullback_of_mono'
      hpull hcover (by
        intro x y hx hy hxy
        apply Subtype.ext
        exact congrArg (fun z : B.obj X => z.1) hxy)
  have hhorn : HomotopyHypothesis.Henry.SemiSSet.hornInclusions H.ι := by
    exact MorphismProperty.ofHoms.mk
      (⟨n, k⟩ : Σ n : ℕ, Fin (n + 2))
  change HomotopyHypothesis.Henry.SemiSSet.anodyne i
  unfold HomotopyHypothesis.Henry.SemiSSet.anodyne
  exact MorphismProperty.multiplicativeClosure.of _
    (Or.inl (HomotopyHypothesis.Henry.SemiSSet.hornInclusions.pushouts_mk sq.flip hhorn))

example : HomotopyHypothesis.Approximation.Zeeman.HornAttachmentStatement.{u} :=
  @hornAttachmentStatement_proof.{u}

#print axioms hornAttachmentStatement_proof

end HomotopyHypothesis.Horn.Attachment
