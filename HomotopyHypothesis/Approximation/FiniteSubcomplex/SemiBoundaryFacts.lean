import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.FiniteSubcomplex

private theorem semiSimplex_mono_injective {m n : ℕ}
    (f : HomotopyHypothesis.Henry.SemiSimplexCategory.mk m ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) :
    Function.Injective f.hom.toOrderHom := by
  letI : Mono f.hom := f.property
  exact (SimplexCategory.mono_iff_injective).mp inferInstance

theorem semiSimplex_endomorphism_eq_id (n : ℕ)
    (f : HomotopyHypothesis.Henry.SemiSimplexCategory.mk n ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) : f = 𝟙 _ := by
  apply HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map_injective
  letI : Mono f.hom := f.property
  exact SimplexCategory.eq_id_of_mono f.hom

theorem semiBoundary_obj_eq_univ_of_lt
    (n : ℕ) (m : ℕ) (hmn : m < n) :
    (HomotopyHypothesis.Henry.SemiSSet.boundary n).obj
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro f
  have hnot : ∃ j : Fin (n + 1), ∀ k : Fin (m + 1),
      f.down.hom.toOrderHom k ≠ j := by
    by_contra h
    push_neg at h
    have hs : Function.Surjective f.down.hom.toOrderHom := fun j => h j
    have hcard := Fintype.card_le_of_surjective f.down.hom.toOrderHom hs
    simp only [Fintype.card_fin] at hcard
    omega
  rcases hnot with ⟨j, hj⟩
  exact ⟨j, by simpa [Set.mem_range] using hj⟩

theorem semiBoundary_obj_eq_empty_of_eq
    (n : ℕ) :
    (HomotopyHypothesis.Henry.SemiSSet.boundary n).obj
      (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨j, hj⟩ := hf
  have hsurj : Function.Surjective f.down.hom.toOrderHom :=
    Finite.injective_iff_surjective.mp (semiSimplex_mono_injective f.down)
  obtain ⟨k, hk⟩ := hsurj j
  exact hj ⟨k, hk⟩

theorem semiStdSimplex_obj_eq_empty_of_lt
    (n m : ℕ) (hnm : n < m) :
    IsEmpty ((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).obj
        (op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))) := by
  classical
  refine ⟨fun f => ?_⟩
  have hle : m ≤ n := by
    letI : Mono f.down.hom := f.down.property
    exact SimplexCategory.len_le_of_mono f.down.hom
  omega

theorem semiBoundary_element_dim_lt
    {U : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ} {n : ℕ}
    {x : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).obj U}
    (hx : x ∈ (HomotopyHypothesis.Henry.SemiSSet.boundary n).obj U) :
    U.unop.obj.len < n := by
  classical
  obtain ⟨j, hj⟩ := hx
  let f := ULift.down x
  have hle : U.unop.obj.len ≤ n := by
    letI : Mono f.hom := f.property
    exact SimplexCategory.len_le_of_mono f.hom
  by_contra hlt
  have hEq : U.unop.obj.len = n := by omega
  subst n
  have hinj : Function.Injective f.hom.toOrderHom := by
    letI : Mono f.hom := f.property
    exact (SimplexCategory.mono_iff_injective).mp inferInstance
  have hsurj : Function.Surjective f.hom.toOrderHom :=
    Finite.injective_iff_surjective.mp hinj
  obtain ⟨k, hk⟩ := hsurj j
  exact hj ⟨k, hk⟩

end HomotopyHypothesis.Approximation.FiniteSubcomplex
