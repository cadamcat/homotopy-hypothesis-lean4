import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeLiftOfHomotopyEquivalence
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Gluing.RelativeHomotopy.GlueHomotopy
import HomotopyHypothesis.Realization.SemisimplicialComparison.TopFacts
universe u

open CategoryTheory Limits TopCat HomotopyHypothesis.Henry HomotopyHypothesis.Homotopy.ExtensionPrinciple

namespace HomotopyHypothesis.Gluing.PushoutHomotopy

theorem inverse_under_base {A B B' : TopCat.{u}}
    (i : A ⟶ B) (i' : A ⟶ B')
    (hi : Top.relativeFiniteCellComplexes i)
    (hi' : Top.relativeFiniteCellComplexes i')
    (vB : B ⟶ B') (hvB : Top.homotopyEquivalences vB)
    (hc : i ≫ vB = i') :
    ∃ (uB : B' ⟶ B),
      i' ≫ uB = i ∧
      (uB ≫ vB).hom.HomotopicRel (ContinuousMap.id B') (Set.range i'.hom) ∧
      (vB ≫ uB).hom.HomotopicRel (ContinuousMap.id B) (Set.range i.hom) := by
  have hcomm : i ≫ vB = i' ≫ 𝟙 B' := by rw [hc, Category.comp_id]
  obtain ⟨uB, huB, hrel1⟩ := (Packages.relativeLift_of_homotopyEquivalence i' hi' vB hvB).1 i (𝟙 B') hcomm
  have hrel1' : (uB ≫ vB).hom.HomotopicRel (ContinuousMap.id B') (Set.range i'.hom) := by
    simpa using hrel1
  have h_comp_i : i ≫ (vB ≫ uB) = i ≫ 𝟙 B := by
    calc
      i ≫ (vB ≫ uB) = (i ≫ vB) ≫ uB := (Category.assoc _ _ _).symm
      _ = i' ≫ uB := by rw [hc]
      _ = i := huB
      _ = i ≫ 𝟙 B := (Category.comp_id _).symm
  have h_post : ((vB ≫ uB) ≫ vB).hom.HomotopicRel ((𝟙 B) ≫ vB).hom (Set.range i.hom) := by
    have heq1 : ((vB ≫ uB) ≫ vB) = vB ≫ (uB ≫ vB) := Category.assoc _ _ _
    have heq2 : (𝟙 B) ≫ vB = vB := Category.id_comp _
    rw [heq1, heq2]
    obtain ⟨R⟩ := hrel1'
    refine ⟨{
      toHomotopy := R.toHomotopy.compContinuousMap vB.hom
      prop' := by
        intro t x hx
        rcases hx with ⟨a, rfl⟩
        have hvi : vB.hom (i.hom a) ∈ Set.range i'.hom := by
          refine ⟨a, ?_⟩
          have hh := congrArg (fun m : A ⟶ B' => m.hom a) hc
          exact hh.symm
        exact R.prop t (vB.hom (i.hom a)) hvi
    }⟩
  have hrel2 := (Packages.relativeLift_of_homotopyEquivalence i hi vB hvB).2 (vB ≫ uB) (𝟙 B) h_comp_i h_post
  exact ⟨uB, huB, hrel1', hrel2⟩

lemma homotopicRel_postcomp {X Y Z : TopCat.{u}} {f g : X ⟶ Y} {S : Set X}
    (H : f.hom.HomotopicRel g.hom S) (k : Y ⟶ Z) :
    (f ≫ k).hom.HomotopicRel (g ≫ k).hom S := by
  obtain ⟨R⟩ := H
  refine ⟨{
    toHomotopy := (ContinuousMap.Homotopy.refl k.hom).comp R.toHomotopy
    prop' := by
      intro t x hx
      have hR : R (t, x) = f.hom x := R.eq_fst t hx
      change k.hom (R (t, x)) = (f ≫ k).hom x
      rw [hR]
      rfl
  }⟩

theorem homotopyEquivalence_of_isPushout_under
    {A B C P B' P' : TopCat.{u}}
    (i : A ⟶ B) (f : A ⟶ C) (k : B ⟶ P) (j : C ⟶ P)
    (i' : A ⟶ B') (k' : B' ⟶ P') (j' : C ⟶ P')
    (h : IsPushout i f k j) (h' : IsPushout i' f k' j')
    (hi : Top.relativeFiniteCellComplexes i)
    (hi' : Top.relativeFiniteCellComplexes i')
    (vB : B ⟶ B') (hvB : Top.homotopyEquivalences vB)
    (hc : i ≫ vB = i')
    (φ : P ⟶ P') (hφk : k ≫ φ = vB ≫ k') (hφj : j ≫ φ = j') :
    Top.homotopyEquivalences φ := by
  obtain ⟨uB, huB, hrel1, hrel2⟩ := inverse_under_base i i' hi hi' vB hvB hc
  have hcomp : i' ≫ (uB ≫ k) = f ≫ j := by
    calc
      i' ≫ (uB ≫ k) = (i' ≫ uB) ≫ k := by simp only [Category.assoc]
      _ = i ≫ k := by rw [huB]
      _ = f ≫ j := h.w
  let ψ : P' ⟶ P := h'.desc (uB ≫ k) j hcomp
  have hψk' : k' ≫ ψ = uB ≫ k := h'.inl_desc (uB ≫ k) j hcomp
  have hψj' : j' ≫ ψ = j := h'.inr_desc (uB ≫ k) j hcomp
  -- Show φ ≫ ψ is homotopic to 𝟙 P
  have hj_comp : j ≫ (φ ≫ ψ) = j ≫ 𝟙 P := by
    calc
      j ≫ (φ ≫ ψ) = (j ≫ φ) ≫ ψ := (Category.assoc _ _ _).symm
      _ = j' ≫ ψ := by rw [hφj]
      _ = j := hψj'
      _ = j ≫ 𝟙 P := (Category.comp_id _).symm
  have hk_comp : k ≫ (φ ≫ ψ) = (vB ≫ uB) ≫ k := by
    calc
      k ≫ (φ ≫ ψ) = (k ≫ φ) ≫ ψ := (Category.assoc _ _ _).symm
      _ = (vB ≫ k') ≫ ψ := by rw [hφk]
      _ = vB ≫ (k' ≫ ψ) := Category.assoc _ _ _
      _ = vB ≫ (uB ≫ k) := by rw [hψk']
      _ = (vB ≫ uB) ≫ k := (Category.assoc _ _ _).symm
  have hk_rel : (k ≫ (φ ≫ ψ)).hom.HomotopicRel (k ≫ 𝟙 P).hom (Set.range i.hom) := by
    rw [hk_comp, Category.comp_id]
    exact homotopicRel_postcomp hrel2 k
  have h_phi_psi_rel := Gluing.RelativeHomotopy.homotopicRel_of_isPushout_proof h hj_comp hk_rel
  obtain ⟨H_phi_psi⟩ := h_phi_psi_rel
  have h_phi_psi : (φ ≫ ψ).hom.Homotopic (𝟙 P : P ⟶ P).hom := ⟨H_phi_psi.toHomotopy⟩
  -- Show ψ ≫ φ is homotopic to 𝟙 P'
  have hj'_comp : j' ≫ (ψ ≫ φ) = j' ≫ 𝟙 P' := by
    calc
      j' ≫ (ψ ≫ φ) = (j' ≫ ψ) ≫ φ := (Category.assoc _ _ _).symm
      _ = j ≫ φ := by rw [hψj']
      _ = j' := hφj
      _ = j' ≫ 𝟙 P' := (Category.comp_id _).symm
  have hk'_comp : k' ≫ (ψ ≫ φ) = (uB ≫ vB) ≫ k' := by
    calc
      k' ≫ (ψ ≫ φ) = (k' ≫ ψ) ≫ φ := (Category.assoc _ _ _).symm
      _ = (uB ≫ k) ≫ φ := by rw [hψk']
      _ = uB ≫ (k ≫ φ) := Category.assoc _ _ _
      _ = uB ≫ (vB ≫ k') := by rw [hφk]
      _ = (uB ≫ vB) ≫ k' := (Category.assoc _ _ _).symm
  have hk'_rel : (k' ≫ (ψ ≫ φ)).hom.HomotopicRel (k' ≫ 𝟙 P').hom (Set.range i'.hom) := by
    rw [hk'_comp, Category.comp_id]
    exact homotopicRel_postcomp hrel1 k'
  have h_psi_phi_rel := Gluing.RelativeHomotopy.homotopicRel_of_isPushout_proof h' hj'_comp hk'_rel
  obtain ⟨H_psi_phi⟩ := h_psi_phi_rel
  have h_psi_phi : (ψ ≫ φ).hom.Homotopic (𝟙 P' : P' ⟶ P').hom := ⟨H_psi_phi.toHomotopy⟩
  exact ⟨ψ, h_phi_psi, h_psi_phi⟩

end HomotopyHypothesis.Gluing.PushoutHomotopy
