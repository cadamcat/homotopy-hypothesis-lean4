import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Homeomorph.Lemmas
universe u

open CategoryTheory Limits TopCat Topology Set

namespace HomotopyHypothesis.Approximation.FiniteSubcomplex

/-- A compact image in a sequential union of embedded, T1 stages is contained in one stage. -/
theorem compact_map_factors_through_stage
    {F : ℕ ⥤ TopCat.{u}} {c : Cocone F} (hc : IsColimit c)
    {K : TopCat.{u}} [CompactSpace K] (g : K ⟶ c.pt)
    (hT1 : ∀ n, T1Space (F.obj n))
    (hEmb : ∀ n, IsEmbedding (c.ι.app n).hom) :
    ∃ n, ∃ g' : K ⟶ F.obj n, g' ≫ c.ι.app n = g := by
  classical
  let i (n : ℕ) : ((F.obj n : TopCat) : Type u) → c.pt := (c.ι.app n).hom
  have hImage : ∃ n, ∀ x : K, g.hom x ∈ Set.range (i n) := by
    by_contra h
    push_neg at h
    let hmiss : ∀ n, ∃ x : K, g.hom x ∉ Set.range (i n) := h
    let p (n : ℕ) : c.pt := g.hom (Classical.choose (hmiss n))
    have hp_miss (n : ℕ) : p n ∉ Set.range (i n) := Classical.choose_spec (hmiss n)
    let S : Set c.pt := Set.range p
    have hstage_inter (m : ℕ) : (S ∩ Set.range (i m)).Finite := by
      have himage : (p '' {n : ℕ | n < m}).Finite :=
        (Set.finite_lt_nat m).image p
      apply himage.subset
      rintro y ⟨⟨n, rfl⟩, ⟨x, hx⟩⟩
      have hnm : n < m := by
        by_contra hnm
        have hmn : m ≤ n := Nat.le_of_not_gt hnm
        have hy' : p n ∈ Set.range (i n) := by
          refine ⟨(F.map (homOfLE hmn)).hom x, ?_⟩
          have hnat := c.w (homOfLE hmn)
          have hnat' := congrArg (fun f : F.obj m ⟶ c.pt => f.hom x) hnat
          change i n ((F.map (homOfLE hmn)).hom x) = i m x at hnat'
          exact hnat'.trans hx
        exact hp_miss n hy'
      exact ⟨n, hnm, rfl⟩
    have hpre_finite (m : ℕ) : (i m ⁻¹' S).Finite := by
      have hpre_subset : i m ⁻¹' S ⊆ i m ⁻¹' (S ∩ Set.range (i m)) := by
        intro x hx
        exact ⟨hx, ⟨x, rfl⟩⟩
      have hfin : (i m ⁻¹' (S ∩ Set.range (i m))).Finite := by
        exact (hstage_inter m).preimage_embedding
          ⟨i m, (hEmb m).injective⟩
      exact hfin.subset hpre_subset
    have hSclosed : IsClosed S := by
      apply (TopCat.isClosed_iff_of_isColimit c hc S).2
      intro m
      letI : T1Space (F.obj m) := hT1 m
      exact (hpre_finite m).isClosed
    have hScompact : IsCompact S := by
      have hG : IsCompact (Set.range g.hom) := isCompact_range g.hom.continuous
      apply hG.of_isClosed_subset hSclosed
      rintro y ⟨n, rfl⟩
      exact ⟨Classical.choose (hmiss n), rfl⟩
    have hSdiscrete : IsDiscrete S := by
      rw [isDiscrete_iff_forall_mem_exists_isOpen]
      intro x hx
      let Q : Set c.pt := S \ {x}
      have hQclosed : IsClosed Q := by
        apply (TopCat.isClosed_iff_of_isColimit c hc Q).2
        intro m
        letI : T1Space (F.obj m) := hT1 m
        exact ((hpre_finite m).subset (by
          intro y hy
          exact hy.1)).isClosed
      refine ⟨Qᶜ, hQclosed.isOpen_compl, ?_⟩
      ext y
      constructor
      · rintro ⟨hyQ, hyS⟩
        by_contra hne
        apply hyQ
        exact ⟨hyS, by simp [hne]⟩
      · intro hy
        subst y
        simp [Q, hx]
    have hSfinite : S.Finite := hScompact.finite hSdiscrete
    let cT := (forget TopCat).mapCocone c
    have hcT : IsColimit cT := isColimitOfPreserves (forget TopCat) hc
    have hjoint (y : c.pt) : ∃ n, ∃ x : F.obj n, i n x = y := by
      simpa [cT, i] using Types.jointly_surjective_of_isColimit hcT y
    let stage (y : c.pt) : ℕ := Classical.choose (hjoint y)
    let rep (y : c.pt) : F.obj (stage y) :=
      Classical.choose (Classical.choose_spec (hjoint y))
    have hrep (y : c.pt) : i (stage y) (rep y) = y :=
      Classical.choose_spec (Classical.choose_spec (hjoint y))
    let N : ℕ := (hSfinite.toFinset.image stage).sup id
    have hstage_le (y : c.pt) (hy : y ∈ S) : stage y ≤ N := by
      change stage y ≤ (hSfinite.toFinset.image stage).sup id
      apply Finset.le_sup (f := id)
      exact Finset.mem_image.mpr ⟨y, hSfinite.mem_toFinset.mpr hy, rfl⟩
    have hS_in_N : S ⊆ Set.range (i N) := by
      intro y hy
      refine ⟨(F.map (homOfLE (hstage_le y hy))).hom (rep y), ?_⟩
      have hnat := c.w (homOfLE (hstage_le y hy))
      have hnat' := congrArg
        (fun f : F.obj (stage y) ⟶ c.pt => f.hom (rep y)) hnat
      calc
        i N ((F.map (homOfLE (hstage_le y hy))).hom (rep y)) = i (stage y) (rep y) :=
          hnat'
        _ = y := hrep y
    have hcontr : p N ∈ Set.range (i N) := hS_in_N ⟨N, rfl⟩
    exact (hp_miss N hcontr).elim
  obtain ⟨n, hn⟩ := hImage
  let e : F.obj n ≃ₜ Set.range (i n) := (hEmb n).toHomeomorph
  refine ⟨n, ofHom ⟨fun x => e.symm ⟨g.hom x, hn x⟩, ?_⟩, ?_⟩
  · exact e.continuous_symm.comp
      (Continuous.subtype_mk g.hom.continuous (fun x => hn x))
  · ext x
    have hx := e.apply_symm_apply ⟨g.hom x, hn x⟩
    exact congrArg Subtype.val hx

/-- A continuous map factors through an embedding whenever its image lies in the embedding's
range. -/
theorem TopCat.factor_through_embedding_of_range_subset
    {A B C : TopCat.{u}} {f : A ⟶ C} {g : B ⟶ C}
    (hg : IsEmbedding g.hom) (hsub : Set.range f.hom ⊆ Set.range g.hom) :
    ∃ f' : A ⟶ B, f' ≫ g = f := by
  let e : B ≃ₜ Set.range g.hom := hg.toHomeomorph
  refine ⟨TopCat.ofHom ⟨fun x => e.symm ⟨f.hom x, hsub ⟨x, rfl⟩⟩, ?_⟩, ?_⟩
  · exact e.continuous_symm.comp
      (Continuous.subtype_mk f.hom.continuous (fun x => hsub ⟨x, rfl⟩))
  · ext x
    exact congrArg Subtype.val
      (e.apply_symm_apply ⟨f.hom x, hsub ⟨x, rfl⟩⟩)

end HomotopyHypothesis.Approximation.FiniteSubcomplex
