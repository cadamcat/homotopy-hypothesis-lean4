import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.DiscreteSubset
universe u

open CategoryTheory Limits TopCat Topology Set

namespace HomotopyHypothesis.Approximation.FiniteSubcomplex

/-- A closed embedding preserves closed discrete subsets. -/
theorem closedEmbedding_image_closedDiscrete
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsClosedEmbedding f) {Q : Set X}
    (hclosed : IsClosed Q) (hdisc : IsDiscrete Q) :
    IsClosed (f '' Q) ∧ IsDiscrete (f '' Q) := by
  exact ⟨hf.isClosedMap Q hclosed, hdisc.image hf.isInducing⟩

/-- A finite union of closed discrete subsets is closed and discrete. -/
theorem closedDiscrete_union
    {X : Type u} [TopologicalSpace X] {Q R : Set X}
    (hQclosed : IsClosed Q) (hQdisc : IsDiscrete Q)
    (hRclosed : IsClosed R) (hRdisc : IsDiscrete R) :
    IsClosed (Q ∪ R) ∧ IsDiscrete (Q ∪ R) := by
  exact ⟨hQclosed.union hRclosed, hQdisc.union hRdisc hQclosed hRclosed⟩

/-- Adjoining finitely many points to a closed discrete subset of a T₁ space preserves closed
discreteness. -/
theorem closedDiscrete_union_finite_of_t1
    {X : Type u} [TopologicalSpace X] [T1Space X] {Q R : Set X}
    (hclosed : IsClosed Q) (hdisc : IsDiscrete Q) (hR : R.Finite) :
    IsClosed (Q ∪ R) ∧ IsDiscrete (Q ∪ R) := by
  have hRclosed : IsClosed R := hR.isClosed
  have hRdisc : IsDiscrete R := by
    rw [isDiscrete_iff_discreteTopology]
    exact @Finite.instDiscreteTopology R _ inferInstance hR.to_subtype
  exact closedDiscrete_union hclosed hdisc hRclosed hRdisc

/-- Closed embeddings on all successor maps of a sequential diagram imply the same for every
transition map. -/
theorem sequential_map_closedEmbedding
    {F : ℕ ⥤ TopCat.{u}}
    (hstep : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))).hom)
    {m n : ℕ} (f : m ⟶ n) : IsClosedEmbedding (F.map f).hom := by
  have hmn : m ≤ n := f.le
  induction hmn with
  | refl =>
      have hf : f = 𝟙 m := Subsingleton.elim _ _
      simpa [hf] using (Homeomorph.refl (F.obj m)).isClosedEmbedding
  | @step n hmn ih =>
      have hf : f = homOfLE hmn ≫ homOfLE (Nat.le_succ n) := Subsingleton.elim _ _
      rw [hf]
      simp only [F.map_comp]
      have hfun : ⇑((F.map (homOfLE hmn) ≫
          F.map (homOfLE (Nat.le_succ n))).hom) =
          (F.map (homOfLE (Nat.le_succ n))).hom ∘ (F.map (homOfLE hmn)).hom := by
        funext x
        rfl
      rw [hfun]
      exact (hstep n).comp (ih (homOfLE hmn))

/-- In a sequential colimit, closed embeddings at every stage induce closed embeddings from
each stage into the colimit. -/
theorem sequential_colimit_stage_closedEmbedding
    {F : ℕ ⥤ TopCat.{u}} {c : Cocone F} (hc : IsColimit c)
    (hmap : ∀ {m n : ℕ} (f : m ⟶ n), IsClosedEmbedding (F.map f).hom)
    (hinj : ∀ n, Function.Injective (c.ι.app n).hom) :
    ∀ n, IsClosedEmbedding (c.ι.app n).hom := by
  classical
  have hleft {m n : ℕ} (hmn : m ≤ n) (S : Set (F.obj n)) :
      (c.ι.app m).hom ⁻¹' ((c.ι.app n).hom '' S) =
        (F.map (homOfLE hmn)).hom ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hnat := c.w (homOfLE hmn)
      have hnat' := congrArg (fun q : F.obj m ⟶ c.pt => q.hom x) hnat
      change (c.ι.app n).hom ((F.map (homOfLE hmn)).hom x) =
        (c.ι.app m).hom x at hnat'
      have h' : (c.ι.app n).hom y =
          (c.ι.app n).hom ((F.map (homOfLE hmn)).hom x) := hxy.trans hnat'.symm
      have : y = (F.map (homOfLE hmn)).hom x := hinj n h'
      simpa [this] using hy
    · intro hx
      refine ⟨(F.map (homOfLE hmn)).hom x, hx, ?_⟩
      have hnat := c.w (homOfLE hmn)
      have hnat' := congrArg (fun q : F.obj m ⟶ c.pt => q.hom x) hnat
      change (c.ι.app n).hom ((F.map (homOfLE hmn)).hom x) =
        (c.ι.app m).hom x at hnat'
      exact hnat'
  have hright {m n : ℕ} (hnm : n ≤ m) (S : Set (F.obj n)) :
      (c.ι.app m).hom ⁻¹' ((c.ι.app n).hom '' S) =
        (F.map (homOfLE hnm)).hom '' S := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hnat := c.w (homOfLE hnm)
      have hnat' := congrArg (fun q : F.obj n ⟶ c.pt => q.hom y) hnat
      change (c.ι.app m).hom ((F.map (homOfLE hnm)).hom y) =
        (c.ι.app n).hom y at hnat'
      have h' : (c.ι.app m).hom ((F.map (homOfLE hnm)).hom y) =
          (c.ι.app m).hom x := hnat'.trans hxy
      have hx : (F.map (homOfLE hnm)).hom y = x := hinj m h'
      exact ⟨y, hy, hx⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      have hnat := c.w (homOfLE hnm)
      have hnat' := congrArg (fun q : F.obj n ⟶ c.pt => q.hom y) hnat
      change (c.ι.app m).hom ((F.map (homOfLE hnm)).hom y) =
        (c.ι.app n).hom y at hnat'
      exact hnat'.symm
  intro n
  have hClosedMap : IsClosedMap (c.ι.app n).hom := by
    intro S hS
    apply (TopCat.isClosed_iff_of_isColimit c hc
      ((c.ι.app n).hom '' S)).2
    intro m
    by_cases hmn : m ≤ n
    · rw [hleft hmn S]
      exact hS.preimage (F.map (homOfLE hmn)).hom.continuous
    · have hnm : n ≤ m := by omega
      rw [hright hnm S]
      exact (hmap (homOfLE hnm)).isClosedMap _ hS
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap
    (c.ι.app n).hom.continuous (hinj n) hClosedMap

/-- Closed embeddings into an arbitrary linearly ordered colimit stage induce closed
embeddings into the colimit. -/
theorem transfinite_colimit_stage_closedEmbedding
    {J : Type u} [LinearOrder J] {F : J ⥤ TopCat.{u}} {c : Cocone F}
    (hc : IsColimit c)
    (hmap : ∀ {j k : J} (f : j ⟶ k), IsClosedEmbedding (F.map f).hom)
    (hinj : ∀ j, Function.Injective (c.ι.app j).hom) :
    ∀ j, IsClosedEmbedding (c.ι.app j).hom := by
  classical
  have hleft {j k : J} (hjk : k ≤ j) (S : Set (F.obj j)) :
      (c.ι.app k).hom ⁻¹' ((c.ι.app j).hom '' S) =
        (F.map (homOfLE hjk)).hom ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hnat := c.w (homOfLE hjk)
      have hnat' := congrArg
        (fun q : F.obj k ⟶ c.pt => q.hom x) hnat
      change (c.ι.app j).hom ((F.map (homOfLE hjk)).hom x) =
        (c.ι.app k).hom x at hnat'
      have h' : (c.ι.app j).hom y =
          (c.ι.app j).hom ((F.map (homOfLE hjk)).hom x) :=
        hxy.trans hnat'.symm
      have hy' : y = (F.map (homOfLE hjk)).hom x := hinj j h'
      change (F.map (homOfLE hjk)).hom x ∈ S
      rw [← hy']
      exact hy
    · intro hx
      refine ⟨(F.map (homOfLE hjk)).hom x, hx, ?_⟩
      have hnat := c.w (homOfLE hjk)
      have hnat' := congrArg
        (fun q : F.obj k ⟶ c.pt => q.hom x) hnat
      change (c.ι.app j).hom ((F.map (homOfLE hjk)).hom x) =
        (c.ι.app k).hom x at hnat'
      exact hnat'
  have hright {j k : J} (hjk : j ≤ k) (S : Set (F.obj j)) :
      (c.ι.app k).hom ⁻¹' ((c.ι.app j).hom '' S) =
        (F.map (homOfLE hjk)).hom '' S := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hnat := c.w (homOfLE hjk)
      have hnat' := congrArg
        (fun q : F.obj j ⟶ c.pt => q.hom y) hnat
      change (c.ι.app k).hom ((F.map (homOfLE hjk)).hom y) =
        (c.ι.app j).hom y at hnat'
      have h' : (c.ι.app k).hom ((F.map (homOfLE hjk)).hom y) =
          (c.ι.app k).hom x := hnat'.trans hxy
      have hx : (F.map (homOfLE hjk)).hom y = x := hinj k h'
      exact ⟨y, hy, hx⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      have hnat := c.w (homOfLE hjk)
      have hnat' := congrArg
        (fun q : F.obj j ⟶ c.pt => q.hom y) hnat
      change (c.ι.app k).hom ((F.map (homOfLE hjk)).hom y) =
        (c.ι.app j).hom y at hnat'
      exact hnat'.symm
  intro j
  have hClosedMap : IsClosedMap (c.ι.app j).hom := by
    intro S hS
    apply (TopCat.isClosed_iff_of_isColimit c hc
      ((c.ι.app j).hom '' S)).2
    intro k
    by_cases hjk : k ≤ j
    · rw [hleft hjk S]
      exact hS.preimage (F.map (homOfLE hjk)).hom.continuous
    · have hkj : j ≤ k := le_of_not_ge hjk
      rw [hright hkj S]
      exact (hmap (homOfLE hkj)).isClosedMap _ hS
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap
    (c.ι.app j).hom.continuous (hinj j) hClosedMap

/-- A subset that is closed and discrete on every stage of an injective colimit remains closed
and discrete in the colimit. -/
theorem transfinite_colimit_closedDiscrete_of_stagewise
    {J : Type u} [LinearOrder J] {F : J ⥤ TopCat.{u}} {c : Cocone F}
    (hc : IsColimit c)
    (hinj : ∀ j, Function.Injective (c.ι.app j).hom)
    (Q : Set c.pt)
    (hstage : ∀ j,
      IsClosed ((c.ι.app j).hom ⁻¹' Q) ∧ IsDiscrete ((c.ι.app j).hom ⁻¹' Q)) :
    IsClosed Q ∧ IsDiscrete Q := by
  constructor
  · apply (TopCat.isClosed_iff_of_isColimit c hc Q).2
    intro j
    exact (hstage j).1
  · rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro x hx
    have hremoved : IsClosed (Q \ {x}) := by
      apply (TopCat.isClosed_iff_of_isColimit c hc (Q \ {x})).2
      intro j
      let e := (c.ι.app j).hom
      have hpreQ := (hstage j).1
      by_cases hhit : ∃ y : F.obj j, e y = x
      · obtain ⟨y, hy⟩ := hhit
        have hpre : e ⁻¹' (Q \ {x}) = e ⁻¹' Q \ {y} := by
          ext z
          simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨hzQ, hzx⟩
            refine ⟨hzQ, ?_⟩
            intro hzy
            apply hzx
            simpa [hzy] using hy
          · rintro ⟨hzQ, hzy⟩
            refine ⟨hzQ, ?_⟩
            intro hzx
            apply hzy
            exact hinj j (hzx.trans hy.symm)
        rw [hpre]
        exact isClosed_of_subset_discrete_closed (by
          intro z hz
          exact hz.1) (hstage j).2 hpreQ
      · have hpre : e ⁻¹' (Q \ {x}) = e ⁻¹' Q := by
          ext z
          simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_singleton_iff]
          constructor
          · exact fun hz => hz.1
          · intro hzQ
            refine ⟨hzQ, ?_⟩
            intro hzx
            exact hhit ⟨z, hzx⟩
        rw [hpre]
        exact hpreQ
    refine ⟨(Q \ {x})ᶜ, hremoved.isOpen_compl, ?_⟩
    ext z
    change ((z ∉ (Q \ {x})) ∧ (z ∈ Q)) ↔ z = x
    constructor
    · rintro ⟨hnot, hzQ⟩
      by_contra hne
      exact hnot ⟨hzQ, hne⟩
    · intro hzx
      subst z
      exact ⟨by simp, hx⟩

/-- A colimit of T₁ stages has T₁ colimit space when its cocone maps are injective. -/
theorem transfinite_colimit_t1Space_of_stagewise
    {J : Type u} [LinearOrder J] {F : J ⥤ TopCat.{u}} {c : Cocone F}
    (hc : IsColimit c)
    (hinj : ∀ j, Function.Injective (c.ι.app j).hom)
    (hT1 : ∀ j, T1Space (F.obj j)) : T1Space c.pt := by
  refine ⟨fun x => ?_⟩
  apply (TopCat.isClosed_iff_of_isColimit c hc ({x} : Set c.pt)).2
  intro j
  letI : T1Space (F.obj j) := hT1 j
  apply Set.Subsingleton.isClosed
  intro y hy z hz
  have hy' : (c.ι.app j).hom y = x := by simpa using hy
  have hz' : (c.ι.app j).hom z = x := by simpa using hz
  exact hinj j (hy'.trans hz'.symm)

end HomotopyHypothesis.Approximation.FiniteSubcomplex
