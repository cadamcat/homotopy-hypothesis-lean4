import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Category.TopCat.Limits.Products
universe u

open CategoryTheory Limits TopCat Topology Set

namespace HomotopyHypothesis.Approximation.FiniteSubcomplex

/-- Closedness in a topological pushout can be checked on its two legs. -/
theorem pushout_isClosed_iff_preimages
    {A B C P : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (sq : IsPushout f g i j) (S : Set P) :
    IsClosed S ↔ IsClosed (i.hom ⁻¹' S) ∧ IsClosed (j.hom ⁻¹' S) := by
  constructor
  · intro hS
    exact ⟨hS.preimage i.hom.continuous, hS.preimage j.hom.continuous⟩
  · rintro ⟨hB, hC⟩
    classical
    let c : PushoutCocone f g := PushoutCocone.mk i j sq.w
    have hc : IsColimit c := sq.isColimit
    apply (TopCat.isClosed_iff_of_isColimit c hc S).2
    intro k
    cases k with
    | some o =>
      cases o with
      | left => exact hB
      | right => exact hC
    | none =>
      have hzero : c.ι.app WalkingSpan.zero = g ≫ j := by
        change f ≫ i = g ≫ j
        exact sq.w
      rw [hzero]
      change IsClosed ((j.hom ∘ g.hom) ⁻¹' S)
      rw [Set.preimage_comp]
      exact hC.preimage g.hom.continuous

/-- A subset of a pushout is discrete if every point can be removed with closed preimages
along both legs. -/
theorem pushout_isDiscrete_of_closed_singleton_complements
    {A B C P : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (sq : IsPushout f g i j) (S : Set P)
    (h : ∀ x ∈ S, IsClosed (i.hom ⁻¹' (S \ {x})) ∧
      IsClosed (j.hom ⁻¹' (S \ {x}))) : IsDiscrete S := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hclosed : IsClosed (S \ ({x} : Set P)) :=
    (pushout_isClosed_iff_preimages sq (S \ {x})).2 (h x hx)
  refine ⟨(S \ {x})ᶜ, hclosed.isOpen_compl, ?_⟩
  ext y
  by_cases hxy : y = x
  · subst y
    simp [hx]
  · simp [hxy]

/-- Equality of two points from the same leg of a topological pushout. -/
theorem topCat_pushout_inl_eq_inl_iff
    {A B C P : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (sq : IsPushout f g i j)
    (hf : Function.Injective f.hom) (b b' : B) :
    i.hom b = i.hom b' ↔
      b = b' ∨ ∃ a a', g.hom a = g.hom a' ∧
        f.hom a = b ∧ f.hom a' = b' := by
  classical
  let cT : PushoutCocone ((forget TopCat).map f) ((forget TopCat).map g) :=
    PushoutCocone.mk ((forget TopCat).map i) ((forget TopCat).map j) (by
      exact congrArg ((forget TopCat).map) sq.w)
  have hcT : IsColimit cT := by
    simpa [cT] using
      (isColimitPushoutCoconeMapOfIsColimit (forget TopCat) sq.w sq.isColimit)
  let fT := (forget TopCat).map f
  let gT := (forget TopCat).map g
  let c₀ := CategoryTheory.Limits.Types.Pushout.cocone fT gT
  have hc₀ := CategoryTheory.Limits.Types.Pushout.isColimitCocone fT gT
  let e := IsColimit.coconePointUniqueUpToIso hcT hc₀
  have hE (x : B) : e.hom (cT.inl x) = c₀.inl x := by
    exact ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom hcT hc₀ WalkingSpan.left) x
  have hcanon : c₀.inl b = c₀.inl b' ↔
      b = b' ∨ ∃ a a', gT a = gT a' ∧ fT a = b ∧ fT a' = b' := by
    change (CategoryTheory.Limits.Types.Pushout.inl fT gT b =
      CategoryTheory.Limits.Types.Pushout.inl fT gT b') ↔ _
    letI : Mono fT := (mono_iff_injective fT).2 hf
    change (Quot.mk _ (Sum.inl b) = Quot.mk _ (Sum.inl b')) ↔ _
    rw [CategoryTheory.Limits.Types.Pushout.quot_mk_eq_iff]
    rw [CategoryTheory.Limits.Types.Pushout.inl_rel'_inl_iff]
    constructor
    · rintro (hbb | ⟨a, a', haa', hfa, hfa'⟩)
      · exact Or.inl hbb
      · exact Or.inr ⟨a, a', haa', hfa.symm, hfa'.symm⟩
    · rintro (hbb | ⟨a, a', haa', hfa, hfa'⟩)
      · exact Or.inl hbb
      · exact Or.inr ⟨a, a', haa', hfa.symm, hfa'.symm⟩
  constructor
  · intro h
    have h' : c₀.inl b = c₀.inl b' := by
      calc
        c₀.inl b = e.hom (cT.inl b) := (hE b).symm
        _ = e.hom (cT.inl b') := congrArg e.hom h
        _ = c₀.inl b' := hE b'
    simpa [fT, gT] using hcanon.mp h'
  · intro h
    have h' := hcanon.mpr (by simpa [fT, gT] using h)
    have heq : e.hom (cT.inl b) = e.hom (cT.inl b') := by
      rw [hE b, hE b']
      exact h'
    calc
      cT.inl b = e.inv (e.hom (cT.inl b)) := by simp [e]
      _ = e.inv (e.hom (cT.inl b')) := congrArg e.inv heq
      _ = cT.inl b' := by simp [e]

/-- Equality of points from opposite legs of a topological pushout. -/
theorem topCat_pushout_inl_eq_inr_iff
    {A B C P : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (sq : IsPushout f g i j)
    (hf : Function.Injective f.hom) (b : B) (c : C) :
    i.hom b = j.hom c ↔ ∃ a, f.hom a = b ∧ g.hom a = c := by
  let cT : PushoutCocone ((forget TopCat).map f) ((forget TopCat).map g) :=
    PushoutCocone.mk ((forget TopCat).map i) ((forget TopCat).map j) (by
      exact congrArg ((forget TopCat).map) sq.w)
  have hcT : IsColimit cT := by
    simpa [cT] using
      (isColimitPushoutCoconeMapOfIsColimit (forget TopCat) sq.w sq.isColimit)
  exact CategoryTheory.Limits.Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
    hcT hf b c

/-- Closed discrete subsets in the cell summand stay closed and discrete in a pushout when they
avoid the attaching locus. -/
theorem pushout_image_closedDiscrete
    {A B C P : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (sq : IsPushout f g i j)
    (Q : Set B) (hQ : IsClosed Q) (hQdisc : IsDiscrete Q)
    (hiQ : Set.InjOn i.hom Q)
    (hpreB : i.hom ⁻¹' (i.hom '' Q) = Q)
    (hpreC : j.hom ⁻¹' (i.hom '' Q) = ∅) :
    IsClosed (i.hom '' Q) ∧ IsDiscrete (i.hom '' Q) := by
  have hclosed : IsClosed (i.hom '' Q) :=
    (pushout_isClosed_iff_preimages sq (i.hom '' Q)).2 (by
      rw [hpreB, hpreC]
      exact ⟨hQ, isClosed_empty⟩)
  refine ⟨hclosed, ?_⟩
  apply pushout_isDiscrete_of_closed_singleton_complements sq
  intro x hx
  obtain ⟨b, hb, rfl⟩ := hx
  have hBremove : i.hom ⁻¹' (i.hom '' Q \ {i.hom b}) = Q \ {b} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_diff, Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨b', hb', hEq⟩, hneq⟩
      have hyQ : y ∈ Q := by
        have hy : y ∈ i.hom ⁻¹' (i.hom '' Q) := by
          change i.hom y ∈ i.hom '' Q
          exact ⟨b', hb', hEq⟩
        rw [hpreB] at hy
        exact hy
      refine ⟨hyQ, ?_⟩
      intro hyb
      apply hneq
      exact congrArg i.hom hyb
    · rintro ⟨hyQ, hyb⟩
      constructor
      · exact ⟨y, hyQ, rfl⟩
      · intro hEq
        apply hyb
        exact hiQ hyQ hb hEq
  have hCremove : IsClosed (j.hom ⁻¹' (i.hom '' Q \ {i.hom b})) := by
    rw [Set.preimage_diff, hpreC]
    simp
  have hQremove : IsClosed (Q \ {b}) :=
    isClosed_of_subset_discrete_closed (by
      intro y hy
      exact hy.1) hQdisc hQ
  exact ⟨hBremove ▸ hQremove, hCremove⟩

/-- A compact image in a pushout contains only finitely many selected points from a closed
discrete subset disjoint from the attaching locus. -/
theorem compact_map_finite_pushout_image
    {A B C P K : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (sq : IsPushout f g i j)
    (Q : Set B) [CompactSpace K] (h : K ⟶ P)
    (hQ : IsClosed Q) (hQdisc : IsDiscrete Q)
    (hiQ : Set.InjOn i.hom Q)
    (hpreB : i.hom ⁻¹' (i.hom '' Q) = Q)
    (hpreC : j.hom ⁻¹' (i.hom '' Q) = ∅)
    (hsub : i.hom '' Q ⊆ Set.range h.hom) :
    (i.hom '' Q).Finite := by
  obtain ⟨hclosed, hdisc⟩ :=
    pushout_image_closedDiscrete sq Q hQ hQdisc hiQ hpreB hpreC
  have hcompact : IsCompact (i.hom '' Q) :=
    (isCompact_range h.hom.continuous).of_isClosed_subset hclosed hsub
  exact hcompact.finite hdisc

/-- Selecting at most one point in each summand of a topological coproduct gives a closed
discrete subset when the summands are T1. -/
theorem sigma_range_isClosedDiscrete {I H : Type u} (A : I → TopCat.{u})
    (p : H → Σ i, (A i : Type u))
    (hp : Function.Injective (fun h => (p h).1)) (hA : ∀ i, T1Space (A i)) :
    IsClosed (Set.range p) ∧ IsDiscrete (Set.range p) := by
  constructor
  · rw [isClosed_sigma_iff]
    intro i
    let F : Set (A i) :=
      (fun y : A i => (⟨i, y⟩ : Σ j, (A j : Type u))) ⁻¹' Set.range p
    change IsClosed F
    have hFsub : ∀ x ∈ F, ∀ y ∈ F, x = y := by
      intro x hx y hy
      rcases hx with ⟨h₁, hh₁⟩
      rcases hy with ⟨h₂, hh₂⟩
      have hidx : (p h₁).1 = (p h₂).1 := by
        calc
          (p h₁).1 = i := by simpa using congrArg Sigma.fst hh₁
          _ = (p h₂).1 := by simpa using (congrArg Sigma.fst hh₂).symm
      have hh : h₁ = h₂ := hp hidx
      subst h₂
      have hxy : (⟨i, x⟩ : Σ k, (A k : Type u)) = ⟨i, y⟩ := by
        simpa using hh₁.symm.trans hh₂
      cases hxy
      rfl
    by_cases hne : F.Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hFeq : F = {x} := by
        ext y
        constructor
        · intro hy
          simp only [Set.mem_singleton_iff]
          exact hFsub y hy x hx
        · intro hy
          have hy' : y = x := Set.mem_singleton_iff.mp hy
          subst y
          exact hx
      rw [hFeq]
      letI : T1Space (A i) := hA i
      exact isClosed_singleton
    · have hFeq : F = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hne ⟨x, hx⟩)
      rw [hFeq]
      exact isClosed_empty
  · rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro x hx
    obtain ⟨h, rfl⟩ := hx
    let U : Set (Σ i, (A i : Type u)) := {z | z.1 = (p h).1}
    have hU : IsOpen U := by
      rw [isOpen_sigma_iff]
      intro i
      by_cases hi : i = (p h).1
      · subst i
        simpa [U] using (isOpen_univ : IsOpen (Set.univ : Set (A (p h).1)))
      · have hpre :
            (fun y : A i => (⟨i, y⟩ : Σ j, (A j : Type u))) ⁻¹' U = ∅ := by
          ext y
          simp [U, hi]
        rw [hpre]
        exact isOpen_empty
    refine ⟨U, hU, ?_⟩
    have hEq : U ∩ Set.range p = {p h} := by
      ext z
      constructor
      · rintro ⟨hzU, hz⟩
        obtain ⟨h', rfl⟩ := hz
        have hidx : (p h').1 = (p h).1 := hzU
        have hh' : h' = h := hp hidx
        subst h'
        rfl
      · intro hz
        have hz' : z = p h := by simpa using hz
        subst z
        exact ⟨rfl, ⟨h, rfl⟩⟩
    exact hEq

/-- A compact map into a pushout meets only finitely many coproduct summands away from the
attaching locus. -/
theorem compact_map_meets_finitely_many_pushoutSummands
    {I H : Type u} (D : I → TopCat.{u})
    {A C P K : TopCat.{u}}
    {f : A ⟶ TopCat.of (Σ i, (D i : Type u))} {g : A ⟶ C}
    {i : TopCat.of (Σ i, (D i : Type u)) ⟶ P} {j : C ⟶ P}
    (sq : IsPushout f g i j)
    (hf : Function.Injective f.hom)
    (p : H → Σ i, (D i : Type u))
    (hp : Function.Injective (fun h => (p h).1))
    (hD : ∀ k, T1Space (D k))
    (hAway : ∀ h, p h ∉ Set.range f.hom)
    (h : K ⟶ P) [CompactSpace K]
    (hHit : ∀ x, i.hom (p x) ∈ Set.range h.hom) :
    Finite H := by
  classical
  let Q : Set (TopCat.of (Σ k, (D k : Type u))) := Set.range p
  have hQ := sigma_range_isClosedDiscrete D p hp hD
  have hSame := topCat_pushout_inl_eq_inl_iff sq hf
  have hCross := topCat_pushout_inl_eq_inr_iff sq hf
  have hpreB : i.hom ⁻¹' (i.hom '' Q) = Q := by
    ext b
    constructor
    · rintro ⟨b', ⟨x, rfl⟩, heq⟩
      rcases (hSame b (p x)).mp heq.symm with hb | ⟨a, a', _, hfa, hfa'⟩
      · exact ⟨x, hb.symm⟩
      ·
        exact False.elim ((hAway x) ⟨a', hfa'⟩)
    · intro hb
      exact ⟨b, hb, rfl⟩
  have hpreC : j.hom ⁻¹' (i.hom '' Q) = ∅ := by
    ext c
    constructor
    · rintro ⟨b, ⟨x, rfl⟩, heq⟩
      obtain ⟨a, hfa, _⟩ := (hCross _ c).mp heq
      exact (hAway x) ⟨a, hfa⟩
    · intro hc
      exact hc.elim
  have hiQ : Set.InjOn i.hom Q := by
    intro b hb b' hb' heq
    rcases hb with ⟨x, rfl⟩
    rcases hb' with ⟨y, rfl⟩
    rcases (hSame (p x) (p y)).mp heq with hxy | ⟨a, a', _, hfa, _⟩
    · exact congrArg p (hp (congrArg Sigma.fst hxy))
    · exact False.elim ((hAway x) ⟨a, hfa⟩)
  have hsub : i.hom '' Q ⊆ Set.range h.hom := by
    rintro z ⟨b, hb, rfl⟩
    obtain ⟨x, rfl⟩ := hb
    exact hHit x
  have hfinite := compact_map_finite_pushout_image
    sq Q h hQ.1 hQ.2 hiQ hpreB hpreC hsub
  have hrange : (Set.range (fun x => i.hom (p x))).Finite := by
    have heq : Set.range (fun x => i.hom (p x)) = i.hom '' Q := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨p x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨b, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    rw [heq]
    exact hfinite
  have himageFinite :
      ((fun x => i.hom (p x)) '' (Set.univ : Set H)).Finite := by
    have heq : (fun x => i.hom (p x)) '' (Set.univ : Set H) =
        Set.range (fun x => i.hom (p x)) := by
      ext z
      simp
    rw [heq]
    exact hrange
  have hfiniteUniv : (Set.univ : Set H).Finite :=
    himageFinite.of_finite_image (fun x _ y _ heq => hp (congrArg Sigma.fst (hiQ
      ⟨x, rfl⟩ ⟨y, rfl⟩ heq)))
  exact Set.finite_univ_iff.mp hfiniteUniv

/-- Cobase change preserves closed embeddings in the category of topological spaces. -/
theorem pushout_isClosedEmbedding
    {A B C P : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (sq : IsPushout f g i j)
    (hf : IsClosedEmbedding f.hom) : IsClosedEmbedding j.hom := by
  classical
  let c : PushoutCocone f g := PushoutCocone.mk i j sq.w
  have hc : IsColimit c := sq.isColimit
  let cT : PushoutCocone ((forget TopCat).map f) ((forget TopCat).map g) :=
    PushoutCocone.mk ((forget TopCat).map i) ((forget TopCat).map j) (by
      exact congrArg ((forget TopCat).map) sq.w)
  have hcT : IsColimit cT := by
    simpa [cT] using
      (isColimitPushoutCoconeMapOfIsColimit (forget TopCat) sq.w sq.isColimit)
  have hcross (b : B) (x : C) : i.hom b = j.hom x ↔
      ∃ a : A, f.hom a = b ∧ g.hom a = x :=
    CategoryTheory.Limits.Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      hcT hf.injective b x
  have hj : Function.Injective j.hom :=
    CategoryTheory.Limits.Types.pushoutCocone_inr_injective_of_isColimit hcT hf.injective
  have hClosedMap : IsClosedMap j.hom := by
    intro S hS
    have hpreB :
        (c.ι.app WalkingSpan.left).hom ⁻¹'
          ((c.ι.app WalkingSpan.right).hom '' S) = f.hom '' (g.hom ⁻¹' S) := by
      ext b
      constructor
      · rintro ⟨x, hx, hEq⟩
        obtain ⟨a, hfa, hga⟩ := (hcross b x).mp hEq.symm
        have ha : g.hom a ∈ S := by rw [hga]; exact hx
        exact ⟨a, ha, hfa⟩
      · rintro ⟨a, ha, rfl⟩
        refine ⟨g.hom a, ha, ?_⟩
        have hsq := congrArg (fun q => q.hom a) sq.w
        exact hsq.symm
    change IsClosed ((c.ι.app WalkingSpan.right).hom '' S)
    apply (TopCat.isClosed_iff_of_isColimit c hc _).2
    intro k
    cases k with
    | some o =>
      cases o with
      | left =>
        change IsClosed ((c.ι.app WalkingSpan.left).hom ⁻¹'
          ((c.ι.app WalkingSpan.right).hom '' S))
        rw [hpreB]
        exact hf.isClosedMap _ (hS.preimage g.hom.continuous)
      | right =>
        change IsClosed (j.hom ⁻¹' (j.hom '' S))
        rw [Set.preimage_image_eq _ hj]
        exact hS
    | none =>
        have hzero : c.ι.app WalkingSpan.zero = g ≫ j := by
          change f ≫ i = g ≫ j
          exact sq.w
        rw [hzero]
        change IsClosed ((j.hom ∘ g.hom) ⁻¹' (j.hom '' S))
        rw [Set.preimage_comp, Set.preimage_image_eq _ hj]
        exact hS.preimage g.hom.continuous
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap j.hom.continuous hj hClosedMap

/-- A pushout of T1 spaces along a closed embedding is T1. -/
theorem pushout_t1Space
    {A B C P : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (sq : IsPushout f g i j)
    [T1Space B] [T1Space C] (hf : IsClosedEmbedding f.hom) : T1Space P := by
  classical
  let c : PushoutCocone f g := PushoutCocone.mk i j sq.w
  have hc : IsColimit c := sq.isColimit
  let cT : PushoutCocone ((forget TopCat).map f) ((forget TopCat).map g) :=
    PushoutCocone.mk ((forget TopCat).map i) ((forget TopCat).map j) (by
      exact congrArg ((forget TopCat).map) sq.w)
  have hcT : IsColimit cT := by
    simpa [cT] using
      (isColimitPushoutCoconeMapOfIsColimit (forget TopCat) sq.w sq.isColimit)
  let fT := (forget TopCat).map f
  let gT := (forget TopCat).map g
  have hcross (b : B) (x : C) : i.hom b = j.hom x ↔
      ∃ a : A, f.hom a = b ∧ g.hom a = x :=
    CategoryTheory.Limits.Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      hcT hf.injective b x
  have hSame (b b' : B) : i.hom b = i.hom b' ↔
      b = b' ∨ ∃ a a', g.hom a = g.hom a' ∧ f.hom a = b ∧ f.hom a' = b' := by
    let c₀ := CategoryTheory.Limits.Types.Pushout.cocone fT gT
    have hc₀ := CategoryTheory.Limits.Types.Pushout.isColimitCocone fT gT
    let e := IsColimit.coconePointUniqueUpToIso hcT hc₀
    have hE (x : B) : e.hom (cT.inl x) = c₀.inl x := by
      exact ConcreteCategory.congr_hom
        (IsColimit.comp_coconePointUniqueUpToIso_hom hcT hc₀ WalkingSpan.left) x
    have hcanon : c₀.inl b = c₀.inl b' ↔
        b = b' ∨ ∃ a a', gT a = gT a' ∧ fT a = b ∧ fT a' = b' := by
      change (CategoryTheory.Limits.Types.Pushout.inl fT gT b =
        CategoryTheory.Limits.Types.Pushout.inl fT gT b') ↔ _
      letI : Mono fT := (mono_iff_injective fT).2 hf.injective
      change (Quot.mk _ (Sum.inl b) = Quot.mk _ (Sum.inl b')) ↔ _
      rw [CategoryTheory.Limits.Types.Pushout.quot_mk_eq_iff]
      rw [CategoryTheory.Limits.Types.Pushout.inl_rel'_inl_iff]
      constructor
      · rintro (hbb | ⟨a, a', haa', hfa, hfa'⟩)
        · exact Or.inl hbb
        · exact Or.inr ⟨a, a', haa', hfa.symm, hfa'.symm⟩
      · rintro (hbb | ⟨a, a', haa', hfa, hfa'⟩)
        · exact Or.inl hbb
        · exact Or.inr ⟨a, a', haa', hfa.symm, hfa'.symm⟩
    constructor
    · intro h
      have h' : c₀.inl b = c₀.inl b' := by
        calc
          c₀.inl b = e.hom (cT.inl b) := (hE b).symm
          _ = e.hom (cT.inl b') := congrArg e.hom h
          _ = c₀.inl b' := hE b'
      simpa [fT, gT] using hcanon.mp h'
    · intro h
      have h' := hcanon.mpr (by simpa [fT, gT] using h)
      have heq : e.hom (cT.inl b) = e.hom (cT.inl b') := by
        rw [hE b, hE b']
        exact h'
      calc
        cT.inl b = e.inv (e.hom (cT.inl b)) := by simp [e]
        _ = e.inv (e.hom (cT.inl b')) := congrArg e.inv heq
        _ = cT.inl b' := by simp [e]
  have hj : Function.Injective j.hom :=
    CategoryTheory.Limits.Types.pushoutCocone_inr_injective_of_isColimit hcT hf.injective
  letI : T1Space A := hf.toIsEmbedding.t1Space
  have hleftFiber (b : B) : IsClosed (i.hom ⁻¹' ({i.hom b} : Set P)) := by
    by_cases hb : b ∈ Set.range f.hom
    · obtain ⟨a₀, ha₀⟩ := hb
      have hEq : i.hom ⁻¹' ({i.hom b} : Set P) =
          f.hom '' (g.hom ⁻¹' ({g.hom a₀} : Set C)) := by
        ext b'
        constructor
        · intro h
          have h' : i.hom b' = i.hom b := by simpa using h
          rcases (hSame b' b).mp h' with hbb | ⟨a, a', haa', hfa, hfa'⟩
          · subst b'
            exact ⟨a₀, by simp, ha₀⟩
          · have ha' : a' = a₀ := hf.injective (hfa'.trans ha₀.symm)
            subst a'
            exact ⟨a, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using haa', hfa⟩
        · rintro ⟨a, ha, hfa⟩
          have hga : g.hom a = g.hom a₀ := by simpa using ha
          have hsqA := congrArg (fun q => q.hom a) sq.w
          have hsqA₀ := congrArg (fun q => q.hom a₀) sq.w
          have h' : i.hom (f.hom a) = i.hom b := by
            calc
              i.hom (f.hom a) = j.hom (g.hom a) := hsqA
              _ = j.hom (g.hom a₀) := congrArg j.hom hga
              _ = i.hom (f.hom a₀) := hsqA₀.symm
              _ = i.hom b := congrArg i.hom ha₀
          simpa [Set.mem_preimage, Set.mem_singleton_iff, hfa] using h'
      rw [hEq]
      exact hf.isClosedMap _ (isClosed_singleton.preimage g.hom.continuous)
    · have hEq : i.hom ⁻¹' ({i.hom b} : Set P) = {b} := by
        ext b'
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro h
          rcases (hSame b' b).mp h with hbb | ⟨a, a', _, _, hfa'⟩
          · exact hbb
          · exact (hb ⟨a', hfa'⟩).elim
        · rintro rfl
          rfl
      rw [hEq]
      exact isClosed_singleton
  have hrightFiber (x : C) : IsClosed (j.hom ⁻¹' ({j.hom x} : Set P)) := by
    have hEq : j.hom ⁻¹' ({j.hom x} : Set P) = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        exact hj h
      · rintro rfl
        rfl
    rw [hEq]
    exact isClosed_singleton
  have hleftOfRight (x : C) : IsClosed (i.hom ⁻¹' ({j.hom x} : Set P)) := by
    have hEq : i.hom ⁻¹' ({j.hom x} : Set P) = f.hom '' (g.hom ⁻¹' ({x} : Set C)) := by
      ext b
      constructor
      · intro h
        have h' : i.hom b = j.hom x := by simpa using h
        rcases (hcross b x).mp h' with ⟨a, hfa, rfl⟩
        exact ⟨a, by simp, hfa⟩
      · rintro ⟨a, ha, hfa⟩
        have hga : g.hom a = x := by simpa using ha
        have hsqA := congrArg (fun q => q.hom a) sq.w
        have hsqA' : i.hom (f.hom a) = j.hom (g.hom a) := by simpa using hsqA
        have h' : i.hom (f.hom a) = j.hom x := by rw [← hga]; exact hsqA'
        simpa [Set.mem_preimage, Set.mem_singleton_iff, hfa] using h'
    rw [hEq]
    exact hf.isClosedMap _ (isClosed_singleton.preimage g.hom.continuous)
  have hrightOfLeft (b : B) : IsClosed (j.hom ⁻¹' ({i.hom b} : Set P)) := by
    have hEq : j.hom ⁻¹' ({i.hom b} : Set P) = g.hom '' (f.hom ⁻¹' ({b} : Set B)) := by
      ext x
      constructor
      · intro h
        have h' : i.hom b = j.hom x := by simpa using h.symm
        rcases (hcross b x).mp h' with ⟨a, hfa, hga⟩
        exact ⟨a, hfa, hga⟩
      · rintro ⟨a, ha, hga⟩
        have hfa : f.hom a = b := by simpa using ha
        have hsqA := congrArg (fun q => q.hom a) sq.w
        have hsqA' : i.hom (f.hom a) = j.hom (g.hom a) := by simpa using hsqA
        have h' : j.hom x = i.hom b := by
          calc
            j.hom x = j.hom (g.hom a) := congrArg j.hom hga.symm
            _ = i.hom (f.hom a) := hsqA'.symm
            _ = i.hom b := congrArg i.hom hfa
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using h'
    rw [hEq]
    have hfiber : (f.hom ⁻¹' ({b} : Set B)).Finite :=
      (Set.finite_singleton b).preimage_embedding ⟨f.hom, hf.injective⟩
    exact (hfiber.image g.hom).isClosed
  have hleftSingleton (b : B) : IsClosed ({i.hom b} : Set P) := by
    apply (TopCat.isClosed_iff_of_isColimit c hc ({i.hom b} : Set P)).2
    intro k
    cases k with
    | none =>
        change IsClosed ((f ≫ i).hom ⁻¹' ({i.hom b} : Set P))
        change IsClosed (f.hom ⁻¹' (i.hom ⁻¹' ({i.hom b} : Set P)))
        exact (hleftFiber b).preimage f.hom.continuous
    | some o =>
        cases o with
        | left => exact hleftFiber b
        | right => exact hrightOfLeft b
  have hrightSingleton (x : C) : IsClosed ({j.hom x} : Set P) := by
    apply (TopCat.isClosed_iff_of_isColimit c hc ({j.hom x} : Set P)).2
    intro k
    cases k with
    | none =>
        change IsClosed ((f ≫ i).hom ⁻¹' ({j.hom x} : Set P))
        rw [sq.w]
        change IsClosed (g.hom ⁻¹' (j.hom ⁻¹' ({j.hom x} : Set P)))
        exact (hrightFiber x).preimage g.hom.continuous
    | some o =>
        cases o with
        | left => exact hleftOfRight x
        | right => exact hrightFiber x
  refine ⟨fun p => ?_⟩
  obtain ⟨k, z, hz⟩ := Types.jointly_surjective_of_isColimit hcT p
  cases k with
  | none =>
      have hp : i.hom (f.hom z) = p := by
        change i.hom (f.hom z) = p at hz
        exact hz
      simpa [hp] using hleftSingleton (f.hom z)
  | some o =>
      cases o with
      | left =>
          have hp : i.hom z = p := by change i.hom z = p at hz; exact hz
          simpa [hp] using hleftSingleton z
      | right =>
          have hp : j.hom z = p := by change j.hom z = p at hz; exact hz
          simpa [hp] using hrightSingleton z

/-- A coproduct of closed embeddings is a closed embedding. -/
theorem sigma_map_isClosedEmbedding {I : Type u} {A B : I → Type u}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
    (f : ∀ i, A i → B i) (hf : ∀ i, IsClosedEmbedding (f i)) :
    IsClosedEmbedding (Sigma.map (fun i : I => i) f) := by
  classical
  have hEmb : IsEmbedding (Sigma.map (fun i : I => i) f) := by
    rw [Topology.isEmbedding_sigmaMap (fun _ _ h => h)]
    exact fun i => (hf i).toIsEmbedding
  have hClosedMap : IsClosedMap (Sigma.map (fun i : I => i) f) := by
    intro S hS
    apply (isClosed_sigma_iff).2
    intro i
    have hSi : IsClosed (Sigma.mk i ⁻¹' S) := (isClosed_sigma_iff.mp hS i)
    have heq : Sigma.mk i ⁻¹' (Sigma.map (fun i : I => i) f '' S) =
        f i '' (Sigma.mk i ⁻¹' S) := by
      ext y
      constructor
      · rintro ⟨⟨j, x⟩, hx, hEq⟩
        simp only [Sigma.map] at hEq
        cases hEq
        exact ⟨x, by simpa using hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨i, x⟩, hx, rfl⟩
    rw [heq]
    exact (hf i).isClosedMap _ hSi
  exact IsClosedEmbedding.of_isEmbedding_isClosedMap hEmb hClosedMap

/-- The induced map between topological coproducts is a closed embedding when each component is. -/
theorem topCat_sigma_map_isClosedEmbedding {I : Type u} {A B : I → TopCat.{u}}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, IsClosedEmbedding (f i).hom) :
    IsClosedEmbedding (Limits.Sigma.map f).hom := by
  classical
  let eA := TopCat.sigmaIsoSigma A
  let eB := TopCat.sigmaIsoSigma B
  let raw : TopCat.of (Σ i, A i) ⟶ TopCat.of (Σ i, B i) := ofHom ⟨
    Sigma.map (fun i : I => i) (fun i x => (f i).hom x),
    (continuous_sigma_map.2 (fun i => (f i).hom.continuous))⟩
  have hraw : IsClosedEmbedding raw.hom := sigma_map_isClosedEmbedding
    (fun i x => (f i).hom x) hf
  have hcomm : eA.hom ≫ raw = Limits.Sigma.map f ≫ eB.hom := by
    apply Limits.Sigma.hom_ext
    intro i
    have hEA : Sigma.ι A i ≫ eA.hom = TopCat.sigmaι A i := by
      simpa [eA] using TopCat.sigmaIsoSigma_hom_ι A i
    have hEB : Sigma.ι B i ≫ eB.hom = TopCat.sigmaι B i := by
      simpa [eB] using TopCat.sigmaIsoSigma_hom_ι B i
    calc
      _ = TopCat.sigmaι A i ≫ raw := by rw [← Category.assoc, hEA]
      _ = f i ≫ TopCat.sigmaι B i := by
        apply TopCat.hom_ext
        ext x
        · rfl
        · exact HEq.rfl
      _ = f i ≫ Sigma.ι B i ≫ eB.hom := by
        rw [← hEB]
      _ = (Sigma.ι A i ≫ Limits.Sigma.map f) ≫ eB.hom := by
        change (f i ≫ Sigma.ι B i) ≫ eB.hom =
          (Sigma.ι A i ≫ Limits.Sigma.map f) ≫ eB.hom
        apply (cancel_mono eB.hom).2
        change f i ≫ Sigma.ι B i = Sigma.ι A i ≫ Sigma.map' id f
        rw [Sigma.ι_comp_map']
        simp
  have hfactor : Limits.Sigma.map f = eA.hom ≫ raw ≫ eB.inv := by
    apply (cancel_mono eB.hom).1
    calc
      _ = eA.hom ≫ raw := hcomm.symm
      _ = (eA.hom ≫ raw ≫ eB.inv) ≫ eB.hom := by simp [Category.assoc]
  rw [hfactor]
  have hA : IsClosedEmbedding eA.hom.hom := (TopCat.homeoOfIso eA).isClosedEmbedding
  have hB : IsClosedEmbedding eB.inv.hom := (TopCat.homeoOfIso eB).symm.isClosedEmbedding
  exact hB.comp (hraw.comp hA)

/-- A dependent sum of T1 spaces is T1. -/
theorem sigma_t1Space {I : Type u} {A : I → Type u} [∀ i, TopologicalSpace (A i)]
    (hA : ∀ i, T1Space (A i)) : T1Space (Σ i, A i) := by
  refine ⟨fun x => ?_⟩
  rw [isClosed_sigma_iff]
  intro i
  by_cases hi : i = x.1
  · subst i
    have hpre : Sigma.mk x.1 ⁻¹' ({x} : Set (Σ i, A i)) = {x.2} := by
      ext y
      cases x with
      | mk i₀ x₀ =>
        change (Sigma.mk i₀ y = Sigma.mk i₀ x₀) ↔ y = x₀
        simp
    rw [hpre]
    exact (hA x.1).t1 x.2
  · have hpre : Sigma.mk i ⁻¹' ({x} : Set (Σ i, A i)) = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false]
      constructor
      · intro hEq
        exact (hi (congrArg Sigma.fst hEq)).elim
      · intro hFalse
        exact False.elim hFalse
    rw [hpre]
    exact isClosed_empty

/-- A coproduct of T1 topological spaces is T1. -/
theorem topCat_sigma_t1Space {I : Type u} (A : I → TopCat.{u})
    (hA : ∀ i, T1Space (A i)) : T1Space (TopCat.of (Σ i, (A i : Type u))) :=
  sigma_t1Space (fun i => hA i)

end HomotopyHypothesis.Approximation.FiniteSubcomplex
