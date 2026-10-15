import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeFiniteCellComplexHomotopyExtension
import HomotopyHypothesis.Blueprint.Henry.Topology
universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Homotopy.RelativeLifting

private def curryHomotopy {B Y : TopCat.{u}} {f₀ f₁ : B ⟶ Y}
    (H : f₀.hom.Homotopy f₁.hom) : B ⟶ TopCat.of C(unitInterval, Y) :=
  TopCat.ofHom <| ContinuousMap.curry (H.toContinuousMap.comp ContinuousMap.prodSwap)

private def constantHomotopyFamily {A Y : TopCat.{u}} (f : A ⟶ Y) :
    A ⟶ TopCat.of C(unitInterval, Y) :=
  TopCat.ofHom <| ContinuousMap.curry (f.hom.comp ContinuousMap.fst)

private theorem homotopicRel_pushout
    {A B C P : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    (inl : B ⟶ P) (inr : C ⟶ P) (h : IsPushout f g inl inr)
    {Y : TopCat.{u}} (b₀ b₁ : B ⟶ Y) (c : C ⟶ Y)
    (hc₀ : f ≫ b₀ = g ≫ c) (hc₁ : f ≫ b₁ = g ≫ c)
    (H : b₀.hom.HomotopyRel b₁.hom (Set.range f.hom)) :
    (h.desc b₀ c hc₀).hom.HomotopicRel (h.desc b₁ c hc₁).hom (Set.range inr.hom) := by
  let HB : B ⟶ TopCat.of C(unitInterval, Y) := curryHomotopy H.toHomotopy
  let HC : C ⟶ TopCat.of C(unitInterval, Y) := constantHomotopyFamily c
  have hcomp : f ≫ HB = g ≫ HC := by
    apply TopCat.hom_ext
    ext a t
    change H (t, f.hom a) = c.hom (g.hom a)
    rw [H.eq_fst t ⟨a, rfl⟩]
    simpa using congrArg (fun m : A ⟶ Y => m a) hc₀
  let q : P ⟶ TopCat.of C(unitInterval, Y) := h.desc HB HC hcomp
  have ql : (inl ≫ q).hom = HB.hom := by
    change (inl ≫ h.desc HB HC hcomp).hom = HB.hom
    simpa using congrArg Hom.hom (h.inl_desc HB HC hcomp)
  have qr : (inr ≫ q).hom = HC.hom := by
    change (inr ≫ h.desc HB HC hcomp).hom = HC.hom
    simpa using congrArg Hom.hom (h.inr_desc HB HC hcomp)
  let F₀ : C(P, Y) := (h.desc b₀ c hc₀).hom
  let F₁ : C(P, Y) := (h.desc b₁ c hc₁).hom
  let k : C(unitInterval × P, Y) := q.hom.uncurry.comp ContinuousMap.prodSwap
  let z₀ : C(P, Y) := q.hom.uncurry.comp
    (ContinuousMap.prodMk (ContinuousMap.id P) (ContinuousMap.const P 0))
  let z₁ : C(P, Y) := q.hom.uncurry.comp
    (ContinuousMap.prodMk (ContinuousMap.id P) (ContinuousMap.const P 1))
  have hz₀' : TopCat.ofHom z₀ = h.desc b₀ c hc₀ := by
    apply h.hom_ext
    · apply TopCat.ext
      intro b
      change (inl ≫ TopCat.ofHom z₀) b = (inl ≫ h.desc b₀ c hc₀) b
      simp only [TopCat.comp_app, TopCat.ofHom_hom, h.inl_desc]
      calc
        z₀ (inl.hom b) = (q.hom (inl.hom b)) 0 := rfl
        _ = (HB.hom b) 0 := by
          have hq := ContinuousMap.congr_fun ql b
          simpa [TopCat.hom_comp] using congrArg (fun m : C(unitInterval, Y) => m 0) hq
        _ = b₀.hom b := by simp [HB, curryHomotopy, ContinuousMap.curry_apply]
    · apply TopCat.ext
      intro x
      change (inr ≫ TopCat.ofHom z₀) x = (inr ≫ h.desc b₀ c hc₀) x
      simp only [TopCat.comp_app, TopCat.ofHom_hom, h.inr_desc]
      calc
        z₀ (inr.hom x) = (q.hom (inr.hom x)) 0 := rfl
        _ = (HC.hom x) 0 := by
          have hq := ContinuousMap.congr_fun qr x
          simpa [TopCat.hom_comp] using congrArg (fun m : C(unitInterval, Y) => m 0) hq
        _ = c.hom x := by simp [HC, constantHomotopyFamily, ContinuousMap.curry_apply]
  have hz₀ : z₀ = F₀ := congrArg Hom.hom hz₀'
  have hz₁' : TopCat.ofHom z₁ = h.desc b₁ c hc₁ := by
    apply h.hom_ext
    · apply TopCat.ext
      intro b
      change (inl ≫ TopCat.ofHom z₁) b = (inl ≫ h.desc b₁ c hc₁) b
      simp only [TopCat.comp_app, TopCat.ofHom_hom, h.inl_desc]
      calc
        z₁ (inl.hom b) = (q.hom (inl.hom b)) 1 := rfl
        _ = (HB.hom b) 1 := by
          have hq := ContinuousMap.congr_fun ql b
          simpa [TopCat.hom_comp] using congrArg (fun m : C(unitInterval, Y) => m 1) hq
        _ = b₁.hom b := by simp [HB, curryHomotopy, ContinuousMap.curry_apply]
    · apply TopCat.ext
      intro x
      change (inr ≫ TopCat.ofHom z₁) x = (inr ≫ h.desc b₁ c hc₁) x
      simp only [TopCat.comp_app, TopCat.ofHom_hom, h.inr_desc]
      calc
        z₁ (inr.hom x) = (q.hom (inr.hom x)) 1 := rfl
        _ = (HC.hom x) 1 := by
          have hq := ContinuousMap.congr_fun qr x
          simpa [TopCat.hom_comp] using congrArg (fun m : C(unitInterval, Y) => m 1) hq
        _ = c.hom x := by simp [HC, constantHomotopyFamily, ContinuousMap.curry_apply]
  have hz₁ : z₁ = F₁ := congrArg Hom.hom hz₁'
  let K : ContinuousMap.Homotopy F₀ F₁ := {
    toFun := fun x => k x
    continuous_toFun := k.continuous
    map_zero_left := by
      intro x
      change z₀ x = F₀ x
      exact ContinuousMap.congr_fun hz₀ x
    map_one_left := by
      intro x
      change z₁ x = F₁ x
      exact ContinuousMap.congr_fun hz₁ x
  }
  have F₀r : F₀.comp inr.hom = c.hom := by
    change (h.desc b₀ c hc₀).hom.comp inr.hom = c.hom
    exact congrArg Hom.hom (h.inr_desc b₀ c hc₀)
  refine ⟨{ toHomotopy := K, prop' := ?_ }⟩
  intro t x hx
  rcases hx with ⟨x, rfl⟩
  change q.hom.uncurry (inr.hom x, t) = F₀ (inr.hom x)
  calc
    q.hom.uncurry (inr.hom x, t) = (q.hom (inr.hom x)) t := rfl
    _ = (HC.hom x) t := by
      have hq := ContinuousMap.congr_fun qr x
      simpa [TopCat.hom_comp] using congrArg (fun m : C(unitInterval, Y) => m t) hq
    _ = c.hom x := by simp [HC, constantHomotopyFamily, ContinuousMap.curry_apply]
    _ = F₀ (inr.hom x) := (ContinuousMap.congr_fun F₀r x).symm

private def hasRelativeLift {A B : TopCat.{u}} (i : A ⟶ B) : Prop :=
  ∀ {X Y : TopCat.{u}} (f : X ⟶ Y), HomotopyHypothesis.Henry.Top.weakEquivalences f →
    ∀ (a : A ⟶ X) (b : B ⟶ Y), a ≫ f = i ≫ b →
      ∃ l : B ⟶ X, i ≫ l = a ∧
        (l ≫ f).hom.HomotopicRel b.hom (Set.range i.hom)

private def relativeLiftProperty : MorphismProperty TopCat.{u} :=
  fun _ _ i => HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i ∧ hasRelativeLift i

private theorem homotopicRel_mono {X Y : TopCat.{u}} {f g : X ⟶ Y} {S T : Set X}
    (H : f.hom.HomotopicRel g.hom S) (hTS : T ⊆ S) :
    f.hom.HomotopicRel g.hom T := by
  rcases H with ⟨Hrel⟩
  refine ⟨{ toHomotopy := Hrel.toHomotopy, prop' := ?_ }⟩
  intro t x hx
  exact Hrel.prop' t x (hTS hx)

private theorem hasRelativeLift_comp
    {A B C : TopCat.{u}} {i : A ⟶ B} {j : B ⟶ C}
    (hi : hasRelativeLift i) (hj : hasRelativeLift j)
    (hjCell : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes j) :
    hasRelativeLift (i ≫ j) := by
  intro X Y f hf a c hsq
  obtain ⟨b, hia, H⟩ := hi f hf a (j ≫ c) (by simpa [Category.assoc] using hsq)
  rcases H with ⟨Hrel⟩
  obtain ⟨c', Hext, hboundary⟩ :=
    HomotopyHypothesis.Henry.Packages.relativeFiniteCellComplex_homotopyExtension
      j hjCell
      c.hom (b ≫ f).hom Hrel.symm.toHomotopy
  let cArrow : C ⟶ Y := TopCat.ofHom c'
  have hstrict : b ≫ f = j ≫ cArrow := by
    apply TopCat.ext
    intro x
    simpa [cArrow, TopCat.hom_comp] using (hboundary 1 x).symm
  obtain ⟨l, hjl, H₂⟩ := hj f hf b cArrow hstrict
  have H₁ : c.hom.HomotopicRel cArrow.hom (Set.range (i ≫ j).hom) := by
    refine ⟨{ toHomotopy := Hext, prop' := ?_ }⟩
    intro t x hx
    rcases hx with ⟨a', rfl⟩
    calc
      Hext (t, j.hom (i.hom a')) = Hrel.symm (t, i.hom a') := hboundary t (i.hom a')
      _ = (j ≫ c).hom (i.hom a') := Hrel.symm.eq_fst t ⟨a', rfl⟩
      _ = c.hom (j.hom (i.hom a')) := rfl
  have H₂' : (l ≫ f).hom.HomotopicRel cArrow.hom (Set.range (i ≫ j).hom) := by
    apply homotopicRel_mono H₂
    rintro _ ⟨a', rfl⟩
    exact ⟨i.hom a', rfl⟩
  refine ⟨l, ?_, H₂'.trans H₁.symm⟩
  calc
    (i ≫ j) ≫ l = i ≫ (j ≫ l) := by simp [Category.assoc]
    _ = i ≫ b := by rw [hjl]
    _ = a := hia

private theorem hasRelativeLift_pushout
    {A B A' P : TopCat.{u}} (i : A ⟶ B) (u : A ⟶ A')
    (v : B ⟶ P) (j : A' ⟶ P) (h : IsPushout i u v j)
    (hi : hasRelativeLift i) : hasRelativeLift j := by
  intro X Y f hf a b hsq
  have hcell : (u ≫ a) ≫ f = i ≫ (v ≫ b) := by
    calc
      (u ≫ a) ≫ f = u ≫ (a ≫ f) := by simp [Category.assoc]
      _ = u ≫ (j ≫ b) := by rw [hsq]
      _ = (u ≫ j) ≫ b := by simp [Category.assoc]
      _ = (i ≫ v) ≫ b := by rw [← h.w]
      _ = i ≫ (v ≫ b) := by simp [Category.assoc]
  obtain ⟨l, hia, H⟩ := hi f hf (u ≫ a) (v ≫ b) hcell
  have hc₀ : i ≫ (l ≫ f) = u ≫ (a ≫ f) := by
    calc
      i ≫ (l ≫ f) = (i ≫ l) ≫ f := by simp [Category.assoc]
      _ = (u ≫ a) ≫ f := by rw [hia]
      _ = u ≫ (a ≫ f) := by simp [Category.assoc]
  have hc₁ : i ≫ (v ≫ b) = u ≫ (a ≫ f) := by
    calc
      i ≫ (v ≫ b) = (i ≫ v) ≫ b := by simp [Category.assoc]
      _ = (u ≫ j) ≫ b := by rw [h.w]
      _ = u ≫ (j ≫ b) := by simp [Category.assoc]
      _ = u ≫ (a ≫ f) := by rw [← hsq]
  let d₀ : P ⟶ Y := h.desc (l ≫ f) (a ≫ f) hc₀
  let d₁ : P ⟶ Y := h.desc (v ≫ b) (a ≫ f) hc₁
  have d₀_eq : d₀ = (h.desc l a hia) ≫ f := by
    apply h.hom_ext <;> simp [d₀, Category.assoc]
  have d₁_eq : d₁ = b := by
    apply h.hom_ext <;> simp [d₁, Category.assoc, hsq]
  rcases H with ⟨Hrel⟩
  have Hpush := homotopicRel_pushout i u v j h (l ≫ f) (v ≫ b) (a ≫ f) hc₀ hc₁ Hrel
  refine ⟨h.desc l a hia, ?_, ?_⟩
  · simpa using h.inr_desc l a hia
  · simpa [d₀, d₁, d₀_eq, d₁_eq] using Hpush

private theorem hasRelativeLift_diskBoundary (n : ℕ) :
    hasRelativeLift (TopCat.diskBoundaryInclusion.{u} n) := by
  intro X Y f hf a b h
  exact hf n a b h

private theorem hasRelativeLift_iso {A B : TopCat.{u}} (i : A ⟶ B) [IsIso i] :
    hasRelativeLift i := by
  intro X Y f hf a b h
  let l : B ⟶ X := inv i ≫ a
  have hia : i ≫ l = a := by simp [l]
  have hcomp : i ≫ (l ≫ f) = i ≫ b := by
    simpa [l, Category.assoc] using h
  have hlf : l ≫ f = b := (cancel_epi i).mp hcomp
  refine ⟨l, hia, ?_⟩
  rw [hlf]
  exact ⟨ContinuousMap.HomotopyRel.refl b.hom (Set.range i.hom)⟩

private theorem relativeLiftProperty_isMultiplicative :
    @MorphismProperty.IsMultiplicative TopCat.{u} (inferInstance : Category TopCat.{u})
      relativeLiftProperty where
  id_mem (X : TopCat.{u}) := by
    refine ⟨?_, hasRelativeLift_iso (A := X) (B := X) (𝟙 X)⟩
    rw [HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes]
    exact MorphismProperty.le_multiplicativeClosure _ _
      (Or.inr (MorphismProperty.isomorphisms.infer_property (𝟙 X)))
  comp_mem {A B C : TopCat.{u}} (i : A ⟶ B) (j : B ⟶ C) hi hj := by
    rcases hi with ⟨hiCell, hiLift⟩
    rcases hj with ⟨hjCell, hjLift⟩
    refine ⟨?_, hasRelativeLift_comp hiLift hjLift hjCell⟩
    rw [HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes] at hiCell hjCell ⊢
    exact MorphismProperty.comp_mem _ i j hiCell hjCell

/-- A finite relative cell inclusion extends the compression lifting property from disk boundaries. -/
theorem relativeLift_of_weakEquivalence_proof {A B X Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    (f : X ⟶ Y) (hf : HomotopyHypothesis.Henry.Top.weakEquivalences f)
    (a : A ⟶ X) (b : B ⟶ Y) (h : a ≫ f = i ≫ b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧
      (l ≫ f).hom.HomotopicRel b.hom (Set.range i.hom) := by
  letI : relativeLiftProperty.IsMultiplicative := relativeLiftProperty_isMultiplicative
  have hCells : HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ≤ relativeLiftProperty := by
    intro A B q hq
    have hfinite : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes q := by
      rw [HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes]
      exact MorphismProperty.le_multiplicativeClosure _ q (Or.inl hq)
    refine ⟨hfinite, ?_⟩
    rcases hq with ⟨A₀, B₀, p, attach, cell, hp, hsq⟩
    change MorphismProperty.ofHoms
      (fun n : ℕ => TopCat.diskBoundaryInclusion.{u} n) p at hp
    rcases hp with ⟨n⟩
    exact hasRelativeLift_pushout (TopCat.diskBoundaryInclusion.{u} n)
      attach cell q hsq.flip (hasRelativeLift_diskBoundary n)
  have hIsos : MorphismProperty.isomorphisms TopCat.{u} ≤ relativeLiftProperty := by
    intro A B q hq
    have hfinite : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes q := by
      rw [HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes]
      exact MorphismProperty.le_multiplicativeClosure _ q (Or.inr hq)
    refine ⟨hfinite, ?_⟩
    haveI : IsIso q := (MorphismProperty.isomorphisms.iff q).mp hq
    intro X Y f hf a b h
    exact (hasRelativeLift_iso (A := A) (B := B) q) f hf a b h
  have hGen : (HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}) ≤ relativeLiftProperty := by
    intro A B q hq
    rcases hq with hq | hq
    · exact hCells q hq
    · exact hIsos q hq
  have hAll : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes ≤
      relativeLiftProperty := by
    rw [HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes]
    exact (MorphismProperty.multiplicativeClosure_le_iff
      (W := HomotopyHypothesis.Henry.Top.cellBoundaries.pushouts ⊔
        MorphismProperty.isomorphisms TopCat.{u}) relativeLiftProperty).2 hGen
  exact (hAll i hi).2 f hf a b h

#print axioms relativeLift_of_weakEquivalence_proof

end HomotopyHypothesis.Homotopy.RelativeLifting
