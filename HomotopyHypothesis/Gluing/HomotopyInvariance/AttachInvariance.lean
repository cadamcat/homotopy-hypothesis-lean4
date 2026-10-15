import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.HomotopyEquivalenceOfIsPushout
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeFiniteCellComplexHomotopyExtension
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Gluing.RelativeHomotopy.GlueHomotopy
import HomotopyHypothesis.Realization.SemisimplicialComparison.TopFacts
/-!
# Homotopy invariance of attaching maps

Pushouts of a relative finite cell complex along homotopic maps are homotopy equivalent
(Hatcher, Proposition 0.18).
-/

universe u

open CategoryTheory Limits TopCat

namespace HomotopyHypothesis.Gluing.HomotopyInvariance

open HomotopyHypothesis.Henry

noncomputable section

private abbrev Cyl (A : TopCat.{u}) : TopCat.{u} := TopCat.of (A × unitInterval)

private def endpoint {A : TopCat.{u}} (t : unitInterval) : A ⟶ Cyl A :=
  TopCat.ofHom ⟨fun a => (a, t), by fun_prop⟩

private def cylProjection (A : TopCat.{u}) : Cyl A ⟶ A :=
  TopCat.ofHom ⟨Prod.fst, by fun_prop⟩

@[simp] private theorem endpoint_comp_projection {A : TopCat.{u}} (t : unitInterval) :
    endpoint t ≫ cylProjection A = 𝟙 A := by
  ext a
  rfl

private abbrev MapCyl {A B : TopCat.{u}} (i : A ⟶ B) (t : unitInterval) :=
  pushout i (endpoint t)

private def mapCylBottom {A B : TopCat.{u}} (i : A ⟶ B) (t : unitInterval) :
    B ⟶ MapCyl i t := pushout.inl i (endpoint t)

private def mapCylSide {A B : TopCat.{u}} (i : A ⟶ B) (t : unitInterval) :
    Cyl A ⟶ MapCyl i t := pushout.inr i (endpoint t)

private def mapCylRetraction {A B : TopCat.{u}} (i : A ⟶ B) (t : unitInterval) :
    MapCyl i t ⟶ B :=
  pushout.desc (𝟙 B) (cylProjection A ≫ i) (by
    calc
      i ≫ 𝟙 B = i := by simp
      _ = (endpoint t ≫ cylProjection A) ≫ i := by
        rw [endpoint_comp_projection]
        simp
      _ = endpoint t ≫ (cylProjection A ≫ i) := Category.assoc _ _ _)

private theorem mapCylBottom_retraction {A B : TopCat.{u}} (i : A ⟶ B)
    (t : unitInterval) :
    mapCylBottom i t ≫ mapCylRetraction i t = 𝟙 B := by
  dsimp [mapCylBottom, mapCylRetraction]
  rw [pushout.inl_desc]

private theorem mapCylSide_retraction {A B : TopCat.{u}} (i : A ⟶ B)
    (t : unitInterval) :
    mapCylSide i t ≫ mapCylRetraction i t = cylProjection A ≫ i := by
  dsimp [mapCylSide, mapCylRetraction]
  rw [pushout.inr_desc]

private theorem mapCyl_isPushout {A B : TopCat.{u}} (i : A ⟶ B) (t : unitInterval) :
    IsPushout i (endpoint t) (mapCylBottom i t) (mapCylSide i t) :=
  IsPushout.of_hasPushout i (endpoint t)

private theorem mapCylSide_relFinCell {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : Top.relativeFiniteCellComplexes i) (t : unitInterval) :
    Top.relativeFiniteCellComplexes (mapCylSide i t) := by
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (mapCyl_isPushout i t).flip hi

private def shrinkToZero : C(unitInterval × unitInterval, unitInterval) := {
  toFun := fun p => ⟨(p.1 : ℝ) * (1 - (p.2 : ℝ)), by
    constructor
    · exact mul_nonneg (unitInterval.nonneg p.1) (by linarith [unitInterval.le_one p.2])
    · have h₁ := unitInterval.le_one p.1
      have h₂ := unitInterval.le_one p.2
      have h₃ := unitInterval.nonneg p.2
      have hp := mul_nonneg (by linarith : 0 ≤ 1 - (p.1 : ℝ))
        (by linarith : 0 ≤ 1 - (p.2 : ℝ))
      nlinarith
  ⟩
  continuous_toFun := by fun_prop
}

private def growToOne : C(unitInterval × unitInterval, unitInterval) := {
  toFun := fun p => ⟨(p.1 : ℝ) + (p.2 : ℝ) * (1 - (p.1 : ℝ)), by
    constructor
    · have h₁ := unitInterval.nonneg p.1
      have h₂ := unitInterval.nonneg p.2
      have h₃ := unitInterval.le_one p.1
      have hp := mul_nonneg h₂ (by linarith [unitInterval.le_one p.1])
      nlinarith
    · have h₁ := unitInterval.le_one p.1
      have h₂ := unitInterval.le_one p.2
      have hp := mul_nonneg (by linarith : 0 ≤ 1 - (p.1 : ℝ))
        (by linarith : 0 ≤ 1 - (p.2 : ℝ))
      nlinarith
  ⟩
  continuous_toFun := by fun_prop
}

private theorem shrinkToZero_atStart (r : unitInterval) : shrinkToZero (r, 0) = r := by
  apply Subtype.ext
  simp [shrinkToZero]

private theorem shrinkToZero_atEnd (r : unitInterval) : shrinkToZero (r, 1) = 0 := by
  apply Subtype.ext
  simp [shrinkToZero]

private theorem shrinkToZero_fixed (s : unitInterval) : shrinkToZero (0, s) = 0 := by
  apply Subtype.ext
  simp [shrinkToZero]

private theorem growToOne_atStart (r : unitInterval) : growToOne (r, 0) = r := by
  apply Subtype.ext
  simp [growToOne]

private theorem growToOne_atEnd (r : unitInterval) : growToOne (r, 1) = 1 := by
  apply Subtype.ext
  simp [growToOne]

private theorem growToOne_fixed (s : unitInterval) : growToOne (1, s) = 1 := by
  apply Subtype.ext
  simp [growToOne]

private def contractCylToZero {A : TopCat.{u}} {M : TopCat.{u}}
    {c d : Cyl A ⟶ M} (hend : endpoint 0 ≫ c = endpoint 0 ≫ d)
    (hd : ∀ a r, d.hom (a, r) = d.hom (a, 0)) : c.hom.Homotopy d.hom := {
  toFun := fun x => c.hom (x.2.1, shrinkToZero (x.2.2, x.1))
  continuous_toFun := by fun_prop
  map_zero_left := by
    intro x
    change c.hom (x.1, shrinkToZero (x.2, 0)) = c.hom (x.1, x.2)
    rw [shrinkToZero_atStart]
  map_one_left := by
    intro x
    change c.hom (x.1, shrinkToZero (x.2, 1)) = d.hom (x.1, x.2)
    rw [shrinkToZero_atEnd]
    have he := congrArg (fun f : A ⟶ M => f.hom x.1) hend
    change c.hom (x.1, 0) = d.hom (x.1, 0) at he
    exact he.trans (hd x.1 x.2).symm
}

private def contractCylToOne {A : TopCat.{u}} {M : TopCat.{u}}
    {c d : Cyl A ⟶ M} (hend : endpoint 1 ≫ c = endpoint 1 ≫ d)
    (hd : ∀ a r, d.hom (a, r) = d.hom (a, 1)) : c.hom.Homotopy d.hom := {
  toFun := fun x => c.hom (x.2.1, growToOne (x.2.2, x.1))
  continuous_toFun := by fun_prop
  map_zero_left := by
    intro x
    change c.hom (x.1, growToOne (x.2, 0)) = c.hom (x.1, x.2)
    rw [growToOne_atStart]
  map_one_left := by
    intro x
    change c.hom (x.1, growToOne (x.2, 1)) = d.hom (x.1, x.2)
    rw [growToOne_atEnd]
    have he := congrArg (fun f : A ⟶ M => f.hom x.1) hend
    change c.hom (x.1, 1) = d.hom (x.1, 1) at he
    exact he.trans (hd x.1 x.2).symm
}

private theorem homotopyEquivalence_of_homotopic {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (hg : Top.homotopyEquivalences g) (hfg : Realization.SemisimplicialComparison.HT f g) :
    Top.homotopyEquivalences f := by
  obtain ⟨r, hgr, hrg⟩ := hg
  refine ⟨r, ?_, ?_⟩
  · exact (Realization.SemisimplicialComparison.HT.comp hfg (Realization.SemisimplicialComparison.HT.refl r)).trans hgr
  · exact (Realization.SemisimplicialComparison.HT.comp (Realization.SemisimplicialComparison.HT.refl r) hfg.symm).symm.trans hrg

private theorem mapCylRetraction_homotopyEquivalence_zero {A B : TopCat.{u}}
    (i : A ⟶ B) : Top.homotopyEquivalences (mapCylRetraction i 0) := by
  let b := mapCylBottom i 0
  let c := mapCylSide i 0
  let p := mapCylRetraction i 0
  let sq := mapCyl_isPushout i 0
  have hbp : b ≫ p = 𝟙 B := by
    simpa [b, p] using mapCylBottom_retraction i (0 : unitInterval)
  let d : Cyl A ⟶ MapCyl i 0 := cylProjection A ≫ i ≫ b
  have hend : endpoint 0 ≫ c = endpoint 0 ≫ d := by
    calc
      endpoint 0 ≫ c = i ≫ b := (sq.w).symm
      _ = endpoint 0 ≫ d := by
        simp only [d, ← Category.assoc, endpoint_comp_projection, Category.id_comp]
  have hd : ∀ a r, d.hom (a, r) = d.hom (a, 0) := by
    intro a r
    rfl
  have hrel : c.hom.HomotopicRel d.hom (Set.range (endpoint (0 : unitInterval)).hom) := by
    refine ⟨{ toHomotopy := contractCylToZero hend hd, prop' := ?_ }⟩
    intro s x hx
    rcases hx with ⟨a, rfl⟩
    change c.hom (a, shrinkToZero (0, s)) = c.hom (a, 0)
    rw [shrinkToZero_fixed]
  have hrel' : c.hom.HomotopicRel (c ≫ p ≫ b).hom
      (Set.range (endpoint (0 : unitInterval)).hom) := by
    have hcp : c ≫ p = cylProjection A ≫ i := by
      simpa [c, p] using mapCylSide_retraction i (0 : unitInterval)
    have hEq : c ≫ p ≫ b = d := by
      calc
        c ≫ p ≫ b = (c ≫ p) ≫ b := by simp [Category.assoc]
        _ = (cylProjection A ≫ i) ≫ b := by rw [hcp]
        _ = d := rfl
    simpa [hEq] using hrel
  have hrelM := HomotopyHypothesis.Gluing.RelativeHomotopy.homotopicRel_of_isPushout_proof
    sq.flip (f := 𝟙 (MapCyl i 0)) (g := p ≫ b) (by
      calc
        b ≫ 𝟙 (MapCyl i 0) = b := by simp
        _ = (b ≫ p) ≫ b := by rw [hbp]; simp
        _ = b ≫ (p ≫ b) := Category.assoc _ _ _) hrel'
  have hp : Realization.SemisimplicialComparison.HT (𝟙 (MapCyl i 0)) (p ≫ b) := by
    exact hrelM.homotopic
  refine ⟨b, hp.symm, ?_⟩
  rw [hbp]

private theorem mapCylRetraction_homotopyEquivalence_one {A B : TopCat.{u}}
    (i : A ⟶ B) : Top.homotopyEquivalences (mapCylRetraction i 1) := by
  let b := mapCylBottom i 1
  let c := mapCylSide i 1
  let p := mapCylRetraction i 1
  let sq := mapCyl_isPushout i 1
  have hbp : b ≫ p = 𝟙 B := by
    simpa [b, p] using mapCylBottom_retraction i (1 : unitInterval)
  let d : Cyl A ⟶ MapCyl i 1 := cylProjection A ≫ i ≫ b
  have hend : endpoint 1 ≫ c = endpoint 1 ≫ d := by
    calc
      endpoint 1 ≫ c = i ≫ b := (sq.w).symm
      _ = endpoint 1 ≫ d := by
        simp only [d, ← Category.assoc, endpoint_comp_projection, Category.id_comp]
  have hd : ∀ a r, d.hom (a, r) = d.hom (a, 1) := by
    intro a r
    rfl
  have hrel : c.hom.HomotopicRel d.hom (Set.range (endpoint (1 : unitInterval)).hom) := by
    refine ⟨{ toHomotopy := contractCylToOne hend hd, prop' := ?_ }⟩
    intro s x hx
    rcases hx with ⟨a, rfl⟩
    change c.hom (a, growToOne (1, s)) = c.hom (a, 1)
    rw [growToOne_fixed]
  have hrel' : c.hom.HomotopicRel (c ≫ p ≫ b).hom
      (Set.range (endpoint (1 : unitInterval)).hom) := by
    have hcp : c ≫ p = cylProjection A ≫ i := by
      simpa [c, p] using mapCylSide_retraction i (1 : unitInterval)
    have hEq : c ≫ p ≫ b = d := by
      calc
        c ≫ p ≫ b = (c ≫ p) ≫ b := by simp [Category.assoc]
        _ = (cylProjection A ≫ i) ≫ b := by rw [hcp]
        _ = d := rfl
    simpa [hEq] using hrel
  have hrelM := HomotopyHypothesis.Gluing.RelativeHomotopy.homotopicRel_of_isPushout_proof
    sq.flip (f := 𝟙 (MapCyl i 1)) (g := p ≫ b) (by
      calc
        b ≫ 𝟙 (MapCyl i 1) = b := by simp
        _ = (b ≫ p) ≫ b := by rw [hbp]; simp
        _ = b ≫ (p ≫ b) := Category.assoc _ _ _) hrel'
  have hp : Realization.SemisimplicialComparison.HT (𝟙 (MapCyl i 1)) (p ≫ b) := by
    exact hrelM.homotopic
  refine ⟨b, hp.symm, ?_⟩
  rw [hbp]

theorem exists_homotopyEquivalence_of_isPushout_homotopic_proof {A B Z P₀ P₁ : TopCat.{u}}
    {i : A ⟶ B} (hi : Top.relativeFiniteCellComplexes i) {g₀ g₁ : A ⟶ Z}
    (hg : g₀.hom.Homotopic g₁.hom) {k₀ : B ⟶ P₀} {j₀ : Z ⟶ P₀} {k₁ : B ⟶ P₁}
    {j₁ : Z ⟶ P₁} (h₀ : IsPushout i g₀ k₀ j₀) (h₁ : IsPushout i g₁ k₁ j₁) :
    ∃ φ : P₀ ⟶ P₁, Top.homotopyEquivalences φ := by
  obtain ⟨H⟩ := hg
  let Kmap : C(A × unitInterval, Z) := H.toContinuousMap.comp ContinuousMap.prodSwap
  let K : Cyl A ⟶ Z := TopCat.ofHom Kmap
  have hK₀ : endpoint 0 ≫ K = g₀ := by
    apply TopCat.hom_ext
    ext a
    change H (0, a) = g₀.hom a
    exact H.map_zero_left a
  have hK₁ : endpoint 1 ≫ K = g₁ := by
    apply TopCat.hom_ext
    ext a
    change H (1, a) = g₁.hom a
    exact H.map_one_left a
  let b₀ := mapCylBottom i 0
  let c₀ := mapCylSide i 0
  let p₀ := mapCylRetraction i 0
  let b₁ := mapCylBottom i 1
  let c₁ := mapCylSide i 1
  let p₁ := mapCylRetraction i 1
  let sq₀ := mapCyl_isPushout i 0
  let sq₁ := mapCyl_isPushout i 1
  have hcell₀ : Top.relativeFiniteCellComplexes c₀ := by
    simpa [c₀] using mapCylSide_relFinCell i hi (0 : unitInterval)
  have hcell₁ : Top.relativeFiniteCellComplexes c₁ := by
    simpa [c₁] using mapCylSide_relFinCell i hi (1 : unitInterval)
  have hp₀ : Top.homotopyEquivalences p₀ := by
    simpa [p₀] using mapCylRetraction_homotopyEquivalence_zero i
  have hp₁ : Top.homotopyEquivalences p₁ := by
    simpa [p₁] using mapCylRetraction_homotopyEquivalence_one i
  let Hbase : (b₁.hom.comp i.hom).Homotopy
      (c₁.hom.comp (endpoint (0 : unitInterval)).hom) := {
    toFun := fun x => c₁.hom (x.2, unitInterval.symm x.1)
    continuous_toFun := by fun_prop
    map_zero_left := by
      intro a
      have hs := congrArg (fun f : A ⟶ MapCyl i 1 => f.hom a) sq₁.w
      change b₁.hom (i.hom a) = c₁.hom (a, 1) at hs
      change c₁.hom (a, unitInterval.symm 0) = b₁.hom (i.hom a)
      simpa using hs.symm
    map_one_left := by
      intro a
      change c₁.hom (a, unitInterval.symm 1) = c₁.hom (a, 0)
      simp
  }
  let Hbase' : (b₁.hom.comp i.hom).Homotopy
      ((endpoint (0 : unitInterval) ≫ c₁).hom) :=
    Hbase.cast rfl (by simp)
  obtain ⟨umap, Hu, hHu⟩ := Henry.Packages.relativeFiniteCellComplex_homotopyExtension
    i hi b₁.hom (endpoint (0 : unitInterval) ≫ c₁).hom Hbase'
  let u : B ⟶ MapCyl i 1 := TopCat.ofHom umap
  have hiu : i ≫ u = endpoint 0 ≫ c₁ := by
    apply TopCat.hom_ext
    ext a
    change umap (i.hom a) = c₁.hom (a, 0)
    calc
      umap (i.hom a) = Hu (1, i.hom a) := (Hu.map_one_left _).symm
      _ = Hbase' (1, a) := hHu 1 a
      _ = c₁.hom (a, 0) := by
        change c₁.hom (a, unitInterval.symm 1) = c₁.hom (a, 0)
        simp
  have hb₁p₁ : b₁ ≫ p₁ = 𝟙 B := by
    simpa [b₁, p₁] using mapCylBottom_retraction i (1 : unitInterval)
  have htrack : ∀ s a, Hu (s, i.hom a) = Hbase' (s, a) := hHu
  have hrelU : (u ≫ p₁).hom.HomotopicRel (ContinuousMap.id B) (Set.range i.hom) := by
    have hrelStart : (b₁ ≫ p₁).hom.HomotopicRel (u ≫ p₁).hom
        (Set.range i.hom) := by
      have hSource : p₁.hom.comp b₁.hom = (b₁ ≫ p₁).hom := by
        simp [TopCat.hom_comp]
      have hTarget : p₁.hom.comp umap = (u ≫ p₁).hom := by
        simp [u, TopCat.hom_comp]
      let Hpost := (ContinuousMap.Homotopy.refl p₁.hom).comp Hu
      refine ⟨{ toHomotopy := Hpost.cast hSource hTarget, prop' := ?_ }⟩
      intro s x hx
      rcases hx with ⟨a, rfl⟩
      have hPc : p₁.hom (c₁.hom (a, unitInterval.symm s)) = i.hom a := by
        have h := congrArg (fun f : Cyl A ⟶ B => f.hom (a, unitInterval.symm s))
          (mapCylSide_retraction i (1 : unitInterval))
        simpa [c₁, p₁, TopCat.hom_comp, ContinuousMap.comp_apply, cylProjection] using h
      have hPb : p₁.hom (b₁.hom (i.hom a)) = i.hom a := by
        have h := congrArg (fun f : B ⟶ B => f.hom (i.hom a)) hb₁p₁
        simpa [TopCat.hom_comp] using h
      change p₁.hom (Hu (s, i.hom a)) = p₁.hom (b₁.hom (i.hom a))
      calc
        p₁.hom (Hu (s, i.hom a)) = p₁.hom (Hbase' (s, a)) :=
          congrArg p₁.hom (htrack s a)
        _ = p₁.hom (c₁.hom (a, unitInterval.symm s)) := by
          rfl
        _ = i.hom a := hPc
        _ = p₁.hom (b₁.hom (i.hom a)) := hPb.symm
    obtain ⟨R⟩ := hrelStart.symm
    have hright : (b₁ ≫ p₁).hom = ContinuousMap.id B := by
      have h := congrArg Hom.hom hb₁p₁
      simpa [TopCat.hom_comp] using h
    exact ⟨R.cast rfl hright⟩
  let v : MapCyl i 0 ⟶ MapCyl i 1 := sq₀.desc u c₁ hiu
  have hvB : b₀ ≫ v = u := by simpa [b₀, v, sq₀] using sq₀.inl_desc u c₁ hiu
  have hvC : c₀ ≫ v = c₁ := by simpa [c₀, v, sq₀] using sq₀.inr_desc u c₁ hiu
  have hb₀p₀ : b₀ ≫ p₀ = 𝟙 B := by
    simpa [b₀, p₀] using mapCylBottom_retraction i (0 : unitInterval)
  have hbaseRel : (b₀ ≫ (v ≫ p₁)).hom.HomotopicRel (b₀ ≫ p₀).hom
      (Set.range i.hom) := by
    obtain ⟨R⟩ := hrelU
    have hleft : (u ≫ p₁).hom = (b₀ ≫ (v ≫ p₁)).hom := by
      have h := congrArg Hom.hom (by
        calc
          b₀ ≫ (v ≫ p₁) = (b₀ ≫ v) ≫ p₁ := by rw [Category.assoc]
          _ = u ≫ p₁ := by rw [hvB])
      exact h.symm
    have hright : ContinuousMap.id B = (b₀ ≫ p₀).hom := by
      have h := congrArg Hom.hom hb₀p₀
      simpa [TopCat.hom_comp] using h.symm
    exact ⟨R.cast hleft hright⟩
  have hsideEq : c₀ ≫ (v ≫ p₁) = c₀ ≫ p₀ := by
    calc
      c₀ ≫ (v ≫ p₁) = c₁ ≫ p₁ := by rw [← Category.assoc, hvC]
      _ = cylProjection A ≫ i := by
        simpa [c₁, p₁] using mapCylSide_retraction i (1 : unitInterval)
      _ = c₀ ≫ p₀ := by
        simpa [c₀, p₀] using (mapCylSide_retraction i (0 : unitInterval)).symm
  have hrelV := HomotopyHypothesis.Gluing.RelativeHomotopy.homotopicRel_of_isPushout_proof
    sq₀ hsideEq hbaseRel
  have hvp : Realization.SemisimplicialComparison.HT (v ≫ p₁) p₀ := by
    change (v ≫ p₁).hom.Homotopic p₀.hom
    exact hrelV.homotopic
  have hv : Top.homotopyEquivalences v :=
    Realization.SemisimplicialComparison.hoeq_of_comp_right hp₁
      (homotopyEquivalence_of_homotopic hp₀ hvp)
  let q₀ := pushout c₀ K
  let q₁ := pushout c₁ K
  let l₀ : MapCyl i 0 ⟶ q₀ := pushout.inl c₀ K
  let r₀ : Z ⟶ q₀ := pushout.inr c₀ K
  let l₁ : MapCyl i 1 ⟶ q₁ := pushout.inl c₁ K
  let r₁ : Z ⟶ q₁ := pushout.inr c₁ K
  let qs₀ : IsPushout c₀ K l₀ r₀ := IsPushout.of_hasPushout c₀ K
  let qs₁ : IsPushout c₁ K l₁ r₁ := IsPushout.of_hasPushout c₁ K
  have houter₀ : IsPushout i g₀ (b₀ ≫ l₀) r₀ := by
    have h := (sq₀.flip.paste_horiz qs₀.flip).flip
    simpa [hK₀] using h
  have houter₁ : IsPushout i g₁ (b₁ ≫ l₁) r₁ := by
    have h := (sq₁.flip.paste_horiz qs₁.flip).flip
    simpa [hK₁] using h
  let iso₀ : P₀ ≅ q₀ := h₀.isoIsPushout _ _ houter₀
  let iso₁ : P₁ ≅ q₁ := h₁.isoIsPushout _ _ houter₁
  have hcompatQ : c₀ ≫ v ≫ l₁ = K ≫ r₁ := by
    calc
      c₀ ≫ v ≫ l₁ = c₁ ≫ l₁ := by rw [← Category.assoc, hvC]
      _ = K ≫ r₁ := qs₁.w
  let ψ : q₀ ⟶ q₁ := pushout.desc (v ≫ l₁) r₁ hcompatQ
  have hψL : l₀ ≫ ψ = v ≫ l₁ := by
    change pushout.inl c₀ K ≫ pushout.desc (v ≫ l₁) r₁ hcompatQ = v ≫ l₁
    exact pushout.inl_desc _ _ _
  have hψR : r₀ ≫ ψ = r₁ := by
    change pushout.inr c₀ K ≫ pushout.desc (v ≫ l₁) r₁ hcompatQ = r₁
    exact pushout.inr_desc _ _ _
  have hψ : Top.homotopyEquivalences ψ :=
    Henry.Packages.homotopyEquivalence_of_isPushout
      c₀ K l₀ r₀ c₁ K l₁ r₁ (𝟙 (Cyl A)) v (𝟙 Z) ψ
      qs₀ qs₁ hcell₀ hcell₁
      (Realization.SemisimplicialComparison.hoeq_of_isIso (𝟙 (Cyl A))) hv
      (Realization.SemisimplicialComparison.hoeq_of_isIso (𝟙 Z))
      hvC (by simp) hψL hψR
  have hφ := Realization.SemisimplicialComparison.hoeq_comp
    (Realization.SemisimplicialComparison.hoeq_comp (Realization.SemisimplicialComparison.hoeq_of_isIso iso₀.hom) hψ)
    (Realization.SemisimplicialComparison.hoeq_of_isIso iso₁.inv)
  exact ⟨(iso₀.hom ≫ ψ) ≫ iso₁.inv, hφ⟩

#print axioms HomotopyHypothesis.Gluing.HomotopyInvariance.exists_homotopyEquivalence_of_isPushout_homotopic_proof

end

end HomotopyHypothesis.Gluing.HomotopyInvariance
