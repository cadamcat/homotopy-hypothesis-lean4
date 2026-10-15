import Mathlib.CategoryTheory.Limits.Presheaf
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismNaturality.Proofs.Part1
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Code
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdryIota
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Rank
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismHom
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapComp
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism
/-!
# Colimit presentations of derived boundaries

Proper-face representatives identify the derived boundary colimit with the side subcomplex.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismRelative

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological
open HomotopyHypothesis.Approximation.DerivedPrismNaturality

theorem pv_map_injective {k l : ℕ} {t : Fin (k + 1) → Fin (l + 1)}
    (ht : Function.Injective t) : Function.Injective (PV.map t) := by
  intro a b hab
  cases a with
  | top i =>
    cases b with
    | top j =>
      have hij : t i = t j := by simpa [PV.map] using hab
      congr 1
      exact ht hij
    | mid S => simp [PV.map] at hab
  | mid S =>
    cases b with
    | top j => simp [PV.map] at hab
    | mid S' =>
      have hSS' : S.image t = S'.image t := by simpa [PV.map] using hab
      have h := (Finset.image_injective ht) hSS'
      subst S'
      rfl

noncomputable def sdLanRepresentableIso :
    Henry.SemiSSet.stdSimplex.{u} ⋙ sdLan.{u} ≅ sdCos.{u} :=
  Presheaf.isExtensionAlongULiftYoneda sdCos.{u}

noncomputable def dprismLanRepresentableIso :
    Henry.SemiSSet.stdSimplex.{u} ⋙ dprismLan.{u} ≅ dprismCos.{u} :=
  Presheaf.isExtensionAlongULiftYoneda dprismCos.{u}

theorem sdLan_map_isPushout {A B C D : SemiSSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {h : B ⟶ D} {k : C ⟶ D} (sq : IsPushout f g h k) :
    IsPushout (sdLan.map f) (sdLan.map g) (sdLan.map h) (sdLan.map k) := by
  letI : PreservesColimit (span f g) sdLan :=
    (Presheaf.preservesColimitsOfSize_leftKanExtension sdCos.{u}).preservesColimitsOfShape.preservesColimit
  exact sq.map sdLan

theorem dprismLan_map_isPushout {A B C D : SemiSSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {h : B ⟶ D} {k : C ⟶ D} (sq : IsPushout f g h k) :
    IsPushout (dprismLan.map f) (dprismLan.map g) (dprismLan.map h) (dprismLan.map k) := by
  letI : PreservesColimit (span f g) dprismLan :=
    (Presheaf.preservesColimitsOfSize_leftKanExtension dprismCos.{u}).preservesColimitsOfShape.preservesColimit
  exact sq.map dprismLan

noncomputable def relDprismLanMap {W : SemiSSet.{u}} (A B : Subfunctor W) (h : A ≤ B) :
    pushout (sdLan.map (Subfunctor.homOfLe h)) (sdLanToDprism.app A.toFunctor) ⟶
      dprismLan.obj B.toFunctor :=
  pushout.desc (sdLanToDprism.app B.toFunctor)
    (dprismLan.map (Subfunctor.homOfLe h))
    (sdLanToDprism.naturality (Subfunctor.homOfLe h))

theorem relDprismLanMap_refl_anodyne {W : SemiSSet.{u}} (A : Subfunctor W) :
    anodyne (relDprismLanMap A A le_rfl) := by
  have hIso : IsIso (relDprismLanMap A A le_rfl) := by
    have hId : Subfunctor.homOfLe (le_rfl : A ≤ A) = 𝟙 A.toFunctor := by
      ext d x
      rfl
    have hf : sdLan.map (Subfunctor.homOfLe (le_rfl : A ≤ A)) = 𝟙 _ := by
      rw [hId]
      simp
    have hg : dprismLan.map (Subfunctor.homOfLe (le_rfl : A ≤ A)) = 𝟙 _ := by
      rw [hId]
      simp
    have hpush : IsIso (pushout.inr
        (sdLan.map (Subfunctor.homOfLe (le_rfl : A ≤ A)))
        (sdLanToDprism.app A.toFunctor)) := by
      rw [hf]
      infer_instance
    have h₁ : pushout.inr (sdLan.map (Subfunctor.homOfLe (le_rfl : A ≤ A)))
        (sdLanToDprism.app A.toFunctor) ≫
        relDprismLanMap A A le_rfl = 𝟙 _ := by
      dsimp [relDprismLanMap]
      rw [pushout.inr_desc, hg]
    have h₂ : relDprismLanMap A A le_rfl ≫
        pushout.inr (sdLan.map (Subfunctor.homOfLe (le_rfl : A ≤ A)))
          (sdLanToDprism.app A.toFunctor) = 𝟙 _ := by
      apply pushout.hom_ext
      · dsimp [relDprismLanMap]
        rw [← Category.assoc, pushout.inl_desc, ← pushout.condition, hf, Category.id_comp]
        simp
      · dsimp [relDprismLanMap]
        rw [← Category.assoc, pushout.inr_desc, hg, Category.id_comp]
        simp
    exact ⟨⟨pushout.inr (sdLan.map (Subfunctor.homOfLe (le_rfl : A ≤ A)))
      (sdLanToDprism.app A.toFunctor), h₂, h₁⟩⟩
  unfold anodyne
  exact .of _ (Or.inr (MorphismProperty.isomorphisms.infer_property _))

def pvBaseSupport {k : ℕ} (A : Finset (PV k)) : Finset (Fin (k + 1)) :=
  Finset.univ.filter fun i =>
    PV.top i ∈ A ∨ ∃ S, PV.mid S ∈ A ∧ i ∈ S

theorem pvBaseSupport_nonempty {k : ℕ} {A : Finset (PV k)}
    (hA : (dprismComplex k).S A) (hAne : A.Nonempty) : (pvBaseSupport A).Nonempty := by
  rcases hAne with ⟨a, ha⟩
  cases a with
  | top i =>
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ha⟩⟩
  | mid S =>
    rcases hA.1 S ha with ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨S, ha, hi⟩⟩⟩

theorem pvBaseSupport_proper_of_side {k : ℕ} {A : Finset (PV k)}
    (hSide : ∃ i, PV.top i ∉ A ∧ ∀ S, PV.mid S ∈ A → i ∉ S) :
    ∃ i, i ∉ pvBaseSupport A := by
  rcases hSide with ⟨i, hiTop, hiMid⟩
  refine ⟨i, ?_⟩
  intro hi
  rcases Finset.mem_filter.mp hi with ⟨-, hcase⟩
  rcases hcase with htop | ⟨S, hS, hmem⟩
  · exact hiTop htop
  · exact hiMid S hS hmem

theorem pvBaseSupport_map_subset_range {c : Henry.SemiSimplexCategory} {k n : ℕ}
    (θ : c ⟶ Henry.SemiSimplexCategory.mk k)
    (τ : (dprismComplex c.obj.len).Simplex n) :
    ∀ i ∈ pvBaseSupport
        (Finset.univ.image (fun j => PV.map θ.1.toOrderHom (τ.1 j))),
      i ∈ Set.range θ.1.toOrderHom := by
  intro i hi
  rcases (Finset.mem_filter.mp hi).2 with htop | ⟨S, hmid, hiS⟩
  · rcases Finset.mem_image.mp htop with ⟨j, -, hEq⟩
    cases hτ : τ.1 j with
    | top j₀ =>
      have hEq' : PV.top (θ.1.toOrderHom j₀) = PV.top i := by
        simpa [PV.map, hτ] using hEq
      exact ⟨j₀, PV.top.inj hEq'⟩
    | mid T => simp [PV.map, hτ] at hEq
  · rcases Finset.mem_image.mp hmid with ⟨j, -, hEq⟩
    cases hτ : τ.1 j with
    | top j₀ => simp [PV.map, hτ] at hEq
    | mid T =>
      have hEq' : PV.mid (T.image θ.1.toOrderHom) = PV.mid S := by
        simpa [PV.map, hτ] using hEq
      have hS : T.image θ.1.toOrderHom = S := PV.mid.inj hEq'
      rw [← hS] at hiS
      rcases Finset.mem_image.mp hiS with ⟨j₀, hj₀, rfl⟩
      exact ⟨j₀, rfl⟩

def dprismSideComplex (k : ℕ) : Complex (PV k) where
  S A := (dprismComplex k).S A ∧
    ∃ i, PV.top i ∉ A ∧ ∀ S, PV.mid S ∈ A → i ∉ S
  down _ _ hAB hA := by
    rcases hA.2 with ⟨i, hiTop, hiMid⟩
    exact ⟨(dprismComplex k).down hAB hA.1,
      ⟨i, fun ht => hiTop (hAB ht), fun S hS => hiMid S (hAB hS)⟩⟩

theorem dprismBdry_S_iff (k : ℕ) (A : Finset (PV k)) :
    (dprismBdryComplex k).S A ↔ (sdComplex k).S A ∨ (dprismSideComplex k).S A := by
  constructor
  · rintro ⟨hD, hB⟩
    rcases hB with hNoTop | hSide
    · exact Or.inl ⟨hD, hNoTop⟩
    · exact Or.inr ⟨hD, hSide⟩
  · rintro (⟨hD, hNoTop⟩ | ⟨hD, hSide⟩)
    · exact ⟨hD, Or.inl hNoTop⟩
    · exact ⟨hD, Or.inr hSide⟩

def dprismSideToBdryHom (k : ℕ) :
    (dprismSideComplex k).Hom (dprismBdryComplex k) where
  f := id
  strictMonoOn _ _ := strictMono_id.strictMonoOn _
  map_S _ hA := by
    rw [dprismBdry_S_iff]
    exact Or.inr (by simpa using hA)

def sdToDprismBdryHom (k : ℕ) :
    (sdComplex k).Hom (dprismBdryComplex k) where
  f := id
  strictMonoOn _ _ := strictMono_id.strictMonoOn _
  map_S _ hA := by
    rw [dprismBdry_S_iff]
    exact Or.inl (by simpa using hA)

def dprismSideToDprismHom (k : ℕ) :
    (dprismSideComplex k).Hom (dprismComplex k) where
  f := id
  strictMonoOn _ _ := strictMono_id.strictMonoOn _
  map_S _ hA := by simpa using hA.1

theorem dprismSideToDprism_mono (k : ℕ) :
    Mono (dprismSideToDprismHom k).toSemiSSet := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  apply (mono_iff_injective _).2
  intro x y hxy
  apply ULift.ext
  apply Subtype.ext
  have hfun := congrArg Subtype.val (congrArg ULift.down hxy)
  dsimp [dprismSideToDprismHom, Complex.Hom.toSemiSSet] at hfun
  exact hfun

noncomputable def dprismSideToDprism (k : ℕ) :
    (dprismSideComplex k).toSemiSSet ⟶
      dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk k) :=
  (dprismSideToDprismHom k).toSemiSSet

theorem dprismSideToDprism_mono' (k : ℕ) : Mono (dprismSideToDprism k) := by
  simpa [dprismSideToDprism, dprismCos, dprism] using dprismSideToDprism_mono k

def pvSupportedBy {m k : ℕ} (t : Fin (m + 1) ↪ Fin (k + 1)) : PV k → Prop
  | PV.top i => i ∈ Set.range t
  | PV.mid S => ∀ i ∈ S, i ∈ Set.range t

noncomputable def pvPullback {m k : ℕ} (r : Fin (k + 1) → Fin (m + 1))
    (t : Fin (m + 1) ↪ Fin (k + 1)) : PV k → PV m
  | PV.top i => PV.top (r i)
  | PV.mid S => PV.mid (S.preimage t t.injective.injOn)

theorem image_preimage_eq_of_range {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (s : Finset β) (hf : Function.Injective f)
    (hs : ∀ b ∈ s, b ∈ Set.range f) : (s.preimage f hf.injOn).image f = s := by
  ext b
  simp only [Finset.mem_image, Finset.mem_preimage]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hb
    obtain ⟨a, rfl⟩ := hs b hb
    exact ⟨a, hb, rfl⟩

theorem pvPullback_map {m k : ℕ} (r : Fin (k + 1) → Fin (m + 1))
    (t : Fin (m + 1) ↪ Fin (k + 1)) (hr : ∀ j, r (t j) = j)
    (v : PV k) (hv : pvSupportedBy t v) : PV.map t (pvPullback r t v) = v := by
  cases v with
  | top i =>
    obtain ⟨j, rfl⟩ := hv
    simp [PV.map, pvPullback, hr]
  | mid S =>
    change PV.mid ((S.preimage t t.injective.injOn).image t) = PV.mid S
    congr 1
    exact image_preimage_eq_of_range t S t.injective hv

theorem pvPullback_strictMonoOn {m k : ℕ} (r : Fin (k + 1) → Fin (m + 1))
    (t : Fin (m + 1) ↪ Fin (k + 1)) (ht : StrictMono t)
    (hr : ∀ j, r (t j) = j)
    (A : Finset (PV k)) (hA : (dprismComplex k).S A)
    (hsupport : ∀ a ∈ A, pvSupportedBy t a) :
    StrictMonoOn (pvPullback r t) A := by
  intro a ha b hb hab
  cases a with
  | top i =>
    cases b with
    | top j =>
      have hij : i < j := by
        change PV.rank (PV.top i) < PV.rank (PV.top j) at hab
        simpa [PV.rank, Prod.Lex.toLex_lt_toLex] using hab
      obtain ⟨i₀, hi₀⟩ := hsupport (PV.top i) ha
      obtain ⟨j₀, hj₀⟩ := hsupport (PV.top j) hb
      have hmap : t i₀ < t j₀ := by
        rw [hi₀, hj₀]
        exact hij
      have hsrc : i₀ < j₀ :=
        (OrderEmbedding.ofStrictMono t ht).lt_iff_lt.mp hmap
      have hsrc' : r i < r j := by
        rw [← hi₀, ← hj₀, hr i₀, hr j₀]
        exact hsrc
      change PV.rank (PV.top (r i)) < PV.rank (PV.top (r j))
      simpa [PV.rank, Prod.Lex.toLex_lt_toLex] using hsrc'
    | mid S =>
      change PV.rank (PV.top (r i)) <
        PV.rank (PV.mid (S.preimage t t.injective.injOn))
      simp [PV.rank, Prod.Lex.toLex_lt_toLex]
  | mid S =>
    cases b with
    | top j =>
      change PV.rank (PV.mid S) < PV.rank (PV.top j) at hab
      simp [PV.rank, Prod.Lex.toLex_lt_toLex] at hab
    | mid S' =>
      have hne : S ≠ S' := by
        intro h
        subst S'
        exact lt_irrefl _ hab
      have hcard : S.card < S'.card := by
        rcases hA.2.1 S S' ha hb with hSS' | hS'S
        · exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSS', hne⟩)
        · have hcard' : S'.card < S.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hS'S, hne.symm⟩)
          have hbad : (PV.mid S' : PV k) < PV.mid S := by
            change PV.rank _ < PV.rank _
            exact Prod.Lex.toLex_lt_toLex.2
              (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inl hcard')⟩)
          exact (lt_asymm hab hbad).elim
      have hS₀ := hsupport (PV.mid S) ha
      have hS₁ := hsupport (PV.mid S') hb
      have hpre₀ := image_preimage_eq_of_range t S t.injective hS₀
      have hpre₁ := image_preimage_eq_of_range t S' t.injective hS₁
      have hcard₀ : (S.preimage t t.injective.injOn).card = S.card := by
        have h := Finset.card_image_of_injective (S.preimage t t.injective.injOn) t.injective
        rw [hpre₀] at h
        exact h.symm
      have hcard₁ : (S'.preimage t t.injective.injOn).card = S'.card := by
        have h := Finset.card_image_of_injective (S'.preimage t t.injective.injOn) t.injective
        rw [hpre₁] at h
        exact h.symm
      have hcardPre : (S.preimage t t.injective.injOn).card <
          (S'.preimage t t.injective.injOn).card := by
        rw [hcard₀, hcard₁]
        exact hcard
      change PV.rank (PV.mid (S.preimage t t.injective.injOn)) <
        PV.rank (PV.mid (S'.preimage t t.injective.injOn))
      exact Prod.Lex.toLex_lt_toLex.2
        (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inl hcardPre)⟩)

theorem pvPullback_map_S {m k : ℕ} (r : Fin (k + 1) → Fin (m + 1))
    (t : Fin (m + 1) ↪ Fin (k + 1)) (hr : ∀ j, r (t j) = j)
    (A : Finset (PV k)) (hA : (dprismComplex k).S A)
    (hsupport : ∀ a ∈ A, pvSupportedBy t a) :
    (dprismComplex m).S (A.image (pvPullback r t)) := by
  have preMid (S : Finset (Fin (m + 1)))
      (hS : PV.mid S ∈ A.image (pvPullback r t)) :
      ∃ T, PV.mid T ∈ A ∧ S = T.preimage t t.injective.injOn := by
    rcases Finset.mem_image.mp hS with ⟨a, ha, hEq⟩
    cases a with
    | top j => simp [pvPullback] at hEq
    | mid T => exact ⟨T, ha, by simpa [pvPullback] using hEq.symm⟩
  have preTop (i : Fin (m + 1))
      (hi : PV.top i ∈ A.image (pvPullback r t)) :
      ∃ j, PV.top j ∈ A ∧ t i = j := by
    rcases Finset.mem_image.mp hi with ⟨a, ha, hEq⟩
    cases a with
    | top j =>
      obtain ⟨i', hi'⟩ := hsupport (PV.top j) ha
      have hri : r j = i' := by rw [← hi', hr]
      have hri' : r j = i := by simpa [pvPullback] using hEq
      have heq : i' = i := hri.symm.trans hri'
      have hti : t i = j := by rw [← heq]; exact hi'
      exact ⟨j, ha, hti⟩
    | mid S => simp [pvPullback] at hEq
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨T, hT, rfl⟩ := preMid S hS
    rcases hA.1 T hT with ⟨j, hj⟩
    obtain ⟨i, hi⟩ := hsupport (PV.mid T) hT j hj
    exact ⟨i, Finset.mem_preimage.mpr (by simpa [hi] using hj)⟩
  · intro S S' hS hS'
    obtain ⟨T, hT, hEq⟩ := preMid S hS
    obtain ⟨T', hT', hEq'⟩ := preMid S' hS'
    rw [hEq, hEq']
    rcases hA.2.1 T T' hT hT' with hTT' | hT'T
    · left
      intro i hi
      exact Finset.mem_preimage.mpr (hTT' (Finset.mem_preimage.mp hi))
    · right
      intro i hi
      exact Finset.mem_preimage.mpr (hT'T (Finset.mem_preimage.mp hi))
  · intro i S hi hS
    obtain ⟨T, hT, hEq⟩ := preMid S hS
    obtain ⟨j, hj, htij⟩ := preTop i hi
    have hjT := hA.2.2 j T hj hT
    rw [hEq]
    exact Finset.mem_preimage.mpr (by simpa [htij] using hjT)

theorem exists_pvPullback_simplex {m k n : ℕ} (r : Fin (k + 1) → Fin (m + 1))
    (t : Fin (m + 1) ↪ Fin (k + 1)) (ht : StrictMono t) (hr : ∀ j, r (t j) = j)
    (σ : (dprismComplex k).Simplex n)
    (hsupport : ∀ i, pvSupportedBy t (σ.1 i)) :
    ∃ τ : (dprismComplex m).Simplex n,
      ∀ i, PV.map t (τ.1 i) = σ.1 i := by
  let A : Finset (PV k) := Finset.univ.image σ.1
  have hA : (dprismComplex k).S A := σ.2.2
  have hsupportA : ∀ a ∈ A, pvSupportedBy t a := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨i, -, rfl⟩
    exact hsupport i
  let f : Fin (n + 1) → PV m := pvPullback r t ∘ σ.1
  have hf : StrictMono f := by
    intro i j hij
    apply pvPullback_strictMonoOn r t ht hr A hA hsupportA
    · simp [A]
    · simp [A]
    · exact σ.2.1 hij
  have hS : (dprismComplex m).S (Finset.univ.image f) := by
    simpa [A, f, Finset.image_image] using pvPullback_map_S r t hr A hA hsupportA
  refine ⟨⟨f, hf, hS⟩, ?_⟩
  intro i
  exact pvPullback_map r t hr (σ.1 i) (hsupport i)

theorem erase_nonempty {k : ℕ} (hk : 0 < k) (i : Fin (k + 1)) :
    (Finset.univ.erase i : Finset (Fin (k + 1))).Nonempty := by
  by_cases hi : i = 0
  · refine ⟨⟨1, by omega⟩, ?_⟩
    simp only [Finset.mem_erase, Finset.mem_univ]
    subst i
    constructor
    · intro h
      have hval := congrArg Fin.val h
      norm_num at hval
    · trivial
  · refine ⟨0, ?_⟩
    simp only [Finset.mem_erase, Finset.mem_univ]
    exact ⟨Ne.symm hi, trivial⟩

noncomputable abbrev dprismLanElementsDiagram (X : SemiSSet.{u}) :=
  (Functor.Elements.π X).leftOp ⋙ dprismCos.{u}

noncomputable def dprismLanElementsDiagramIso (X : SemiSSet.{u}) :
    Presheaf.functorToRepresentables.{u} X ⋙ dprismLan.{u} ≅
      dprismLanElementsDiagram X := by
  change (((Functor.Elements.π X).leftOp ⋙ uliftYoneda.{u}) ⋙ dprismLan.{u}) ≅ _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.Elements.π X).leftOp
      dprismLanRepresentableIso

noncomputable def dprismLanElementsCocone (X : SemiSSet.{u}) :
    Cocone (dprismLanElementsDiagram X) :=
  (Cocone.precompose (dprismLanElementsDiagramIso X).inv).obj
    (dprismLan.{u}.mapCocone (Presheaf.coconeOfRepresentable X))

noncomputable def dprismLanElementsCocone_isColimit (X : SemiSSet.{u}) :
    IsColimit (dprismLanElementsCocone X) := by
  letI : PreservesColimitsOfSize.{0, u} dprismLan.{u} :=
    Presheaf.preservesColimitsOfSize_leftKanExtension.{0, 0, u, 0, 0, u + 1, u}
      dprismCos.{u}
  exact (IsColimit.precomposeHomEquiv (dprismLanElementsDiagramIso X).symm
      (dprismLan.{u}.mapCocone (Presheaf.coconeOfRepresentable X))).symm
    (isColimitOfPreserves dprismLan.{u} (Presheaf.colimitOfRepresentable X))

noncomputable def dprismLanElementsColimitIso (X : SemiSSet.{u}) :
    dprismLan.{u}.obj X ≅ colimit (dprismLanElementsDiagram X) :=
  (dprismLanElementsCocone_isColimit X).coconePointUniqueUpToIso (colimit.isColimit _)

def boundaryElementFace {k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements) :
    e.obj.unop ⟶ Henry.SemiSimplexCategory.mk k := e.val.1.down

theorem boundaryElementFace_not_surjective {k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements) :
    ¬ Function.Surjective (boundaryElementFace e).1.toOrderHom := by
  intro hsurj
  rcases e.val.2 with ⟨i, hi⟩
  apply hi
  obtain ⟨j, hj⟩ := hsurj i
  exact ⟨j, by simpa [boundaryElementFace] using hj⟩

noncomputable def boundaryElementOfFace {m k : ℕ}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : ¬ Function.Surjective θ.1.toOrderHom) :
    (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements := by
  have hnot : ∃ i, i ∉ Set.range θ.1.toOrderHom := by
    by_contra h
    apply hθ
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  let i := Classical.choose hnot
  have hi : i ∉ Set.range θ.1.toOrderHom := Classical.choose_spec hnot
  have hmem : ULift.up θ ∈
      (Henry.SemiSSet.boundary.{u} k).obj (op (Henry.SemiSimplexCategory.mk m)) := by
    exact ⟨i, by simpa using hi⟩
  exact (Henry.SemiSSet.boundary.{u} k).toFunctor.elementsMk _ ⟨ULift.up θ, hmem⟩

theorem boundaryElementFace_precomp_not_surjective {m k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
    (ρ : Henry.SemiSimplexCategory.mk m ⟶ e.obj.unop) :
    ¬ Function.Surjective (ρ ≫ boundaryElementFace e).1.toOrderHom := by
  have hnot := boundaryElementFace_not_surjective e
  have hmissing : ∃ i, i ∉ Set.range (boundaryElementFace e).1.toOrderHom := by
    by_contra h
    apply hnot
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hmissing
  intro hs
  obtain ⟨j, hj⟩ := hs i
  apply hi
  refine ⟨ρ.1.toOrderHom j, ?_⟩
  change (boundaryElementFace e).1.toOrderHom (ρ.1.toOrderHom j) = i
  simpa using hj

noncomputable def boundaryElementPrecomp {m k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
    (ρ : Henry.SemiSimplexCategory.mk m ⟶ e.obj.unop) :
    (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements :=
  boundaryElementOfFace (ρ ≫ boundaryElementFace e)
    (boundaryElementFace_precomp_not_surjective e ρ)

theorem boundaryElementFace_precomp {m k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
    (ρ : Henry.SemiSimplexCategory.mk m ⟶ e.obj.unop) :
    boundaryElementFace (boundaryElementPrecomp e ρ) = ρ ≫ boundaryElementFace e := rfl

theorem boundaryElementPrecomp_eq_of_faces {m k : ℕ}
    (e e' : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
    (ρ : Henry.SemiSimplexCategory.mk m ⟶ e.obj.unop)
    (ρ' : Henry.SemiSimplexCategory.mk m ⟶ e'.obj.unop)
    (h : ρ ≫ boundaryElementFace e = ρ' ≫ boundaryElementFace e') :
    boundaryElementPrecomp e ρ = boundaryElementPrecomp e' ρ' := by
  refine Functor.Elements.ext (boundaryElementPrecomp e ρ)
    (boundaryElementPrecomp e' ρ') rfl ?_
  apply Subtype.ext
  apply ULift.ext
  change boundaryElementFace (boundaryElementPrecomp e ρ) =
    boundaryElementFace (boundaryElementPrecomp e' ρ')
  rw [boundaryElementFace_precomp, boundaryElementFace_precomp]
  exact h

def boundaryElementPrecompHom {m k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
    (ρ : Henry.SemiSimplexCategory.mk m ⟶ e.obj.unop) :
    e ⟶ boundaryElementPrecomp e ρ where
  hom := ρ.op
  map_val := rfl

def boundaryElementFactorHom {m k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
    (ρ : Henry.SemiSimplexCategory.mk m ⟶ e.obj.unop)
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk k)
    (h : ρ ≫ boundaryElementFace e = θ)
    (hθ : ¬ Function.Surjective θ.1.toOrderHom) :
    e ⟶ boundaryElementOfFace θ hθ where
  hom := ρ.op
  map_val := by
    apply Subtype.ext
    apply ULift.ext
    change ρ ≫ boundaryElementFace e = θ
    exact h

theorem boundaryElementFace_ofFace {m k : ℕ}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : ¬ Function.Surjective θ.1.toOrderHom) :
    boundaryElementFace (boundaryElementOfFace θ hθ) = θ := rfl

def dprismBdryInclusionHom (k : ℕ) :
    (dprismBdryComplex k).Hom (dprismComplex k) where
  f := id
  strictMonoOn _ _ := strictMono_id.strictMonoOn _
  map_S _ hA := by simpa using hA.1

noncomputable def faceDprismToBdry {m k : ℕ}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : ¬ Function.Surjective θ.1.toOrderHom) :
    (dprismComplex m).Hom (dprismBdryComplex k) where
  f := PV.map θ.1.toOrderHom
  strictMonoOn := map_strictMonoOn_proof (SemiSimplexCategory.strictMono θ)
  map_S A hA := by
    have hnot : ∃ i, i ∉ Set.range θ.1.toOrderHom := by
      by_contra h
      apply hθ
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hnot
    refine ⟨map_S_proof (SemiSimplexCategory.strictMono θ) A hA, Or.inr ⟨i, ?_, ?_⟩⟩
    · intro hitop
      rcases Finset.mem_image.mp hitop with ⟨a, ha, hEq⟩
      cases a with
      | top j =>
        have hji : θ.1.toOrderHom j = i := by simpa [PV.map] using hEq
        exact hi ⟨j, hji⟩
      | mid S => simp [PV.map] at hEq
    · intro S hSmid hiS
      rcases Finset.mem_image.mp hSmid with ⟨a, ha, hEq⟩
      cases a with
      | top j => simp [PV.map] at hEq
      | mid T =>
        have hEq' : T.image θ.1.toOrderHom = S := by simpa [PV.map] using hEq
        have hiT : i ∈ T.image θ.1.toOrderHom := by simpa [hEq'] using hiS
        rcases Finset.mem_image.mp hiT with ⟨j, hj, hji⟩
        exact hi ⟨j, hji⟩

noncomputable def faceDprismToSide {x : Henry.SemiSimplexCategory} {k : ℕ}
    (θ : x ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : ¬ Function.Surjective θ.1.toOrderHom) :
    (dprismComplex x.obj.len).Hom (dprismSideComplex k) where
  f := PV.map θ.1.toOrderHom
  strictMonoOn := map_strictMonoOn_proof (SemiSimplexCategory.strictMono θ)
  map_S A hA := by
    have hnot : ∃ i, i ∉ Set.range θ.1.toOrderHom := by
      by_contra h
      apply hθ
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hnot
    refine ⟨map_S_proof (SemiSimplexCategory.strictMono θ) A hA, i, ?_, ?_⟩
    · intro hitop
      rcases Finset.mem_image.mp hitop with ⟨a, ha, hEq⟩
      cases a with
      | top j =>
        have hji : θ.1.toOrderHom j = i := by simpa [PV.map] using hEq
        exact hi ⟨j, hji⟩
      | mid S => simp [PV.map] at hEq
    · intro S hSmid hiS
      rcases Finset.mem_image.mp hSmid with ⟨a, ha, hEq⟩
      cases a with
      | top j => simp [PV.map] at hEq
      | mid T =>
        have hEq' : T.image θ.1.toOrderHom = S := by simpa [PV.map] using hEq
        have hiT : i ∈ T.image θ.1.toOrderHom := by simpa [hEq'] using hiS
        rcases Finset.mem_image.mp hiT with ⟨j, hj, hji⟩
        exact hi ⟨j, hji⟩

theorem dprismCos_map_factors_bdry {m k : ℕ}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : ¬ Function.Surjective θ.1.toOrderHom) :
    (faceDprismToBdry θ hθ).toSemiSSet ≫ dprismBdryι.{u} k = dprismCos.{u}.map θ := by
  have hinc : (dprismBdryInclusionHom k).toSemiSSet = dprismBdryι.{u} k := by
    apply Complex.Hom.toSemiSSet_congr
    rfl
  have h := Complex.Hom.toSemiSSet_comp (faceDprismToBdry θ hθ)
    (dprismBdryInclusionHom k) (dprismHom (SemiSimplexCategory.strictMono θ)) rfl
  rw [← hinc]
  simpa [dprismCos] using h.symm

theorem dprismCos_map_factors_side {x : Henry.SemiSimplexCategory} {k : ℕ}
    (θ : x ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : ¬ Function.Surjective θ.1.toOrderHom) :
    (faceDprismToSide θ hθ).toSemiSSet ≫
      (dprismSideToDprismHom k).toSemiSSet = dprismCos.{u}.map θ := by
  exact (Complex.Hom.toSemiSSet_comp (faceDprismToSide θ hθ)
    (dprismSideToDprismHom k) (dprismHom (SemiSimplexCategory.strictMono θ)) rfl).symm

noncomputable def faceDprismToSideMap {x : Henry.SemiSimplexCategory} {k : ℕ}
    (θ : x ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : ¬ Function.Surjective θ.1.toOrderHom) :
    dprismCos.{u}.obj x ⟶ (dprismSideComplex k).toSemiSSet :=
  (faceDprismToSide θ hθ).toSemiSSet

theorem dprismCos_map_factors_sideMap {x : Henry.SemiSimplexCategory} {k : ℕ}
    (θ : x ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : ¬ Function.Surjective θ.1.toOrderHom) :
    faceDprismToSideMap θ hθ ≫ dprismSideToDprism k =
      dprismCos.{u}.map θ := by
  simpa [dprismSideToDprism, dprismCos, dprism, faceDprismToSideMap] using
    dprismCos_map_factors_side θ hθ

def semiSimplexOfOrderEmbedding {m k : ℕ} (t : Fin (m + 1) ↪o Fin (k + 1)) :
    Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk k := by
  let f : (Henry.SemiSimplexCategory.mk m).obj ⟶
      (Henry.SemiSimplexCategory.mk k).obj := SimplexCategory.Hom.mk t.toOrderHom
  have hf : Mono f := by
    rw [SimplexCategory.mono_iff_injective]
    exact t.injective
  exact ⟨f, hf⟩

noncomputable def faceEmbeddingOfFinset {k m : ℕ}
    (U : Finset (Fin (k + 1))) (hcard : U.card = m + 1) :
    Fin (m + 1) ↪o Fin (k + 1) :=
  (U.orderIsoOfFin hcard).toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ U))

theorem faceEmbeddingOfFinset_mem {k m : ℕ} {U : Finset (Fin (k + 1))}
    (hcard : U.card = m + 1) (a : Fin (m + 1)  ) :
    faceEmbeddingOfFinset U hcard a ∈ U :=
  (U.orderIsoOfFin hcard a).property

theorem faceEmbeddingOfFinset_mem_range {k m : ℕ} {U : Finset (Fin (k + 1))}
    (hcard : U.card = m + 1) {i : Fin (k + 1)} :
    i ∈ Set.range (faceEmbeddingOfFinset U hcard) ↔ i ∈ U := by
  constructor
  · rintro ⟨a, rfl⟩
    exact faceEmbeddingOfFinset_mem hcard a
  · intro hi
    refine ⟨(U.orderIsoOfFin hcard).symm ⟨i, hi⟩, ?_⟩
    change faceEmbeddingOfFinset U hcard ((U.orderIsoOfFin hcard).symm ⟨i, hi⟩) = i
    simp [faceEmbeddingOfFinset]

noncomputable def faceEnum {k : ℕ} (U : Finset (Fin (k + 1))) (hU : U.Nonempty) :
    Henry.SemiSimplexCategory.mk (U.card - 1) ⟶ Henry.SemiSimplexCategory.mk k := by
  have hcard : U.card = (U.card - 1) + 1 := by
    have hpos : 0 < U.card := Finset.card_pos.mpr hU
    omega
  let t := faceEmbeddingOfFinset U hcard
  exact semiSimplexOfOrderEmbedding t

theorem sideSimplex_factors_support {k n : ℕ}
    (σ : (dprismSideComplex k).Simplex n) :
    ∃ (U : Finset (Fin (k + 1))) (hU : U.Nonempty),
      U = pvBaseSupport (Finset.univ.image σ.1) ∧ (∃ i, i ∉ U) ∧
      ∃ τ : (dprismComplex (U.card - 1)).Simplex n,
        ∀ j, PV.map ((faceEnum U hU).1.toOrderHom) (τ.1 j) = σ.1 j := by
  classical
  let A : Finset (PV k) := Finset.univ.image σ.1
  have hA : (dprismComplex k).S A := σ.2.2.1
  have hAne : A.Nonempty := by
    refine ⟨σ.1 ⟨0, by omega⟩, Finset.mem_image.mpr ⟨⟨0, by omega⟩,
      Finset.mem_univ _, rfl⟩⟩
  let U : Finset (Fin (k + 1)) := pvBaseSupport A
  have hU : U.Nonempty := pvBaseSupport_nonempty hA hAne
  obtain ⟨i, hi⟩ := pvBaseSupport_proper_of_side σ.2.2.2
  have hcard : U.card = (U.card - 1) + 1 := by
    have hpos : 0 < U.card := Finset.card_pos.mpr hU
    omega
  let t : Fin ((U.card - 1) + 1) ↪o Fin (k + 1) := faceEmbeddingOfFinset U hcard
  let eV : Fin ((U.card - 1) + 1) ≃o U := U.orderIsoOfFin hcard
  let r : Fin (k + 1) → Fin ((U.card - 1) + 1) := fun j =>
    if hj : j ∈ U then eV.symm ⟨j, hj⟩ else 0
  have hr : ∀ j, r (t j) = j := by
    intro j
    have hmem := faceEmbeddingOfFinset_mem hcard j
    have hjU : t j ∈ U := by simpa [t] using hmem
    have hsub : (⟨t j, hjU⟩ : U) = eV j := by
      apply Subtype.ext
      rfl
    dsimp [r]
    rw [dif_pos hjU, hsub]
    simp
  have hθ : ¬ Function.Surjective (faceEnum U hU).1.toOrderHom := by
    intro hs
    obtain ⟨j, hj⟩ := hs i
    have hj' : faceEmbeddingOfFinset U hcard j = i := by
      simpa [faceEnum, semiSimplexOfOrderEmbedding] using hj
    have hiU : i ∈ U := by
      rw [← hj']
      exact faceEmbeddingOfFinset_mem hcard j
    exact hi hiU
  have hsupport : ∀ a ∈ A, pvSupportedBy t.toEmbedding a := by
    intro a ha
    cases a with
    | top j =>
      have hjU : j ∈ U := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Or.inl ha⟩
      exact (faceEmbeddingOfFinset_mem_range hcard).2 hjU
    | mid S =>
      intro j hj
      have hjU : j ∈ U := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Or.inr ⟨S, ha, hj⟩⟩
      exact (faceEmbeddingOfFinset_mem_range hcard).2 hjU
  let σbase : (dprismComplex k).Simplex n := ⟨σ.1, σ.2.1, σ.2.2.1⟩
  have hsupportσ : ∀ j, pvSupportedBy t.toEmbedding (σbase.1 j) := by
    intro j
    exact hsupport _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  obtain ⟨τ, hmap⟩ :=
    exists_pvPullback_simplex r t.toEmbedding t.strictMono hr σbase hsupportσ
  refine ⟨U, hU, ?_, ⟨i, hi⟩, ⟨τ, ?_⟩⟩
  · rfl
  intro j
  simpa [faceEnum, semiSimplexOfOrderEmbedding, t] using hmap j

theorem sideSimplex_factors_face {k n : ℕ} (hk : 0 < k)
    (σ : (dprismSideComplex k).Simplex n) :
    ∃ i : Fin (k + 1),
      PV.top i ∉ Finset.univ.image σ.1 ∧
      (∀ S, PV.mid S ∈ Finset.univ.image σ.1 → i ∉ S) ∧
      ∃ τ : (dprismComplex ((Finset.univ.erase i : Finset (Fin (k + 1))).card - 1)).Simplex n,
        ∀ j, PV.map ((faceEnum (Finset.univ.erase i) (erase_nonempty hk i)).1.toOrderHom)
          (τ.1 j) = σ.1 j := by
  classical
  obtain ⟨i, hiTop, hiMid⟩ := σ.2.2.2
  let A : Finset (PV k) := Finset.univ.image σ.1
  let U : Finset (Fin (k + 1)) := Finset.univ.erase i
  have hcard : U.card = (U.card - 1) + 1 := by
    have hpos : 0 < U.card := Finset.card_pos.mpr (erase_nonempty hk i)
    omega
  let t : Fin ((U.card - 1) + 1) ↪o Fin (k + 1) := faceEmbeddingOfFinset U hcard
  let eV : Fin ((U.card - 1) + 1) ≃o U := U.orderIsoOfFin hcard
  let r : Fin (k + 1) → Fin ((U.card - 1) + 1) := fun j =>
    if hj : j ∈ U then eV.symm ⟨j, hj⟩ else 0
  have hr : ∀ j, r (t j) = j := by
    intro j
    have hmem := faceEmbeddingOfFinset_mem hcard j
    have hjU : t j ∈ U := by simpa [t] using hmem
    have hsub : (⟨t j, hjU⟩ : U) = eV j := by
      apply Subtype.ext
      rfl
    dsimp [r]
    rw [dif_pos hjU, hsub]
    simp
  have hθ : ¬ Function.Surjective (faceEnum U (erase_nonempty hk i)).1.toOrderHom := by
    intro hs
    have hiU : i ∉ U := by simp [U]
    obtain ⟨j, hj⟩ := hs i
    have hj' : faceEmbeddingOfFinset U hcard j = i := by
      simpa [faceEnum, semiSimplexOfOrderEmbedding, U] using hj
    have hjU : i ∈ U := by
      rw [← hj']
      exact faceEmbeddingOfFinset_mem hcard j
    exact hiU hjU
  have hsupport : ∀ a ∈ A, pvSupportedBy t.toEmbedding a := by
    intro a ha
    cases a with
    | top j =>
      have hji : j ≠ i := by
        intro h
        subst j
        exact hiTop ha
      exact (faceEmbeddingOfFinset_mem_range hcard).2 (by simp [U, hji])
    | mid S =>
      intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact hiMid S ha hj
      exact (faceEmbeddingOfFinset_mem_range hcard).2 (by simp [U, hji])
  let σbase : (dprismComplex k).Simplex n := ⟨σ.1, σ.2.1, σ.2.2.1⟩
  have hsupportσ : ∀ j, pvSupportedBy t.toEmbedding (σbase.1 j) := by
    intro j
    exact hsupport _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  obtain ⟨τ, hmap⟩ :=
    exists_pvPullback_simplex r t.toEmbedding t.strictMono hr σbase hsupportσ
  refine ⟨i, ?_, ?_, ⟨τ, ?_⟩⟩
  · simpa [A] using hiTop
  · simpa [A] using hiMid
  · intro j
    simpa [faceEnum, semiSimplexOfOrderEmbedding, U, t] using hmap j

theorem exists_faceFactorization {c : Henry.SemiSimplexCategory} {k : ℕ}
    (θ : c ⟶ Henry.SemiSimplexCategory.mk k)
    (U : Finset (Fin (k + 1))) (hU : U.Nonempty)
    (hUrange : ∀ i ∈ U, i ∈ Set.range θ.1.toOrderHom) :
    ∃ ρ : Henry.SemiSimplexCategory.mk (U.card - 1) ⟶ c,
      ρ ≫ θ = faceEnum U hU := by
  have hcard : U.card = (U.card - 1) + 1 := by
    have hpos : 0 < U.card := Finset.card_pos.mpr hU
    omega
  let eV : Fin ((U.card - 1) + 1) ≃o U := U.orderIsoOfFin hcard
  let tU := faceEmbeddingOfFinset U hcard
  let tθ : Fin (c.obj.len + 1) ↪o Fin (k + 1) :=
    OrderEmbedding.ofStrictMono θ.1.toOrderHom (SemiSimplexCategory.strictMono θ)
  have hpre : ∀ a, tU a ∈ Set.range tθ := by
    intro a
    exact hUrange (tU a) (eV a).property
  let r : Fin ((U.card - 1) + 1) → Fin (c.obj.len + 1) :=
    fun a => Classical.choose (hpre a)
  have hr : ∀ a, tθ (r a) = tU a := fun a => Classical.choose_spec (hpre a)
  have hrStrict : StrictMono r := by
    intro a b hab
    apply tθ.lt_iff_lt.mp
    rw [hr a, hr b]
    exact tU.strictMono hab
  let rEmb : Fin ((U.card - 1) + 1) ↪o Fin (c.obj.len + 1) :=
    OrderEmbedding.ofStrictMono r hrStrict
  let ρHom : (Henry.SemiSimplexCategory.mk (U.card - 1)).obj ⟶ c.obj :=
    SimplexCategory.Hom.mk rEmb.toOrderHom
  have hρMono : Mono ρHom := by
    rw [SimplexCategory.mono_iff_injective]
    exact rEmb.injective
  let ρ : Henry.SemiSimplexCategory.mk (U.card - 1) ⟶ c := ⟨ρHom, hρMono⟩
  refine ⟨ρ, ?_⟩
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext a
  exact hr a

theorem exists_support_face_factorization_of_map {c : Henry.SemiSimplexCategory} {k n : ℕ}
    (θ : c ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : ¬ Function.Surjective θ.1.toOrderHom)
    (τ : (dprismComplex c.obj.len).Simplex n)
    (σ : (dprismSideComplex k).Simplex n)
    (hσ : ∀ j, σ.1 j = PV.map θ.1.toOrderHom (τ.1 j)) :
    ∃ (U : Finset (Fin (k + 1))) (hU : U.Nonempty),
      U = pvBaseSupport (Finset.univ.image σ.1) ∧
      ∃ (ρ : Henry.SemiSimplexCategory.mk (U.card - 1) ⟶ c),
        ρ ≫ θ = faceEnum U hU ∧
        ∃ τ₀ : (dprismComplex (U.card - 1)).Simplex n,
          (∀ j, PV.map (faceEnum U hU).1.toOrderHom (τ₀.1 j) = σ.1 j) ∧
          ∀ j, PV.map ρ.1.toOrderHom (τ₀.1 j) = τ.1 j := by
  classical
  have hseq : σ.1 = fun j => PV.map θ.1.toOrderHom (τ.1 j) := funext hσ
  obtain ⟨U, hU, hUsupport, -, τ₀, hτ₀⟩ := sideSimplex_factors_support σ
  have hUrange : ∀ i ∈ U, i ∈ Set.range θ.1.toOrderHom := by
    intro i hi
    have hi' : i ∈ pvBaseSupport
        (Finset.univ.image (fun j => PV.map θ.1.toOrderHom (τ.1 j))) := by
      rw [hUsupport] at hi
      simpa [hseq] using hi
    exact pvBaseSupport_map_subset_range θ τ i hi'
  obtain ⟨ρ, hρ⟩ := exists_faceFactorization θ U hU hUrange
  have hρfun : (fun i => θ.1.toOrderHom (ρ.1.toOrderHom i)) =
      fun i => (faceEnum U hU).1.toOrderHom i := by
    funext i
    have h := congrArg
      (fun g : Henry.SemiSimplexCategory.mk (U.card - 1) ⟶
        Henry.SemiSimplexCategory.mk k => g.1.toOrderHom i) hρ
    simpa using h
  refine ⟨U, hU, hUsupport, ρ, hρ, τ₀, hτ₀, ?_⟩
  intro j
  apply pv_map_injective (SemiSimplexCategory.strictMono θ).injective
  calc
    PV.map θ.1.toOrderHom (PV.map ρ.1.toOrderHom (τ₀.1 j)) =
        PV.map (θ.1.toOrderHom ∘ ρ.1.toOrderHom) (τ₀.1 j) := by
          exact (congrFun (PV.map_comp ρ.1.toOrderHom θ.1.toOrderHom) (τ₀.1 j)).symm
    _ = PV.map (faceEnum U hU).1.toOrderHom (τ₀.1 j) := by
      change PV.map (fun i => θ.1.toOrderHom (ρ.1.toOrderHom i)) _ = _
      rw [hρfun]
    _ = σ.1 j := hτ₀ j
    _ = PV.map θ.1.toOrderHom (τ.1 j) := hσ j

theorem exists_faceFactorization_to_support {c : Henry.SemiSimplexCategory} {k n : ℕ}
    (θ : c ⟶ Henry.SemiSimplexCategory.mk k)
    (τ : (dprismComplex c.obj.len).Simplex n)
    (σ : (dprismSideComplex k).Simplex n)
    (hσ : ∀ j, σ.1 j = PV.map θ.1.toOrderHom (τ.1 j))
    (U : Finset (Fin (k + 1)))
    (hUsupport : U = pvBaseSupport (Finset.univ.image σ.1))
    (hU : U.Nonempty)
    (τ₀ : (dprismComplex (U.card - 1)).Simplex n)
    (hτ₀ : ∀ j, PV.map (faceEnum U hU).1.toOrderHom (τ₀.1 j) = σ.1 j) :
    ∃ ρ : Henry.SemiSimplexCategory.mk (U.card - 1) ⟶ c,
      ρ ≫ θ = faceEnum U hU ∧
      ∀ j, PV.map ρ.1.toOrderHom (τ₀.1 j) = τ.1 j := by
  have hseq : σ.1 = fun j => PV.map θ.1.toOrderHom (τ.1 j) := funext hσ
  have hUrange : ∀ i ∈ U, i ∈ Set.range θ.1.toOrderHom := by
    intro i hi
    have hi' : i ∈ pvBaseSupport
        (Finset.univ.image (fun j => PV.map θ.1.toOrderHom (τ.1 j))) := by
      rw [hUsupport] at hi
      simpa [hseq] using hi
    exact pvBaseSupport_map_subset_range θ τ i hi'
  obtain ⟨ρ, hρ⟩ := exists_faceFactorization θ U hU hUrange
  have hρfun : (fun i => θ.1.toOrderHom (ρ.1.toOrderHom i)) =
      fun i => (faceEnum U hU).1.toOrderHom i := by
    funext i
    have h := congrArg
      (fun g : Henry.SemiSimplexCategory.mk (U.card - 1) ⟶
        Henry.SemiSimplexCategory.mk k => g.1.toOrderHom i) hρ
    simpa using h
  refine ⟨ρ, hρ, ?_⟩
  intro j
  apply pv_map_injective (SemiSimplexCategory.strictMono θ).injective
  calc
    PV.map θ.1.toOrderHom (PV.map ρ.1.toOrderHom (τ₀.1 j)) =
        PV.map (θ.1.toOrderHom ∘ ρ.1.toOrderHom) (τ₀.1 j) := by
          exact (congrFun (PV.map_comp ρ.1.toOrderHom θ.1.toOrderHom) (τ₀.1 j)).symm
    _ = PV.map (faceEnum U hU).1.toOrderHom (τ₀.1 j) := by
      change PV.map (fun i => θ.1.toOrderHom (ρ.1.toOrderHom i)) _ = _
      rw [hρfun]
    _ = σ.1 j := hτ₀ j
    _ = PV.map θ.1.toOrderHom (τ.1 j) := hσ j

theorem boundaryElement_map_eq_stdSimplexMap {k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements) :
    (Presheaf.coconeOfRepresentable (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app (op e) ≫
      (Henry.SemiSSet.boundary.{u} k).ι =
        Henry.SemiSSet.stdSimplex.map (boundaryElementFace e) := by
  change uliftYonedaEquiv.symm e.val ≫ (Henry.SemiSSet.boundary.{u} k).ι =
    Henry.SemiSSet.stdSimplex.map (boundaryElementFace e)
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp]
  simp [Presheaf.coconeOfRepresentable, boundaryElementFace, uliftYonedaEquiv]

theorem dprismLanBoundary_leg {k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements) :
    (dprismLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app (op e) ≫
      dprismLan.map (Henry.SemiSSet.boundary.{u} k).ι ≫
      dprismLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) =
        dprismCos.map (boundaryElementFace e) := by
  let c := e.obj.unop
  let f := uliftYonedaEquiv.symm e.val
  let g := (Henry.SemiSSet.boundary.{u} k).ι
  have hchar : f ≫ g = Henry.SemiSSet.stdSimplex.map (boundaryElementFace e) :=
    boundaryElement_map_eq_stdSimplexMap e
  have hmap : dprismLan.map f ≫ dprismLan.map g = dprismLan.map (f ≫ g) :=
    (dprismLan.map_comp f g).symm
  have hnat : dprismLan.map (Henry.SemiSSet.stdSimplex.map (boundaryElementFace e)) ≫
      dprismLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) =
        dprismLanRepresentableIso.hom.app c ≫ dprismCos.map (boundaryElementFace e) := by
    simpa using dprismLanRepresentableIso.hom.naturality (boundaryElementFace e)
  change (dprismLanRepresentableIso.inv.app c ≫
      dprismLan.map (uliftYonedaEquiv.symm e.val)) ≫
      dprismLan.map (Henry.SemiSSet.boundary.{u} k).ι ≫
        dprismLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) = _
  calc
    _ = ((dprismLanRepresentableIso.inv.app c ≫ dprismLan.map f) ≫
        dprismLan.map g) ≫
          dprismLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) := by
          rfl
    _ = (dprismLanRepresentableIso.inv.app c ≫
        (dprismLan.map f ≫ dprismLan.map g)) ≫
          dprismLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) := by
          simp only [Category.assoc]
    _ = (dprismLanRepresentableIso.inv.app c ≫ dprismLan.map (f ≫ g)) ≫
        dprismLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) := by
          rw [hmap]
    _ = (dprismLanRepresentableIso.inv.app c ≫
        dprismLan.map (Henry.SemiSSet.stdSimplex.map (boundaryElementFace e))) ≫
          dprismLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) := by rw [hchar]
    _ = dprismLanRepresentableIso.inv.app c ≫
        (dprismLanRepresentableIso.hom.app c ≫ dprismCos.map (boundaryElementFace e)) := by
          rw [Category.assoc, hnat]
    _ = dprismCos.map (boundaryElementFace e) := by simp [Category.assoc]

noncomputable def dprismLanBoundarySideCocone (k : ℕ) :
    Cocone (dprismLanElementsDiagram (Henry.SemiSSet.boundary.{u} k).toFunctor) where
  pt := (dprismSideComplex k).toSemiSSet
  ι :=
    { app x :=
        faceDprismToSideMap (boundaryElementFace x.unop)
          (boundaryElementFace_not_surjective x.unop)
      naturality := by
        intro x y f
        change dprismCos.map ((Functor.Elements.π
          (Henry.SemiSSet.boundary.{u} k).toFunctor).leftOp.map f) ≫
            faceDprismToSideMap (boundaryElementFace y.unop)
              (boundaryElementFace_not_surjective y.unop) =
          faceDprismToSideMap (boundaryElementFace x.unop)
            (boundaryElementFace_not_surjective x.unop)
        letI : Mono (dprismSideToDprism k) := dprismSideToDprism_mono' k
        apply (cancel_mono (dprismSideToDprism k)).1
        let q := dprismLan.map (Henry.SemiSSet.boundary.{u} k).ι ≫
          dprismLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k)
        have hc := (dprismLanElementsCocone
          (Henry.SemiSSet.boundary.{u} k).toFunctor).w f
        have hlegY : (dprismLanElementsCocone
              (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app y ≫ q =
            dprismCos.map (boundaryElementFace y.unop) := by
          change (dprismLanElementsCocone
              (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app y ≫
            dprismLan.map (Henry.SemiSSet.boundary.{u} k).ι ≫
              dprismLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) = _
          exact dprismLanBoundary_leg y.unop
        have hlegX : (dprismLanElementsCocone
              (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app x ≫ q =
            dprismCos.map (boundaryElementFace x.unop) := by
          change (dprismLanElementsCocone
              (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app x ≫
            dprismLan.map (Henry.SemiSSet.boundary.{u} k).ι ≫
              dprismLanRepresentableIso.hom.app (Henry.SemiSimplexCategory.mk k) = _
          exact dprismLanBoundary_leg x.unop
        have hD :
            (dprismLanElementsDiagram
              (Henry.SemiSSet.boundary.{u} k).toFunctor).map f ≫
                dprismCos.map (boundaryElementFace y.unop) =
              dprismCos.map (boundaryElementFace x.unop) := by
          calc
            _ = (dprismLanElementsDiagram
                (Henry.SemiSSet.boundary.{u} k).toFunctor).map f ≫
                ((dprismLanElementsCocone
                  (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app y ≫ q) := by
                    rw [hlegY]
            _ = ((dprismLanElementsDiagram
                (Henry.SemiSSet.boundary.{u} k).toFunctor).map f ≫
              (dprismLanElementsCocone
                (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app y) ≫ q := by
                  exact (Category.assoc _ _ _).symm
            _ = (dprismLanElementsCocone
                  (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app x ≫ q := by
                    rw [hc]
            _ = dprismCos.map (boundaryElementFace x.unop) := hlegX
        have hD' :
            dprismCos.map ((Functor.Elements.π
              (Henry.SemiSSet.boundary.{u} k).toFunctor).leftOp.map f) ≫
                dprismCos.map (boundaryElementFace y.unop) =
              dprismCos.map (boundaryElementFace x.unop) := by
          simpa [dprismLanElementsDiagram] using hD
        rw [Category.assoc, dprismCos_map_factors_sideMap, hD',
          ← dprismCos_map_factors_sideMap]
    }

theorem dprismLanBoundarySideCocone_precomp {m k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
    (ρ : Henry.SemiSimplexCategory.mk m ⟶ e.obj.unop) :
    dprismCos.map ρ ≫ (dprismLanBoundarySideCocone k).ι.app (op e) =
      (dprismLanBoundarySideCocone k).ι.app
        (op (boundaryElementPrecomp e ρ)) := by
  have h := (dprismLanBoundarySideCocone k).w
    (boundaryElementPrecompHom e ρ).op
  change dprismCos.map ρ.op.unop ≫ (dprismLanBoundarySideCocone k).ι.app (op e) = _
  exact h

theorem dprismLanElementsCocone_precomp {m k : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
    (ρ : Henry.SemiSimplexCategory.mk m ⟶ e.obj.unop) :
    dprismCos.map ρ ≫
        (dprismLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app (op e) =
      (dprismLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app
        (op (boundaryElementPrecomp e ρ)) := by
  have h := (dprismLanElementsCocone
    (Henry.SemiSSet.boundary.{u} k).toFunctor).w
    (boundaryElementPrecompHom e ρ).op
  change dprismCos.map ρ.op.unop ≫
      (dprismLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app (op e) = _
  exact h

theorem dprismLanElementsCocone_precomp_apply {m k n : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
    (ρ : Henry.SemiSimplexCategory.mk m ⟶ e.obj.unop)
    (τ₀ : (dprismComplex m).Simplex n) :
    ((dprismLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app
        (op (boundaryElementPrecomp e ρ))).app
        (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ₀) =
      ((dprismLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app
        (op e)).app (op (Henry.SemiSimplexCategory.mk n))
        ((dprismCos.map ρ).app (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ₀)) := by
  have h := congrArg
    (fun f : dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk m) ⟶
      dprismLan.{u}.obj (Henry.SemiSSet.boundary.{u} k).toFunctor =>
      f.app (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ₀))
    (dprismLanElementsCocone_precomp e ρ)
  have h' := h.symm
  change
    ((dprismLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app
      (op (boundaryElementPrecomp e ρ))).app (op (Henry.SemiSimplexCategory.mk n))
        (ULift.up τ₀) =
      ((dprismLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app
        (op e)).app (op (Henry.SemiSimplexCategory.mk n))
        ((dprismCos.map ρ).app (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ₀)) at h'
  exact h'

theorem dprismLanElementsCocone_factor_apply {m k n : ℕ}
    (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
    (ρ : Henry.SemiSimplexCategory.mk m ⟶ e.obj.unop)
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk k)
    (h : ρ ≫ boundaryElementFace e = θ)
    (hθ : ¬ Function.Surjective θ.1.toOrderHom)
    (τ₀ : (dprismComplex m).Simplex n) :
    ((dprismLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app
        (op (boundaryElementOfFace θ hθ))).app
        (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ₀) =
      ((dprismLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app
        (op e)).app (op (Henry.SemiSimplexCategory.mk n))
        ((dprismCos.map ρ).app (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ₀)) := by
  have hcolim := (dprismLanElementsCocone
    (Henry.SemiSSet.boundary.{u} k).toFunctor).w
      (boundaryElementFactorHom e ρ θ h hθ).op
  have heval := congrArg (fun f => f.app
      (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ₀)) hcolim
  have heval' := heval.symm
  change ((dprismLanElementsCocone
      (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app
        (op (boundaryElementOfFace θ hθ))).app
        (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ₀) =
      ((dprismLanElementsCocone
        (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app (op e)).app
        (op (Henry.SemiSimplexCategory.mk n))
        ((dprismCos.map ρ).app (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ₀)) at heval'
  exact heval'

theorem boundary_side_representatives_equal {k n : ℕ}
    (e e' : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
    (τ : (dprismCos.{u}.obj e.obj.unop).obj
      (op (Henry.SemiSimplexCategory.mk n)))
    (τ' : (dprismCos.{u}.obj e'.obj.unop).obj
      (op (Henry.SemiSimplexCategory.mk n)))
    (hside : ((dprismLanBoundarySideCocone k).ι.app (op e)).app
        (op (Henry.SemiSimplexCategory.mk n)) τ =
      ((dprismLanBoundarySideCocone k).ι.app (op e')).app
        (op (Henry.SemiSimplexCategory.mk n)) τ') :
    ((dprismLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app
        (op e)).app (op (Henry.SemiSimplexCategory.mk n)) τ =
      ((dprismLanElementsCocone (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app
        (op e')).app (op (Henry.SemiSimplexCategory.mk n)) τ' := by
  classical
  let z : ULift.{u} ((dprismSideComplex k).Simplex n) :=
    ((dprismLanBoundarySideCocone k).ι.app (op e)).app
      (op (Henry.SemiSimplexCategory.mk n)) τ
  let z' : ULift.{u} ((dprismSideComplex k).Simplex n) :=
    ((dprismLanBoundarySideCocone k).ι.app (op e')).app
      (op (Henry.SemiSimplexCategory.mk n)) τ'
  let σ : (dprismSideComplex k).Simplex n := z.down
  have hσeq : σ = z'.down := congrArg ULift.down hside
  have hσ : ∀ j, σ.1 j = PV.map (boundaryElementFace e).1.toOrderHom (τ.down.1 j) := by
    intro j
    change PV.map (boundaryElementFace e).1.toOrderHom (τ.down.1 j) = _
    rfl
  have hσ' : ∀ j, z'.down.1 j =
      PV.map (boundaryElementFace e').1.toOrderHom (τ'.down.1 j) := by
    intro j
    change PV.map (boundaryElementFace e').1.toOrderHom (τ'.down.1 j) = _
    rfl
  have hσ₂ : ∀ j, σ.1 j =
      PV.map (boundaryElementFace e').1.toOrderHom (τ'.down.1 j) := by
    intro j
    rw [hσeq]
    exact hσ' j
  obtain ⟨U, hU, hUsupport, hUproper, τ₀, hfaceMap⟩ :=
    sideSimplex_factors_support σ
  obtain ⟨i, hi⟩ := hUproper
  have hcard : U.card = (U.card - 1) + 1 := by
    have hpos : 0 < U.card := Finset.card_pos.mpr hU
    omega
  have hθ : ¬ Function.Surjective (faceEnum U hU).1.toOrderHom := by
    intro hs
    obtain ⟨j, hj⟩ := hs i
    have hj' : faceEmbeddingOfFinset U hcard j = i := by
      simpa [faceEnum, semiSimplexOfOrderEmbedding] using hj
    have hjU := faceEmbeddingOfFinset_mem hcard j
    rw [hj'] at hjU
    exact hi hjU
  obtain ⟨ρ, hρ, hmap⟩ := exists_faceFactorization_to_support
    (boundaryElementFace e) τ.down σ hσ U hUsupport hU τ₀ hfaceMap
  obtain ⟨ρ', hρ', hmap'⟩ := exists_faceFactorization_to_support
    (boundaryElementFace e') τ'.down σ hσ₂ U hUsupport hU τ₀ hfaceMap
  have hρ'face : ρ' ≫ boundaryElementFace e' = faceEnum U hU := hρ'
  have hρfaces : ρ ≫ boundaryElementFace e = ρ' ≫ boundaryElementFace e' :=
    hρ.trans hρ'face.symm
  have hmapUL :
      (dprismCos.map ρ).app (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ₀) = τ := by
    apply ULift.ext
    apply Subtype.ext
    funext j
    change PV.map ρ.1.toOrderHom (τ₀.1 j) = τ.down.1 j
    exact hmap j
  have hmapUL' :
      (dprismCos.map ρ').app (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ₀) = τ' := by
    apply ULift.ext
    apply Subtype.ext
    funext j
    change PV.map ρ'.1.toOrderHom (τ₀.1 j) = τ'.down.1 j
    exact hmap' j
  have hEval := dprismLanElementsCocone_factor_apply e ρ
    (faceEnum U hU) hρ hθ τ₀
  have hEval' := dprismLanElementsCocone_factor_apply e' ρ'
    (faceEnum U hU) hρ'face hθ τ₀
  rw [hmapUL] at hEval
  rw [hmapUL'] at hEval'
  calc
    _ = ((dprismLanElementsCocone
          (Henry.SemiSSet.boundary.{u} k).toFunctor).ι.app
          (op (boundaryElementOfFace (faceEnum U hU) hθ))).app
          (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ₀) := hEval.symm
    _ = _ := hEval'

theorem exists_side_boundary_representation {k n : ℕ} (hk : 0 < k)
    (z : ULift ((dprismSideComplex k).Simplex n)) :
    ∃ (e : (Henry.SemiSSet.boundary.{u} k).toFunctor.Elements)
      (τ : (dprismCos.{u}.obj e.obj.unop).obj
        (op (Henry.SemiSimplexCategory.mk n))),
      ((dprismLanBoundarySideCocone k).ι.app (op e)).app
        (op (Henry.SemiSimplexCategory.mk n)) τ = z := by
  classical
  let σ : (dprismSideComplex k).Simplex n := z.down
  obtain ⟨i, hiTop, hiMid, τ, hmap⟩ := sideSimplex_factors_face hk σ
  let θ := faceEnum (Finset.univ.erase i) (erase_nonempty hk i)
  have hcard : (Finset.univ.erase i : Finset (Fin (k + 1))).card =
      ((Finset.univ.erase i : Finset (Fin (k + 1))).card - 1) + 1 := by
    have hpos : 0 < (Finset.univ.erase i : Finset (Fin (k + 1))).card :=
      Finset.card_pos.mpr (erase_nonempty hk i)
    omega
  have hθ : ¬ Function.Surjective θ.1.toOrderHom := by
    intro hs
    have hiU : i ∉ (Finset.univ.erase i : Finset (Fin (k + 1))) := by simp
    obtain ⟨j, hj⟩ := hs i
    have hj' : faceEmbeddingOfFinset (Finset.univ.erase i) hcard j = i := by
      simpa [θ, faceEnum, semiSimplexOfOrderEmbedding] using hj
    have hjU : i ∈ (Finset.univ.erase i : Finset (Fin (k + 1))) := by
      have hjU' := faceEmbeddingOfFinset_mem hcard j
      rw [hj'] at hjU'
      exact hjU'
    exact hiU hjU
  refine ⟨boundaryElementOfFace θ hθ, ULift.up τ, ?_⟩
  change (faceDprismToSideMap θ hθ).app
      (op (Henry.SemiSimplexCategory.mk n)) (ULift.up τ) = ULift.up σ
  apply ULift.ext
  apply Subtype.ext
  funext j
  change PV.map θ.1.toOrderHom (τ.1 j) = σ.1 j
  simpa [θ, faceEnum, semiSimplexOfOrderEmbedding] using hmap j

end HomotopyHypothesis.Approximation.DerivedPrismRelative
