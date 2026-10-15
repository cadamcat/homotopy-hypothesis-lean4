import Mathlib.AlgebraicTopology.TopologicalSimplex
import HomotopyHypothesis.Cylinder.SimplicialCategory.Cofibrations
import HomotopyHypothesis.Cylinder.SimplicialCategory.CylinderCategory
import HomotopyHypothesis.Cylinder.SimplicialCategory.FreeAlgKan
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexSubfunctors
import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.CDeltaHornWeakEquivalence
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.ExistsStandardRealization
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.StandardRealizationIsHomotopyFullyFaithful
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Cylinder.SemisimplicialCategory.WeakEquivalences
/-!
# Canonical horn retractions and coherent simplex contractions in `C^Δ`

This file constructs:
1. Functoriality of `stdSimplexCDelta` with respect to maps in `SemiSimplexCategory`.
2. Canonical horn retractions `canonicalHornRetraction n k : Δ_{n+1} ⟶ Λ^{n+1}_k` in `CDelta`
   representing the algebraic Kan filler operation `AlgKan.fill`.
3. Coherent weak equivalences `simplexContraction n : Δ_n ⟶ Δ_0` in `CDelta` compatible with all
   semi-simplicial face maps `[k] ⟶ [n]`.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite ConcreteCategory

namespace HomotopyHypothesis.Cylinder.SimplicialCategory

open HomotopyHypothesis.Henry

/-!
## Functoriality of `stdSimplexCDelta`
-/

/-- The morphism `Δ_m ⟶ Δ_n` in `CDelta` induced by `σ : [m] ⟶ [n]` in `SemiSimplexCategory`. -/
noncomputable def stdSimplexCDeltaMap {m n : ℕ}
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    stdSimplexCDelta.{u} m ⟶ stdSimplexCDelta.{u} n :=
  ObjectProperty.homMk (freeAlgKanMap (SemiSSet.stdSimplex.{u}.map σ))

@[simp]
lemma stdSimplexCDeltaMap_id (n : ℕ) :
    stdSimplexCDeltaMap.{u} (𝟙 (Henry.SemiSimplexCategory.mk n)) = 𝟙 (stdSimplexCDelta.{u} n) := by
  apply ObjectProperty.hom_ext
  change freeAlgKanMap (SemiSSet.stdSimplex.{u}.map (𝟙 _)) = 𝟙 _
  rw [CategoryTheory.Functor.map_id, freeAlgKanMap_id]

@[simp]
lemma stdSimplexCDeltaMap_comp {l m n : ℕ}
    (σ : Henry.SemiSimplexCategory.mk l ⟶ Henry.SemiSimplexCategory.mk m)
    (τ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    stdSimplexCDeltaMap.{u} (σ ≫ τ) =
      stdSimplexCDeltaMap.{u} σ ≫ stdSimplexCDeltaMap.{u} τ := by
  apply ObjectProperty.hom_ext
  change freeAlgKanMap (SemiSSet.stdSimplex.{u}.map (σ ≫ τ)) =
    freeAlgKanMap (SemiSSet.stdSimplex.{u}.map σ) ≫ freeAlgKanMap (SemiSSet.stdSimplex.{u}.map τ)
  rw [CategoryTheory.Functor.map_comp, freeAlgKanMap_comp]

lemma stdSimplexCDeltaMap_simplexMaps {m n : ℕ}
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    CDelta.simplexMaps (stdSimplexCDeltaMap.{u} σ) :=
  ⟨m, n, σ,
    freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)),
    freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n)),
    freeAlgKan_isFreeOn _, freeAlgKan_isFreeOn _,
    freeAlgKanUnit_comp_freeAlgKanMap (SemiSSet.stdSimplex.{u}.map σ)⟩

lemma stdSimplexCDeltaMap_weakEquivalence {m n : ℕ}
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    weakEquivalences CDelta.{u} (stdSimplexCDeltaMap.{u} σ) :=
  Cylinder.SemisimplicialCategory.cDelta_simplexMaps_weakEquivalence _ (stdSimplexCDeltaMap_simplexMaps σ)

lemma stdSimplexCDeltaMap_cofibration {m n : ℕ}
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    cofibrations CDelta.{u} (stdSimplexCDeltaMap.{u} σ) := by
  let B := SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n)
  have heq : SemiSSet.stdSimplex.{u}.map σ =
      (simplexSubfunctorIso.{u} σ).hom ≫
        Subfunctor.homOfLe (le_top : simplexSubfunctor.{u} σ ≤ ⊤) ≫
        (topSubfunctorIso B).hom := by
    ext Δ x
    rfl
  change AlgKan.cellularMaps (freeAlgKanMap (SemiSSet.stdSimplex.{u}.map σ))
  rw [heq, freeAlgKanMap_comp, freeAlgKanMap_comp]
  have : IsIso (freeAlgKanMap (simplexSubfunctorIso.{u} σ).hom) :=
    isIso_freeAlgKanMap_of_isIso (simplexSubfunctorIso.{u} σ).hom
  have : IsIso (freeAlgKanMap (topSubfunctorIso B).hom) :=
    isIso_freeAlgKanMap_of_isIso (topSubfunctorIso B).hom
  exact MorphismProperty.comp_mem _ _ _ (cellularMaps_of_isIso _)
    (MorphismProperty.comp_mem _ _ _
      (cellularMaps_freeAlgKanMap_of_le le_top)
      (cellularMaps_of_isIso _))

/-!
## Canonical horn inclusions and retractions in `CDelta`
-/

/-- The horn inclusion `Λ^{n+1}_k ⟶ Δ_{n+1}` in `CDelta`. -/
noncomputable def hornInclusionCDelta (n : ℕ) (k : Fin (n + 2)) :
    hornCDelta.{u} n k ⟶ stdSimplexCDelta.{u} (n + 1) :=
  ObjectProperty.homMk (freeAlgKanMap (SemiSSet.horn.{u} (n + 1) k).ι)

lemma hornInclusionCDelta_cofibration (n : ℕ) (k : Fin (n + 2)) :
    cofibrations CDelta.{u} (hornInclusionCDelta.{u} n k) := by
  let B := SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))
  have heq : (SemiSSet.horn.{u} (n + 1) k).ι =
      Subfunctor.homOfLe (le_top : SemiSSet.horn.{u} (n + 1) k ≤ ⊤) ≫
        (topSubfunctorIso B).hom :=
    rfl
  change AlgKan.cellularMaps (freeAlgKanMap (SemiSSet.horn.{u} (n + 1) k).ι)
  rw [heq, freeAlgKanMap_comp]
  have : IsIso (freeAlgKanMap (topSubfunctorIso B).hom) :=
    isIso_freeAlgKanMap_of_isIso (topSubfunctorIso B).hom
  exact MorphismProperty.comp_mem _ _ _
    (cellularMaps_freeAlgKanMap_of_le le_top)
    (cellularMaps_of_isIso _)

lemma hornInclusionCDelta_weakEquivalence (n : ℕ) (k : Fin (n + 2)) :
    weakEquivalences CDelta.{u} (hornInclusionCDelta.{u} n k) := by
  refine Packages.cDelta_horn_weakEquivalence n k
    (freeAlgKanUnit (SemiSSet.horn.{u} (n + 1) k).toFunctor)
    (freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))))
    (freeAlgKan_isFreeOn _) (freeAlgKan_isFreeOn _)
    (hornInclusionCDelta.{u} n k) ?_
  exact freeAlgKanUnit_comp_freeAlgKanMap (SemiSSet.horn.{u} (n + 1) k).ι

/-- The canonical retraction `Δ_{n+1} ⟶ Λ^{n+1}_k` in `CDelta` classifying the algebraic Kan
filler of the universal horn. -/
noncomputable def canonicalHornRetraction (n : ℕ) (k : Fin (n + 2)) :
    stdSimplexCDelta.{u} (n + 1) ⟶ hornCDelta.{u} n k :=
  ObjectProperty.homMk
    ((freeAlgKan_isFreeOn
      (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1)))
      (hornCDelta.{u} n k).obj
      ((hornCDelta.{u} n k).obj.fill n k
        (freeAlgKanUnit (SemiSSet.horn.{u} (n + 1) k).toFunctor))).choose)

lemma freeAlgKanUnit_comp_canonicalHornRetraction (n : ℕ) (k : Fin (n + 2)) :
    freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))) ≫
      (canonicalHornRetraction.{u} n k).hom.hom =
      (hornCDelta.{u} n k).obj.fill n k
        (freeAlgKanUnit (SemiSSet.horn.{u} (n + 1) k).toFunctor) :=
  (freeAlgKan_isFreeOn
    (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1)))
    (hornCDelta.{u} n k).obj
    ((hornCDelta.{u} n k).obj.fill n k
      (freeAlgKanUnit (SemiSSet.horn.{u} (n + 1) k).toFunctor))).choose_spec.1

@[simp]
lemma hornInclusionCDelta_comp_canonicalHornRetraction (n : ℕ) (k : Fin (n + 2)) :
    hornInclusionCDelta.{u} n k ≫ canonicalHornRetraction.{u} n k =
      𝟙 (hornCDelta.{u} n k) := by
  apply ObjectProperty.hom_ext
  apply freeAlgKan_hom_ext
  have h1 := freeAlgKanUnit_comp_canonicalHornRetraction.{u} n k
  have h2 := freeAlgKanUnit_comp_freeAlgKanMap (SemiSSet.horn.{u} (n + 1) k).ι
  have h3 := (hornCDelta.{u} n k).obj.fill_spec n k
    (freeAlgKanUnit (SemiSSet.horn.{u} (n + 1) k).toFunctor)
  exact (congrArg (· ≫ (canonicalHornRetraction.{u} n k).hom.hom) h2).trans
    ((congrArg ((SemiSSet.horn.{u} (n + 1) k).ι ≫ ·) h1).trans
      (h3.trans (Category.comp_id _).symm))

lemma canonicalHornRetraction_comp_hom_fill (n : ℕ) (k : Fin (n + 2))
    {Z : AlgKan.{u}} (g : (hornCDelta.{u} n k).obj ⟶ Z) :
    freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))) ≫
      ((canonicalHornRetraction.{u} n k).hom ≫ g).hom =
      Z.fill n k (freeAlgKanUnit (SemiSSet.horn.{u} (n + 1) k).toFunctor ≫ g.hom) :=
  (congrArg (· ≫ g.hom) (freeAlgKanUnit_comp_canonicalHornRetraction.{u} n k)).trans
    (g.fill_hom n k (freeAlgKanUnit (SemiSSet.horn.{u} (n + 1) k).toFunctor))

/-!
## Extension of morphisms into `Δ_0` along cofibrations and coherent contractions `Δ_n ⟶ Δ_0`
-/

noncomputable def constToTopZero (T : TopCat.{u}) :
    T ⟶ SimplexCategory.toTop.{u}.obj (SimplexCategory.mk 0) :=
  TopCat.ofHom ⟨fun _ => default, continuous_const⟩

/-- Every morphism `a : A ⟶ Δ_0` in `CDelta` extends along any cofibration `i : A ⟶ B`. -/
theorem exists_extension_to_stdSimplexCDelta_zero {A B : CDelta.{u}} (i : A ⟶ B)
    (hi : cofibrations CDelta.{u} i) (a : A ⟶ stdSimplexCDelta.{u} 0) :
    ∃ b : B ⟶ stdSimplexCDelta.{u} 0, i ≫ b = a := by
  obtain ⟨R, hR⟩ := Packages.exists_standardRealization.{u}
  let F : CDelta.{u} ⥤ FinCell.{u} := hR.isCellularRealization.toFinCell
  have hFF : IsHomotopyFullyFaithful F := Packages.standardRealization_isHomotopyFullyFaithful hR
  obtain ⟨e, _⟩ := hR.simplex
  let e₀ : R.obj (stdSimplexCDelta.{u} 0) ≅
      SemiSSet.toTop.{u}.obj (Henry.SemiSimplexCategory.mk 0) :=
    e 0 (stdSimplexCDelta.{u} 0)
      (freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk 0)))
      (freeAlgKan_isFreeOn _)
  let ptMap : R.obj B ⟶ SemiSSet.toTop.{u}.obj (Henry.SemiSimplexCategory.mk 0) :=
    constToTopZero (R.obj B)
  let b_top : F.obj B ⟶ F.obj (stdSimplexCDelta.{u} 0) :=
    ObjectProperty.homMk (ptMap ≫ e₀.inv)
  have hb_top : F.map i ≫ b_top = F.map a := by
    apply ObjectProperty.hom_ext
    change R.map i ≫ ptMap ≫ e₀.inv = R.map a
    rw [← cancel_mono e₀.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    ext x
    exact @Subsingleton.elim (SimplexCategory.toTop.{u}.obj (SimplexCategory.mk 0)) inferInstance _ _
  obtain ⟨b, hb, -⟩ := hFF i hi a b_top hb_top
  exact ⟨b, hb⟩

/-- A coherent family of contractions `Δ_k ⟶ Δ_0` for `k ≤ N`. -/
structure CoherentContractionUpTo (N : ℕ) where
  c : ∀ k ≤ N, stdSimplexCDelta.{u} k ⟶ stdSimplexCDelta.{u} 0
  c_zero : c 0 (Nat.zero_le N) = 𝟙 (stdSimplexCDelta.{u} 0)
  c_comp : ∀ {k m : ℕ} (hk : k ≤ m) (hm : m ≤ N)
    (σ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m),
    stdSimplexCDeltaMap.{u} σ ≫ c m hm = c k (hk.trans hm)

/-- Base case `N = 0` of `CoherentContractionUpTo`. -/
noncomputable def coherentContractionUpToZero : CoherentContractionUpTo.{u} 0 where
  c k hk := eqToHom (by rw [Nat.le_zero.mp hk])
  c_zero := rfl
  c_comp {k m} hk hm σ := by
    have hm0 : m = 0 := Nat.le_zero.mp hm
    have hk0 : k = 0 := Nat.le_zero.mp (hk.trans hm)
    subst hm0 hk0
    have hσ : σ = 𝟙 (Henry.SemiSimplexCategory.mk 0) := hom_eq_id_of_end σ
    rw [hσ, stdSimplexCDeltaMap_id]
    rfl

lemma freeAlgKanUnit_comp_stdSimplexCDeltaMap_comp {k m n : ℕ}
    (σ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m)
    (f : stdSimplexCDelta.{u} m ⟶ stdSimplexCDelta.{u} n) :
    freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
      (stdSimplexCDeltaMap.{u} σ ≫ f).hom.hom =
    SemiSSet.stdSimplex.{u}.map σ ≫
      (freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) ≫
        f.hom.hom) :=
  congrArg (· ≫ f.hom.hom) (freeAlgKanUnit_comp_freeAlgKanMap (SemiSSet.stdSimplex.{u}.map σ))

/-- Given a coherent family of contractions up to `N`, the induced semi-simplicial map
`∂Δ_{N+1} ⟶ (Δ_0).X`. -/
noncomputable def boundaryContractionSemiSSet {N : ℕ} (prev : CoherentContractionUpTo.{u} N) :
    (SemiSSet.boundary.{u} (N + 1)).toFunctor ⟶ (stdSimplexCDelta.{u} 0).obj.X where
  app Δ := ↾(fun y =>
    let k := (unop Δ).obj.len
    have hk : k ≤ N := Nat.le_of_lt_succ ((mem_boundary_iff y.1).mp y.2)
    (freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
      (prev.c k hk).hom.hom).app Δ (ULift.up (𝟙 (unop Δ))))
  naturality {Δ Δ'} f := by
    ext y
    dsimp
    let k := (unop Δ).obj.len
    let k' := (unop Δ').obj.len
    have hk : k ≤ N := Nat.le_of_lt_succ ((mem_boundary_iff y.1).mp y.2)
    have hkk' : k' ≤ k := len_le_of_hom (unop f)
    have hcomp := congrArg (fun h : stdSimplexCDelta.{u} k' ⟶ stdSimplexCDelta.{u} 0 =>
        freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k')) ≫ h.hom.hom)
      (prev.c_comp hkk' hk (unop f))
    dsimp only at hcomp
    rw [freeAlgKanUnit_comp_stdSimplexCDeltaMap_comp] at hcomp
    let idΔ' : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k')).obj Δ' :=
      ULift.up (𝟙 (unop Δ'))
    let idΔ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)).obj Δ :=
      ULift.up (𝟙 (unop Δ))
    have happ := ConcreteCategory.congr_hom (congr_app hcomp Δ') idΔ'
    have hnat := ConcreteCategory.congr_hom
      ((freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
        (prev.c k hk).hom.hom).naturality f) idΔ
    dsimp [idΔ', idΔ] at happ hnat
    rw [← hnat, ← happ]
    congr 1

/-- The boundary map `∂Δ_{N+1} ⟶ Δ_0` in `CDelta` induced by `prev : CoherentContractionUpTo N`. -/
noncomputable def boundaryContractionCDelta {N : ℕ} (prev : CoherentContractionUpTo.{u} N) :
    boundaryCDelta.{u} (N + 1) ⟶ stdSimplexCDelta.{u} 0 :=
  ObjectProperty.homMk
    ((freeAlgKan_isFreeOn (SemiSSet.boundary.{u} (N + 1)).toFunctor
      (stdSimplexCDelta.{u} 0).obj (boundaryContractionSemiSSet.{u} prev)).choose)

lemma freeAlgKanUnit_comp_boundaryContractionCDelta {N : ℕ}
    (prev : CoherentContractionUpTo.{u} N) :
    freeAlgKanUnit (SemiSSet.boundary.{u} (N + 1)).toFunctor ≫
      (boundaryContractionCDelta.{u} prev).hom.hom =
      boundaryContractionSemiSSet.{u} prev :=
  (freeAlgKan_isFreeOn (SemiSSet.boundary.{u} (N + 1)).toFunctor
    (stdSimplexCDelta.{u} 0).obj (boundaryContractionSemiSSet.{u} prev)).choose_spec.1

/-- Chosen extension `Δ_{N+1} ⟶ Δ_0` of `boundaryContractionCDelta prev`. -/
noncomputable def succContractionCDelta {N : ℕ} (prev : CoherentContractionUpTo.{u} N) :
    stdSimplexCDelta.{u} (N + 1) ⟶ stdSimplexCDelta.{u} 0 :=
  (exists_extension_to_stdSimplexCDelta_zero
    (boundaryCDeltaInclusion.{u} (N + 1))
    (boundaryCDeltaInclusion_cofibration (N + 1))
    (boundaryContractionCDelta.{u} prev)).choose

lemma boundaryCDeltaInclusion_comp_succContractionCDelta {N : ℕ}
    (prev : CoherentContractionUpTo.{u} N) :
    boundaryCDeltaInclusion.{u} (N + 1) ≫ succContractionCDelta.{u} prev =
      boundaryContractionCDelta.{u} prev :=
  (exists_extension_to_stdSimplexCDelta_zero
    (boundaryCDeltaInclusion.{u} (N + 1))
    (boundaryCDeltaInclusion_cofibration (N + 1))
    (boundaryContractionCDelta.{u} prev)).choose_spec

lemma stdSimplexCDeltaMap_comp_succContractionCDelta {N : ℕ}
    (prev : CoherentContractionUpTo.{u} N) (k : ℕ) (hk : k ≤ N)
    (σ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk (N + 1)) :
    stdSimplexCDeltaMap.{u} σ ≫ succContractionCDelta.{u} prev = prev.c k hk := by
  let σ_bd : SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k) ⟶
      (SemiSSet.boundary.{u} (N + 1)).toFunctor :=
    { app Δ := ↾(fun x =>
        ⟨ULift.up (ULift.down x ≫ σ),
          (mem_boundary_iff _).mpr
            (lt_of_le_of_lt (len_le_of_hom (ULift.down x)) (Nat.lt_succ_of_le hk))⟩)
      naturality {Δ Δ'} f := by
        ext x
        apply Subtype.ext
        change ULift.up ((unop f ≫ ULift.down x) ≫ σ) = ULift.up (unop f ≫ ULift.down x ≫ σ)
        rw [Category.assoc] }
  have hσ_bd : σ_bd ≫ (SemiSSet.boundary.{u} (N + 1)).ι = SemiSSet.stdSimplex.{u}.map σ := by
    ext Δ x
    rfl
  have hmap : stdSimplexCDeltaMap.{u} σ =
      (ObjectProperty.homMk (freeAlgKanMap σ_bd) :
        stdSimplexCDelta.{u} k ⟶ boundaryCDelta.{u} (N + 1)) ≫
        boundaryCDeltaInclusion.{u} (N + 1) := by
    apply ObjectProperty.hom_ext
    change freeAlgKanMap (SemiSSet.stdSimplex.{u}.map σ) =
      freeAlgKanMap σ_bd ≫ freeAlgKanMap (SemiSSet.boundary.{u} (N + 1)).ι
    rw [← freeAlgKanMap_comp, hσ_bd]
  rw [hmap, Category.assoc, boundaryCDeltaInclusion_comp_succContractionCDelta]
  apply ObjectProperty.hom_ext
  apply freeAlgKan_hom_ext
  have ha := freeAlgKanUnit_comp_boundaryContractionCDelta.{u} prev
  have hunit := freeAlgKanUnit_comp_freeAlgKanMap σ_bd
  have hleft :
      freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
        ((ObjectProperty.homMk (freeAlgKanMap σ_bd) :
          stdSimplexCDelta.{u} k ⟶ boundaryCDelta.{u} (N + 1)) ≫
          boundaryContractionCDelta.{u} prev).hom.hom =
      σ_bd ≫ boundaryContractionSemiSSet.{u} prev :=
    (congrArg (· ≫ (boundaryContractionCDelta.{u} prev).hom.hom) hunit).trans
      (congrArg (σ_bd ≫ ·) ha)
  rw [hleft]
  ext Δ x
  let k' := (unop Δ).obj.len
  have hk'k : k' ≤ k := len_le_of_hom (ULift.down x)
  have hcomp := congrArg (fun h : stdSimplexCDelta.{u} k' ⟶ stdSimplexCDelta.{u} 0 =>
      freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k')) ≫ h.hom.hom)
    (prev.c_comp hk'k hk (ULift.down x))
  dsimp only at hcomp
  rw [freeAlgKanUnit_comp_stdSimplexCDeltaMap_comp] at hcomp
  let idΔ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k')).obj Δ :=
    ULift.up (𝟙 (unop Δ))
  have happ := ConcreteCategory.congr_hom (congr_app hcomp Δ) idΔ
  have hId : (SemiSSet.stdSimplex.{u}.map (ULift.down x)).app Δ idΔ = x :=
    ULift.ext _ _ (Category.id_comp (ULift.down x))
  exact happ.symm.trans (congrArg
    ((freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
      (prev.c k hk).hom.hom).app Δ) hId)

/-- Inductive step from `N` to `N + 1` for `CoherentContractionUpTo`. -/
noncomputable def coherentContractionUpToSucc {N : ℕ}
    (prev : CoherentContractionUpTo.{u} N) :
    CoherentContractionUpTo.{u} (N + 1) where
  c k hk :=
    if h : k ≤ N then prev.c k h
    else eqToHom (by rw [show k = N + 1 by omega]) ≫ succContractionCDelta.{u} prev
  c_zero := by
    simp only [Nat.zero_le, ↓reduceDIte, prev.c_zero]
  c_comp {k m} hk hm σ := by
    split_ifs with hmN hkN hkN'
    · exact prev.c_comp hk hmN σ
    · exfalso; exact hkN (hk.trans hmN)
    · have hm_eq : m = N + 1 := by omega
      subst hm_eq
      rw [eqToHom_refl, Category.id_comp]
      exact stdSimplexCDeltaMap_comp_succContractionCDelta prev k hkN' σ
    · have hm_eq : m = N + 1 := by omega
      have hk_eq : k = N + 1 := by omega
      subst hm_eq hk_eq
      have hσ : σ = 𝟙 (Henry.SemiSimplexCategory.mk (N + 1)) := hom_eq_id_of_end σ
      rw [hσ, stdSimplexCDeltaMap_id, eqToHom_refl, Category.id_comp, Category.id_comp]

/-- Coherent family of contractions up to `N` for every `N : ℕ`. -/
noncomputable def coherentContractionUpTo : ∀ N : ℕ, CoherentContractionUpTo.{u} N
  | 0 => coherentContractionUpToZero.{u}
  | N + 1 => coherentContractionUpToSucc.{u} (coherentContractionUpTo N)

lemma coherentContractionUpTo_agrees {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    (coherentContractionUpTo.{u} (N + 1)).c k (Nat.le_succ_of_le hk) =
      (coherentContractionUpTo.{u} N).c k hk := by
  dsimp [coherentContractionUpTo, coherentContractionUpToSucc]
  simp [hk]

lemma coherentContractionUpTo_eq_self (N k : ℕ) (hk : k ≤ N) :
    (coherentContractionUpTo.{u} N).c k hk =
      (coherentContractionUpTo.{u} k).c k (le_refl k) := by
  induction N with
  | zero =>
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    rfl
  | succ N ih =>
    rcases Nat.of_le_succ hk with hkN | rfl
    · rw [coherentContractionUpTo_agrees k hkN, ih hkN]
    · rfl

/-- The coherent contraction `Δ_n ⟶ Δ_0` in `CDelta`. -/
noncomputable def simplexContraction (n : ℕ) :
    stdSimplexCDelta.{u} n ⟶ stdSimplexCDelta.{u} 0 :=
  (coherentContractionUpTo.{u} n).c n (le_refl n)

@[simp]
lemma simplexContraction_zero :
    simplexContraction.{u} 0 = 𝟙 (stdSimplexCDelta.{u} 0) :=
  (coherentContractionUpTo.{u} 0).c_zero

@[simp]
lemma stdSimplexCDeltaMap_comp_simplexContraction {k n : ℕ}
    (σ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk n) :
    stdSimplexCDeltaMap.{u} σ ≫ simplexContraction.{u} n = simplexContraction.{u} k := by
  have hkn : k ≤ n := len_le_of_hom σ
  dsimp [simplexContraction]
  rw [(coherentContractionUpTo.{u} n).c_comp hkn (le_refl n) σ,
    coherentContractionUpTo_eq_self n k hkn]

/-- The 0-th vertex map `[0] ⟶ [n]` in `SemiSimplexCategory`. -/
def zeroVertexSimplex (n : ℕ) :
    Henry.SemiSimplexCategory.mk 0 ⟶ Henry.SemiSimplexCategory.mk n :=
  ⟨SimplexCategory.Hom.mk ⟨fun _ => 0, fun _ _ _ => le_refl 0⟩,
    SimplexCategory.mono_iff_injective.mpr (fun (a b : Fin 1) _ => Subsingleton.elim a b)⟩

theorem simplexContraction_weakEquivalence (n : ℕ) :
    weakEquivalences CDelta.{u} (simplexContraction.{u} n) := by
  apply cDelta_weakEquivalence_of_comp_left
    (stdSimplexCDeltaMap.{u} (zeroVertexSimplex n))
    (simplexContraction.{u} n)
    (stdSimplexCDeltaMap_weakEquivalence (zeroVertexSimplex n))
  rw [stdSimplexCDeltaMap_comp_simplexContraction, simplexContraction_zero]
  exact cDelta_weakEquivalence_id _

end HomotopyHypothesis.Cylinder.SimplicialCategory
