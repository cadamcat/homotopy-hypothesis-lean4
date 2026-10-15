import Mathlib.Tactic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteRealization.Proofs
import HomotopyHypothesis.Approximation.BarycentricCell.Coordinates
import HomotopyHypothesis.Approximation.BarycentricCell.Core
import HomotopyHypothesis.Approximation.BarycentricCell.Existence
import HomotopyHypothesis.Approximation.BarycentricCell.Mixtures
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellSingular
import HomotopyHypothesis.Approximation.DerivedPrismTop.DerivedPositions
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprism
universe u

open CategoryTheory Limits Opposite Convexity

namespace HomotopyHypothesis.Approximation.BarycentricCell

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological
open HomotopyHypothesis.Approximation.DerivedPrismTop

private theorem simplexChar_naturality {K : SemiSSet.{u}} {m n : ℕ}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n)
    (x : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ K) :
    simplexChar (Henry.SemiSSet.stdSimplex.map θ ≫ x) =
      toTop.map θ ≫ simplexChar x := by
  unfold simplexChar realization
  rw [Functor.map_comp]
  simp only [← Category.assoc]
  simpa only [Functor.comp_map] using congrArg
    (fun t => t ≫ (Henry.SemiSSet.stdSimplex.{u}.leftKanExtension toTop.{u}).map x)
    ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).naturality θ).symm

private def faceInclusion {m n : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) :
    Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n :=
  ⟨SimplexCategory.Hom.mk e.toOrderHom, by
    change Mono (show SimplexCategory.mk m ⟶ SimplexCategory.mk n from
      SimplexCategory.Hom.mk e.toOrderHom)
    rw [SimplexCategory.mono_iff_injective]
    exact e.injective⟩

private theorem exists_nonzero_face {n : ℕ} (t : StdSimplex ℝ (Fin (n + 1))) :
    ∃ (m : ℕ) (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n)
      (p : StdSimplex ℝ (Fin (m + 1))),
      StdSimplex.map θ.hom.toOrderHom p = t ∧ ∀ i, p.weights i ≠ 0 := by
  classical
  let s := t.weights.support
  have hpos : 0 < s.card := Finset.card_pos.mpr t.support_weights_nonempty
  have hcard : s.card = (s.card - 1) + 1 := by omega
  let e : Fin ((s.card - 1) + 1) ↪o Fin (n + 1) := s.orderEmbOfFin hcard
  have he : Set.range e = (s : Set (Fin (n + 1))) := Finset.range_orderEmbOfFin s hcard
  obtain ⟨p, hp⟩ := (StdSimplex.mem_range_map_iff e t).mpr (by
    intro i hi
    by_contra hne
    apply hi
    rw [he]
    exact Finsupp.mem_support_iff.mpr hne)
  let θ : Henry.SemiSimplexCategory.mk (s.card - 1) ⟶ Henry.SemiSimplexCategory.mk n :=
    faceInclusion e
  have hp' : StdSimplex.map θ.hom.toOrderHom p = t := by
    simpa [θ, faceInclusion] using hp
  refine ⟨s.card - 1, θ, p, hp', ?_⟩
  intro i hi
  have hmem : e i ∈ s := s.orderEmbOfFin_mem hcard i
  have hne := Finsupp.mem_support_iff.mp hmem
  apply hne
  rw [← hp, StdSimplex.weights_map,
    Finsupp.mapDomain_apply_of_injective e.injective, hi]

private theorem exists_simplexChar_nonzero_rep {K : SemiSSet.{u}}
    (z : realization.obj K) :
    ∃ (n : ℕ) (x : K.obj (op (Henry.SemiSimplexCategory.mk n)))
      (p : StdSimplex ℝ (Fin (n + 1))),
      (∀ i, p.weights i ≠ 0) ∧
        (simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up p) = z := by
  obtain ⟨n, y, t, ht⟩ := HomotopyHypothesis.Approximation.FiniteRealization.exists_simplexChar_rep z
  change ULift.{u} (StdSimplex ℝ (Fin (n + 1))) at t
  rcases t with ⟨t⟩
  obtain ⟨m, θ, p, hp, hnz⟩ := exists_nonzero_face t
  refine ⟨m, K.map θ.op (uliftYonedaEquiv y), p, hnz, ?_⟩
  rw [uliftYonedaEquiv_symm_map, Equiv.symm_apply_apply, simplexChar_naturality]
  change (simplexChar y).hom
    (ULift.up (StdSimplex.map θ.hom.toOrderHom p)) = z
  have hpUL : ULift.up (StdSimplex.map θ.hom.toOrderHom p) = ULift.up t :=
    congrArg ULift.up hp
  calc
    (simplexChar y).hom (ULift.up (StdSimplex.map θ.hom.toOrderHom p)) =
        (simplexChar y).hom (ULift.up t) := congrArg (fun x => (simplexChar y).hom x) hpUL
    _ = z := ht

theorem exists_sd_nonzero_rep {k : ℕ}
    (z : realization.obj ((sdComplex k).toSemiSSet.{u})) :
    ∃ n : ℕ, ∃ s : (sdComplex k).Simplex n, ∃ p : StdSimplex ℝ (Fin (n + 1)),
      (∀ i, p.weights i ≠ 0) ∧
        (simplexChar (Complex.simplexMap.{u} (sdComplex k) s.1 s.2.1 s.2.2)).hom
          (ULift.up p) = z := by
  obtain ⟨n, x, p, hp, hx⟩ := exists_simplexChar_nonzero_rep z
  let s : (sdComplex k).Simplex n := x.down
  refine ⟨n, s, p, hp, ?_⟩
  have heq : Complex.simplexMap.{u} (sdComplex k) s.1 s.2.1 s.2.2 =
      uliftYonedaEquiv.symm x := by
    apply uliftYonedaEquiv.injective
    rfl
  rw [heq]
  exact hx

noncomputable def baryCellMap (k : ℕ) :
    realization.obj ((sdComplex k).toSemiSSet.{u}) ⟶
      toTop.{u}.obj (Henry.SemiSimplexCategory.mk k) :=
  realization.map (sdToDprism k).toSemiSSet ≫ dprismCellProjection.{u} k

theorem baryCellMap_chain_chart {k n : ℕ} (C : FaceChain k n)
    (p : StdSimplex ℝ (Fin (n + 1))) :
    (baryCellMap.{u} k).hom
        ((simplexChar (Complex.simplexMap.{u} (sdComplex k)
          (C.toSdSimplex).1 (C.toSdSimplex).2.1 (C.toSdSimplex).2.2)).hom (ULift.up p)) =
      ULift.up (C.mixture p) := by
  classical
  let s := C.toSdSimplex
  have hcell := baryCell_on_simplex s
  change simplexChar (Complex.simplexMap.{u} (sdComplex k) s.1 s.2.1 s.2.2) ≫
      baryCellMap.{u} k = dprismCellMap ⟨s.1, s.2.1, s.2.2.1⟩ at hcell
  have hout :
      (dprismCellMap ⟨s.1, s.2.1, s.2.2.1⟩).hom (ULift.up p) =
        ULift.up (C.mixture p) := by
    change ULift.up
        (StdSimplex.affineMapMk (R := ℝ) (dprismPosition ∘ s.1) p) =
      ULift.up (C.mixture p)
    apply congrArg ULift.up
    apply StdSimplex.ext
    apply Finsupp.ext
    intro v
    rw [affineMapMk_weights_apply, FaceChain.mixture, faceMixture_weight_apply]
    apply Finset.sum_congr rfl
    intro i hi
    have hS : sdFace s i = C.faces i := FaceChain.sdFace_toSdSimplex C i
    have hbary : barycentricPoint (sdFace s i) (sdFace_spec s i).2 =
        barycentricPoint (C.faces i) (C.nonempty i) := by
      apply StdSimplex.ext
      apply Finsupp.ext
      intro w
      rw [barycentricPoint_weight_apply, barycentricPoint_weight_apply]
      simp [hS]
    have hpos : dprismPosition (s.1 i) = barycentricPoint (C.faces i) (C.nonempty i) := by
      calc
        dprismPosition (s.1 i) = barycentricPoint (sdFace s i) (sdFace_spec s i).2 := by
          calc
            dprismPosition (s.1 i) = dprismPosition (PV.mid (sdFace s i)) :=
              congrArg dprismPosition (sdFace_spec s i).1
            _ = _ := by simp [dprismPosition, (sdFace_spec s i).2]
        _ = _ := hbary
    rw [Function.comp_apply, hpos, barycentricPoint_weight_apply]
  have hpoint := congrArg (fun f => f.hom (ULift.up p)) hcell
  have hpoint' :
      ((baryCellMap.{u} k).hom.comp
        (simplexChar (Complex.simplexMap.{u} (sdComplex k) s.1 s.2.1 s.2.2)).hom)
        (ULift.up p) = (dprismCellMap ⟨s.1, s.2.1, s.2.2.1⟩).hom (ULift.up p) := by
    change ((baryCellMap.{u} k).hom.comp
      (simplexChar (Complex.simplexMap.{u} (sdComplex k) s.1 s.2.1 s.2.2)).hom)
      (ULift.up p) = _ at hpoint
    exact hpoint
  change ((baryCellMap.{u} k).hom.comp
      (simplexChar (Complex.simplexMap.{u} (sdComplex k) s.1 s.2.1 s.2.2)).hom)
      (ULift.up p) = ULift.up (C.mixture p)
  exact Eq.trans hpoint' hout

theorem baryCellMap_simplex_chart {k n : ℕ} (s : (sdComplex k).Simplex n)
    (p : StdSimplex ℝ (Fin (n + 1))) :
    (baryCellMap.{u} k).hom
        ((simplexChar (Complex.simplexMap.{u} (sdComplex k) s.1 s.2.1 s.2.2)).hom
          (ULift.up p)) =
      ULift.up ((FaceChain.ofSdSimplex s).mixture p) := by
  let C := FaceChain.ofSdSimplex s
  have hcan : C.toSdSimplex = s := FaceChain.toSdSimplex_ofSdSimplex s
  have h := baryCellMap_chain_chart C p
  rw [hcan] at h
  exact h

theorem baryCellMap_injective (k : ℕ) : Function.Injective (baryCellMap.{u} k).hom := by
  intro x y hxy
  obtain ⟨n, s, p, hp, hx⟩ := exists_sd_nonzero_rep (k := k) x
  obtain ⟨m, t, q, hq, hy⟩ := exists_sd_nonzero_rep (k := k) y
  let A := FaceChain.ofSdSimplex s
  let B := FaceChain.ofSdSimplex t
  have hAx : (baryCellMap.{u} k).hom x = ULift.up (A.mixture p) := by
    rw [← hx]
    exact baryCellMap_simplex_chart s p
  have hBy : (baryCellMap.{u} k).hom y = ULift.up (B.mixture q) := by
    rw [← hy]
    exact baryCellMap_simplex_chart t q
  have hmixUL : ULift.up (A.mixture p) = ULift.up (B.mixture q) := by
    exact Eq.trans hAx.symm (Eq.trans hxy hBy)
  have hmix : A.mixture p = B.mixture q := ULift.up.inj hmixUL
  obtain ⟨hdim, hAB, hpq⟩ := FaceChain.eq_of_mixture_eq A B p q hp hq hmix
  subst m
  have hA : A = B := eq_of_heq hAB
  have hpq' : p = q := eq_of_heq hpq
  have hst : s = t := by
    calc
      s = A.toSdSimplex := (FaceChain.toSdSimplex_ofSdSimplex s).symm
      _ = B.toSdSimplex := congrArg FaceChain.toSdSimplex hA
      _ = t := FaceChain.toSdSimplex_ofSdSimplex t
  subst t
  subst q
  exact hx.symm.trans hy

theorem baryCellMap_surjective (k : ℕ) : Function.Surjective (baryCellMap.{u} k).hom := by
  intro y
  rcases y with ⟨t⟩
  obtain ⟨n, C, p, hp, hmix⟩ := exists_faceChain_mixture t
  let s := C.toSdSimplex
  refine ⟨(simplexChar (Complex.simplexMap.{u} (sdComplex k) s.1 s.2.1 s.2.2)).hom
    (ULift.up p), ?_⟩
  change (baryCellMap.{u} k).hom
      ((simplexChar (Complex.simplexMap.{u} (sdComplex k) s.1 s.2.1 s.2.2)).hom
        (ULift.up p)) = ULift.up t
  calc
    _ = ULift.up (C.mixture p) := baryCellMap_chain_chart C p
    _ = ULift.up t := congrArg ULift.up hmix

theorem baryCell_bijective_proof (k : ℕ) :
    Function.Bijective (realization.map (sdToDprism k).toSemiSSet.{u} ≫
      dprismCellProjection.{u} k).hom := by
  change Function.Bijective (baryCellMap.{u} k).hom
  exact ⟨baryCellMap_injective k, baryCellMap_surjective k⟩

#print axioms baryCell_bijective_proof
#print axioms HomotopyHypothesis.Approximation.Topological.PV.map_strictMonoOn
#print axioms HomotopyHypothesis.Approximation.Topological.PV.map_S

end HomotopyHypothesis.Approximation.BarycentricCell
