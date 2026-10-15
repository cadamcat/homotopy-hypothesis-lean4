import Mathlib.Tactic
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.BarycentricCell.Core
import HomotopyHypothesis.Approximation.DerivedPrismTop.DerivedPositions
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Code
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Rank
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
universe u

open Convexity

namespace HomotopyHypothesis.Approximation.BarycentricCell

open HomotopyHypothesis.Approximation.Topological
open HomotopyHypothesis.Approximation.DerivedPrismTop
open HomotopyHypothesis.Approximation.Topological.PV

/-- Coordinates of an affine combination in a standard simplex. -/
theorem affineMapMk_weights_apply {n : ℕ} {M : Type u}
    (p : Fin (n + 1) → StdSimplex ℝ M) (x : StdSimplex ℝ (Fin (n + 1))) (q : M) :
    (StdSimplex.affineMapMk (R := ℝ) p x).weights q =
      ∑ i, x.weights i * (p i).weights q := by
  classical
  have h := (StdSimplex.isAffineMap_weights ℝ M).map_iConvexComb x p
  change (StdSimplex.affineMapMk (R := ℝ) p x).weights =
    x.iConvexComb (fun i => (p i).weights) at h
  rw [iConvexComb_eq_sum, Finsupp.sum_fintype _ _ (by simp)] at h
  simpa using congrArg (fun w : M →₀ ℝ => w q) h

/-- A face barycentre has equal positive coordinates on that face and zero elsewhere. -/
theorem barycentricPoint_weights {k : ℕ} (S : Finset (Fin (k + 1)))
    (hS : S.Nonempty) :
    (barycentricPoint S hS).weights =
      ∑ i ∈ S, Finsupp.single i ((S.card : ℝ)⁻¹) := by
  ext i
  simp [barycentricPoint, Finsupp.equivFunOnFinite,
    Finset.centroidWeightsIndicator, Finset.centroidWeights, Set.indicator,
    Finsupp.single_apply]

theorem barycentricPoint_weight_apply {k : ℕ} (S : Finset (Fin (k + 1)))
    (hS : S.Nonempty) (v : Fin (k + 1)) :
    (barycentricPoint S hS).weights v =
      if v ∈ S then (S.card : ℝ)⁻¹ else 0 := by
  rw [barycentricPoint_weights S hS]
  simp [Finsupp.single_apply]

/-- The nonzero coordinates of a face barycentre are exactly its face. -/
theorem barycentricPoint_weights_ne_zero_iff {k : ℕ}
    (S : Finset (Fin (k + 1))) (hS : S.Nonempty) (i : Fin (k + 1)) :
    (barycentricPoint S hS).weights i ≠ 0 ↔ i ∈ S := by
  classical
  rw [barycentricPoint_weights S hS]
  have hcard : (S.card : ℝ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (Finset.card_pos.mpr hS).ne'
  simp [Finsupp.single_apply, hcard]

noncomputable def faceMixture {k n : ℕ}
    (F : Fin (n + 1) → Finset (Fin (k + 1)))
    (hF : ∀ i, (F i).Nonempty) (p : StdSimplex ℝ (Fin (n + 1))) :
    StdSimplex ℝ (Fin (k + 1)) :=
  StdSimplex.affineMapMk (R := ℝ) (fun i => barycentricPoint (F i) (hF i)) p

theorem faceMixture_weight_apply {k n : ℕ}
    (F : Fin (n + 1) → Finset (Fin (k + 1))) (hF : ∀ i, (F i).Nonempty)
    (p : StdSimplex ℝ (Fin (n + 1))) (v : Fin (k + 1)) :
    (faceMixture F hF p).weights v =
      ∑ i, p.weights i * (if v ∈ F i then ((F i).card : ℝ)⁻¹ else 0) := by
  rw [faceMixture, affineMapMk_weights_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [barycentricPoint_weight_apply]

theorem faceMixture_map {k l n : ℕ} (e : Fin (k + 1) → Fin (l + 1))
    (he : Function.Injective e) (F : Fin (n + 1) → Finset (Fin (k + 1)))
    (hF : ∀ i, (F i).Nonempty) (p : StdSimplex ℝ (Fin (n + 1))) :
    StdSimplex.map e (faceMixture F hF p) =
      faceMixture (fun i => (F i).image e) (fun i => (hF i).image e) p := by
  change (StdSimplex.affineMap (R := ℝ) e)
      (StdSimplex.affineMapMk (R := ℝ) (fun i => barycentricPoint (F i) (hF i)) p) = _
  calc
    _ = StdSimplex.affineMapMk (R := ℝ)
        (fun i => (barycentricPoint (F i) (hF i)).map e) p :=
      congrArg (fun f => f p)
        (StdSimplex.comp_affineMapMk (StdSimplex.affineMap (R := ℝ) e)
          (fun i => barycentricPoint (F i) (hF i)))
    _ = _ := by
      apply congrArg (fun f : Fin (n + 1) → StdSimplex ℝ (Fin (l + 1)) =>
        StdSimplex.affineMapMk (R := ℝ) f p)
      funext i
      exact barycentricPoint_map e he (F i) (hF i)

/-- The barycentre of the full simplex is the barycentre of its full face. -/
theorem barycentricPoint_univ {k : ℕ} :
    barycentricPoint (Finset.univ : Finset (Fin (k + 1))) (by simp) =
      StdSimplex.barycenter (K := ℝ) (M := Fin (k + 1)) := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro i
  rw [barycentricPoint_weight_apply, StdSimplex.weights_barycenter_apply]
  simp only [Finset.mem_univ, if_true, Finset.card_univ, Fintype.card_fin]

/-- Add a full-face barycentre as the last term of a face mixture. -/
noncomputable def appendWeight {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (hc' : c < 1)
    (p : StdSimplex ℝ (Fin (n + 1))) : StdSimplex ℝ (Fin (n + 2)) :=
  convexCombPair c (1 - c) hc (sub_pos.mpr hc').le (by ring)
    (StdSimplex.single (Fin.last (n + 1))) (StdSimplex.map Fin.castSucc p)

def snocFaces {k n : ℕ} (F : Fin (n + 1) → Finset (Fin (k + 1)))
    (S : Finset (Fin (k + 1))) : Fin (n + 2) → Finset (Fin (k + 1)) :=
  Fin.lastCases S F

@[simp] theorem snocFaces_last {k n : ℕ}
    (F : Fin (n + 1) → Finset (Fin (k + 1))) (S : Finset (Fin (k + 1))) :
    snocFaces F S (Fin.last (n + 1)) = S := by
  simp [snocFaces]

@[simp] theorem snocFaces_castSucc {k n : ℕ}
    (F : Fin (n + 1) → Finset (Fin (k + 1))) (S : Finset (Fin (k + 1)))
    (i : Fin (n + 1)) : snocFaces F S i.castSucc = F i := by
  simp [snocFaces]

theorem appendWeight_last {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (hc' : c < 1)
    (p : StdSimplex ℝ (Fin (n + 1))) :
    (appendWeight c hc hc' p).weights (Fin.last (n + 1)) = c := by
  rw [appendWeight, StdSimplex.weights_convexCombPair]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    StdSimplex.weights_single]
  have hn : Fin.last (n + 1) ∉ Set.range (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) := by
    rintro ⟨i, hi⟩
    exact (Fin.castSucc_ne_last i) hi
  rw [StdSimplex.weights_map, Finsupp.mapDomain_of_notMem_range _ _ hn]
  simp

theorem appendWeight_castSucc {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (hc' : c < 1)
    (p : StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    (appendWeight c hc hc' p).weights i.castSucc = (1 - c) * p.weights i := by
  rw [appendWeight, StdSimplex.weights_convexCombPair]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    StdSimplex.weights_single, Finsupp.single_eq_of_ne (Fin.castSucc_ne_last i),
    mul_zero, zero_add]
  rw [StdSimplex.weights_map,
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective (n + 1))]

theorem appendWeight_ne_zero {n : ℕ} (c : ℝ) (hc : 0 < c) (hc' : c < 1)
    (p : StdSimplex ℝ (Fin (n + 1))) (hp : ∀ i, p.weights i ≠ 0) :
    ∀ i, (appendWeight c hc.le hc' p).weights i ≠ 0 := by
  intro i
  induction i using Fin.lastCases with
  | last => rw [appendWeight_last]; exact ne_of_gt hc
  | cast j =>
    rw [appendWeight_castSucc]
    exact mul_ne_zero (ne_of_gt (sub_pos.mpr hc')) (hp j)

theorem last_weight_lt_one_of_nonzero {n : ℕ} (t : StdSimplex ℝ (Fin (n + 2)))
    (ht : ∀ i, t.weights i ≠ 0) : t.weights (Fin.last (n + 1)) < 1 := by
  have hsum := t.total_of_fintype
  rw [Fin.sum_univ_castSucc] at hsum
  have hle : t.weights ((0 : Fin (n + 1)).castSucc) ≤
      ∑ i : Fin (n + 1), t.weights i.castSucc :=
    Finset.single_le_sum (fun (i : Fin (n + 1)) _ => t.weights_nonneg i.castSucc)
      (Finset.mem_univ _)
  have hpos : 0 < t.weights ((0 : Fin (n + 1)).castSucc) :=
    lt_of_le_of_ne (t.weights_nonneg _) (Ne.symm (ht _))
  linarith

noncomputable def normalizedPrefix {n : ℕ} (t : StdSimplex ℝ (Fin (n + 2)))
    (hc : t.weights (Fin.last (n + 1)) < 1) : StdSimplex ℝ (Fin (n + 1)) where
  weights := Finsupp.equivFunOnFinite.symm
    (fun i => t.weights i.castSucc / (1 - t.weights (Fin.last (n + 1))))
  nonneg := by
    intro i
    change 0 ≤ t.weights i.castSucc / (1 - t.weights (Fin.last (n + 1)))
    exact div_nonneg (t.weights_nonneg _) (sub_pos.mpr hc).le
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ i : Fin (n + 1),
      t.weights i.castSucc / (1 - t.weights (Fin.last (n + 1)))) = 1
    rw [← Finset.sum_div]
    have hsum := t.total_of_fintype
    rw [Fin.sum_univ_castSucc] at hsum
    have he : (∑ i : Fin (n + 1), t.weights i.castSucc) =
        1 - t.weights (Fin.last (n + 1)) := by linarith
    rw [he, div_self (ne_of_gt (sub_pos.mpr hc))]

theorem normalizedPrefix_weights {n : ℕ} (t : StdSimplex ℝ (Fin (n + 2)))
    (hc : t.weights (Fin.last (n + 1)) < 1) (i : Fin (n + 1)) :
    (normalizedPrefix t hc).weights i =
      t.weights i.castSucc / (1 - t.weights (Fin.last (n + 1))) := rfl

theorem normalizedPrefix_weights_ne_zero {n : ℕ} (t : StdSimplex ℝ (Fin (n + 2)))
    (hc : t.weights (Fin.last (n + 1)) < 1) (ht : ∀ i, t.weights i ≠ 0) :
    ∀ i, (normalizedPrefix t hc).weights i ≠ 0 := by
  intro i
  exact div_ne_zero (ht i.castSucc) (ne_of_gt (sub_pos.mpr hc))

theorem normalizedPrefix_decomposition {n : ℕ} (t : StdSimplex ℝ (Fin (n + 2)))
    (hc : t.weights (Fin.last (n + 1)) < 1) :
    t = convexCombPair (t.weights (Fin.last (n + 1)))
      (1 - t.weights (Fin.last (n + 1))) (t.weights_nonneg _)
      (sub_pos.mpr hc).le (by ring) (StdSimplex.single (Fin.last (n + 1)))
      (StdSimplex.map Fin.castSucc (normalizedPrefix t hc)) := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro i
  rw [StdSimplex.weights_convexCombPair]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  induction i using Fin.lastCases with
  | last =>
    have hn : Fin.last (n + 1) ∉ Set.range (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) := by
      rintro ⟨j, hj⟩
      exact (Fin.castSucc_ne_last j) hj
    rw [StdSimplex.weights_map, Finsupp.mapDomain_of_notMem_range _ _ hn]
    simp
  | cast i =>
    rw [StdSimplex.weights_map,
      Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective (n + 1))]
    simp only [StdSimplex.weights_single, Finsupp.single_eq_of_ne (Fin.castSucc_ne_last i),
      mul_zero, zero_add, normalizedPrefix_weights]
    exact (mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr hc))).symm

theorem normalizedPrefix_appendWeight {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (hc' : c < 1)
    (p : StdSimplex ℝ (Fin (n + 1))) :
    normalizedPrefix (appendWeight c hc hc' p)
      (by rw [appendWeight_last]; exact hc') = p := by
  have hden : 1 - c ≠ 0 := ne_of_gt (sub_pos.mpr hc')
  apply StdSimplex.ext
  apply Finsupp.ext
  intro i
  rw [normalizedPrefix_weights, appendWeight_castSucc, appendWeight_last]
  field_simp [hden]

theorem faceMixture_prefix_split {k n : ℕ}
    (F : Fin (n + 2) → Finset (Fin (k + 1))) (hF : ∀ i, (F i).Nonempty)
    (p : StdSimplex ℝ (Fin (n + 2))) (hc : p.weights (Fin.last (n + 1)) < 1) :
    faceMixture F hF p =
      convexCombPair (p.weights (Fin.last (n + 1)))
        (1 - p.weights (Fin.last (n + 1))) (p.weights_nonneg _)
        (sub_pos.mpr hc).le (by ring)
        (barycentricPoint (F (Fin.last (n + 1))) (hF _))
        (faceMixture (fun i => F i.castSucc) (fun i => hF i.castSucc)
          (normalizedPrefix p hc)) := by
  let q : Fin (n + 2) → StdSimplex ℝ (Fin (k + 1)) :=
    fun i => barycentricPoint (F i) (hF i)
  have hcomp :
      (StdSimplex.affineMapMk (R := ℝ) q).comp
        (StdSimplex.affineMap (R := ℝ) (Fin.castSucc : Fin (n + 1) → Fin (n + 2))) =
      StdSimplex.affineMapMk (R := ℝ) (fun i => q (Fin.castSucc i)) := by
    apply StdSimplex.affineMap_ext
    intro i
    simp
  change StdSimplex.affineMapMk (R := ℝ) q p = _
  conv_lhs => rw [normalizedPrefix_decomposition p hc]
  rw [(StdSimplex.affineMapMk (R := ℝ) q).isAffineMap.map_convexCombPair]
  congr 1
  · simp [q, StdSimplex.affineMapMk_single]
  · change (StdSimplex.affineMapMk (R := ℝ) q)
        (StdSimplex.map Fin.castSucc (normalizedPrefix p hc)) = _
    change ((StdSimplex.affineMapMk (R := ℝ) q).comp
        (StdSimplex.affineMap (R := ℝ) Fin.castSucc)) (normalizedPrefix p hc) = _
    rw [hcomp]
    rfl

private theorem pvMid_card_le {k : ℕ} {S T : Finset (Fin (k + 1))}
    (h : PV.mid S ≤ PV.mid T) : S.card ≤ T.card := by
  change PV.rank (PV.mid S) ≤ PV.rank (PV.mid T) at h
  simp only [PV.rank, Prod.Lex.toLex_le_toLex] at h
  omega

private theorem sdSimplex_mid {k n : ℕ} (s : (sdComplex k).Simplex n)
    (i : Fin (n + 1)) :
    ∃ S, s.1 i = PV.mid S ∧ S.Nonempty := by
  classical
  cases hv : s.1 i with
  | top j =>
    have hi : PV.top j ∈ Finset.univ.image s.1 :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hv⟩
    exact (s.2.2.2 j hi).elim
  | mid S =>
    have hi : PV.mid S ∈ Finset.univ.image s.1 :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hv⟩
    exact ⟨S, rfl, (s.2.2.1).1 S hi⟩

noncomputable def sdFace {k n : ℕ} (s : (sdComplex k).Simplex n)
    (i : Fin (n + 1)) : Finset (Fin (k + 1)) :=
  Classical.choose (sdSimplex_mid s i)

theorem sdFace_spec {k n : ℕ} (s : (sdComplex k).Simplex n)
    (i : Fin (n + 1)) :
    s.1 i = PV.mid (sdFace s i) ∧ (sdFace s i).Nonempty :=
  Classical.choose_spec (sdSimplex_mid s i)

theorem sdFace_strictMono {k n : ℕ} (s : (sdComplex k).Simplex n)
    {i j : Fin (n + 1)} (hij : i < j) : sdFace s i ⊂ sdFace s j := by
  have hi := sdFace_spec s i
  have hj := sdFace_spec s j
  have hpv : PV.mid (sdFace s i) < PV.mid (sdFace s j) := by
    rw [← hi.1, ← hj.1]
    exact s.2.1 hij
  have hMi : PV.mid (sdFace s i) ∈ Finset.univ.image s.1 :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.1⟩
  have hMj : PV.mid (sdFace s j) ∈ Finset.univ.image s.1 :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.1⟩
  have hcomp := (s.2.2.1).2.1 (sdFace s i) (sdFace s j)
    hMi hMj
  rcases hcomp with hsub | hsub
  · exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
      intro heq
      rw [heq] at hpv
      exact (lt_irrefl _ hpv).elim⟩
  · have hcard := pvMid_card_le (le_of_lt hpv)
    have heq : sdFace s i = sdFace s j :=
      (Finset.eq_of_subset_of_card_le hsub (by simpa using hcard)).symm
    rw [heq] at hpv
    exact (lt_irrefl _ hpv).elim

/-- Evaluation of a derived-cylinder cell map is its affine map on vertices. -/
theorem dprismCellMap_apply {k n : ℕ} (σ : (dprismComplex k).Simplex n)
    (x : StdSimplex ℝ (Fin (n + 1))) :
    (dprismCellMap σ).hom (ULift.up x) =
      ULift.up (StdSimplex.affineMapMk (R := ℝ) (dprismPosition ∘ σ.1) x) := by
  rfl

/-- The affine output of a derived simplex is the mixture of its face barycentres. -/
theorem dprismCellMap_weights_apply {k n : ℕ} (s : (sdComplex k).Simplex n)
    (x : StdSimplex ℝ (Fin (n + 1))) (v : Fin (k + 1)) :
    ((dprismCellMap ⟨s.1, s.2.1, s.2.2.1⟩).hom (ULift.up x)).down.weights v =
      ∑ i, x.weights i * (barycentricPoint (sdFace s i) (sdFace_spec s i).2).weights v := by
  have hpos (i : Fin (n + 1)) :
      dprismPosition (s.1 i) =
        barycentricPoint (sdFace s i) (sdFace_spec s i).2 := by
    calc
      dprismPosition (s.1 i) = dprismPosition (PV.mid (sdFace s i)) :=
        congrArg dprismPosition (sdFace_spec s i).1
      _ = barycentricPoint (sdFace s i) (sdFace_spec s i).2 := by
        simp [dprismPosition, (sdFace_spec s i).2]
  change (StdSimplex.affineMapMk (R := ℝ) (dprismPosition ∘ s.1) x).weights v = _
  rw [affineMapMk_weights_apply]
  dsimp only [Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hpos i]

theorem dprismCellMap_weight_formula {k n : ℕ} (s : (sdComplex k).Simplex n)
    (x : StdSimplex ℝ (Fin (n + 1))) (v : Fin (k + 1)) :
    ((dprismCellMap ⟨s.1, s.2.1, s.2.2.1⟩).hom (ULift.up x)).down.weights v =
      ∑ i, x.weights i *
        (if v ∈ sdFace s i then ((sdFace s i).card : ℝ)⁻¹ else 0) := by
  rw [dprismCellMap_weights_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [barycentricPoint_weight_apply]

end HomotopyHypothesis.Approximation.BarycentricCell
