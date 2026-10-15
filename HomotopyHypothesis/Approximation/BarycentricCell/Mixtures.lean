import HomotopyHypothesis.Approximation.BarycentricCell.Coordinates
import HomotopyHypothesis.Approximation.DerivedPrismTop.DerivedPositions
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Code
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
universe u

open Convexity
open HomotopyHypothesis.Approximation.DerivedPrismTop


namespace HomotopyHypothesis.Approximation.BarycentricCell

open HomotopyHypothesis.Approximation.Topological
open HomotopyHypothesis.Approximation.Topological.PV

/-- A strict chain of nonempty faces of a finite simplex. -/
structure FaceChain (k n : ℕ) where
  faces : Fin (n + 1) → Finset (Fin (k + 1))
  nonempty : ∀ i, (faces i).Nonempty
  strict : ∀ {i j}, i < j → faces i ⊂ faces j

namespace FaceChain

theorem face_subset_of_le {k n : ℕ} (C : FaceChain k n) {i j : Fin (n + 1)}
    (hij : i ≤ j) : C.faces i ⊆ C.faces j := by
  by_cases h : i = j
  · simpa [h]
  · exact (C.strict (lt_of_le_of_ne hij h)).subset

private theorem pv_mid_lt_of_card_lt {k : ℕ} {S T : Finset (Fin (k + 1))}
    (h : S.card < T.card) : PV.mid S < PV.mid T := by
  change PV.rank (PV.mid S) < PV.rank (PV.mid T)
  exact Prod.Lex.toLex_lt_toLex.2
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inl h)⟩)

/-- A strict face chain is a simplex in the derived complex. -/
noncomputable def toSdSimplex {k n : ℕ} (C : FaceChain k n) :
    (sdComplex k).Simplex n := by
  let f : Fin (n + 1) → PV k := fun i => PV.mid (C.faces i)
  have hf : StrictMono f := by
    intro i j hij
    exact pv_mid_lt_of_card_lt (Finset.card_lt_card (C.strict hij))
  have hS : (sdComplex k).S (Finset.univ.image f) := by
    refine ⟨⟨?_, ⟨?_, ?_⟩⟩, ?_⟩
    · intro S hS
      rcases Finset.mem_image.mp hS with ⟨i, hi, hEq⟩
      have hfaces : C.faces i = S := PV.mid.inj hEq
      simpa [hfaces] using C.nonempty i
    · intro S T hS hT
      rcases Finset.mem_image.mp hS with ⟨i, hi, hSi⟩
      rcases Finset.mem_image.mp hT with ⟨j, hj, hTj⟩
      have hfacesI : C.faces i = S := PV.mid.inj hSi
      have hfacesJ : C.faces j = T := PV.mid.inj hTj
      rcases le_total i j with h | h
      · left
        rw [← hfacesI, ← hfacesJ]
        exact C.face_subset_of_le h
      · right
        rw [← hfacesI, ← hfacesJ]
        exact C.face_subset_of_le h
    · intro i S htop hmid
      rcases Finset.mem_image.mp htop with ⟨j, hj, hEq⟩
      cases hEq
    · intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, hEq⟩
      cases hEq
  exact ⟨f, hf, hS⟩

theorem sdFace_toSdSimplex {k n : ℕ} (C : FaceChain k n) (i : Fin (n + 1)) :
    sdFace (C.toSdSimplex) i = C.faces i := by
  exact (PV.mid.inj (sdFace_spec (C.toSdSimplex) i).1).symm

noncomputable def ofSdSimplex {k n : ℕ} (s : (sdComplex k).Simplex n) : FaceChain k n where
  faces := sdFace s
  nonempty := fun i => (sdFace_spec s i).2
  strict := fun hij => sdFace_strictMono s hij

theorem toSdSimplex_ofSdSimplex {k n : ℕ} (s : (sdComplex k).Simplex n) :
    (ofSdSimplex s).toSdSimplex = s := by
  apply Subtype.ext
  funext i
  exact (sdFace_spec s i).1.symm

def restrict {k n m : ℕ} (C : FaceChain k n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) : FaceChain k m where
  faces i := C.faces (e i)
  nonempty i := C.nonempty (e i)
  strict hij := C.strict (e.strictMono hij)

theorem face_subset_last {k n : ℕ} (C : FaceChain k n) (i : Fin (n + 1)) :
    C.faces i ⊆ C.faces (Fin.last n) := by
  by_cases h : i = Fin.last n
  · simpa [h]
  · have hlt : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) h
    exact (C.strict hlt).subset

theorem eq_of_faces_eq {k n : ℕ} {A B : FaceChain k n}
    (h : ∀ i, A.faces i = B.faces i) : A = B := by
  cases A with
  | mk af an astr =>
    cases B with
    | mk bf bn bstr =>
      have hf : af = bf := funext h
      subst bf
      rfl

noncomputable def mixture {k n : ℕ} (C : FaceChain k n)
    (p : StdSimplex ℝ (Fin (n + 1))) : StdSimplex ℝ (Fin (k + 1)) :=
  faceMixture C.faces C.nonempty p

def initialSegment {k n : ℕ} (C : FaceChain k (n + 1)) : FaceChain k n where
  faces i := C.faces i.castSucc
  nonempty i := C.nonempty i.castSucc
  strict h := C.strict (Fin.castSucc_lt_castSucc_iff.mpr h)

def mapVertices {k l n : ℕ} (e : Fin (k + 1) → Fin (l + 1))
    (he : Function.Injective e) (C : FaceChain k n) : FaceChain l n where
  faces i := (C.faces i).image e
  nonempty i := (C.nonempty i).image e
  strict := by
    intro i j hij
    have hsub : (C.faces i).image e ⊆ (C.faces j).image e := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
      exact Finset.mem_image.mpr ⟨w, (C.strict hij).subset hw, rfl⟩
    obtain ⟨w, hwj, hwnot⟩ := Finset.exists_of_ssubset (C.strict hij)
    have hin : e w ∈ (C.faces j).image e := Finset.mem_image.mpr ⟨w, hwj, rfl⟩
    have hnot : e w ∉ (C.faces i).image e := by
      intro heMem
      rcases Finset.mem_image.mp heMem with ⟨z, hz, heq⟩
      apply hwnot
      have hzw : z = w := he heq
      simpa [hzw] using hz
    exact (Finset.ssubset_iff_of_subset hsub).2 ⟨e w, hin, hnot⟩

theorem mapVertices_mixture {k l n : ℕ} (e : Fin (k + 1) → Fin (l + 1))
    (he : Function.Injective e) (C : FaceChain k n)
    (p : StdSimplex ℝ (Fin (n + 1))) :
    (C.mapVertices e he).mixture p = StdSimplex.map e (C.mixture p) := by
  change faceMixture (fun i => (C.faces i).image e) (fun i => (C.nonempty i).image e) p = _
  exact (faceMixture_map e he C.faces C.nonempty p).symm

def appendFull {k n : ℕ} (C : FaceChain k n)
    (hproper : C.faces (Fin.last n) ⊂ Finset.univ) : FaceChain k (n + 1) where
  faces := snocFaces C.faces Finset.univ
  nonempty := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa using (Finset.univ_nonempty : (Finset.univ : Finset (Fin (k + 1))).Nonempty)
    | cast j => simpa using C.nonempty j
  strict := by
    intro i j hij
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => exact (lt_irrefl _ hij).elim
      | cast i =>
        have hsub := C.face_subset_last i
        have hproperNe : C.faces (Fin.last n) ≠ Finset.univ :=
          (Finset.ssubset_iff_subset_ne.mp hproper).2
        have hne : C.faces i ≠ Finset.univ := by
          intro heq
          apply hproperNe
          apply Finset.Subset.antisymm (Finset.subset_univ _)
          simpa [heq] using hsub
        simpa only [snocFaces_castSucc, snocFaces_last] using
          (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩)
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact (not_lt_of_ge (Fin.le_last (j.castSucc)) hij).elim
      | cast i =>
        simpa only [snocFaces_castSucc] using C.strict (Fin.castSucc_lt_castSucc_iff.mp hij)

theorem prefix_mixture_split {k n : ℕ} (C : FaceChain k (n + 1))
    (p : StdSimplex ℝ (Fin (n + 2))) (hc : p.weights (Fin.last (n + 1)) < 1) :
    C.mixture p =
      convexCombPair (p.weights (Fin.last (n + 1)))
        (1 - p.weights (Fin.last (n + 1))) (p.weights_nonneg _)
        (sub_pos.mpr hc).le (by ring)
        (barycentricPoint (C.faces (Fin.last (n + 1))) (C.nonempty _))
        (C.initialSegment.mixture (normalizedPrefix p hc)) := by
  simpa [mixture, initialSegment] using
    (faceMixture_prefix_split C.faces C.nonempty p hc)

theorem exists_last_new_vertex {k r : ℕ} (C : FaceChain k (r + 1)) :
    ∃ v, v ∈ C.faces (Fin.last (r + 1)) ∧ v ∉ C.initialSegment.faces (Fin.last r) := by
  exact Finset.exists_of_ssubset (C.strict (Fin.castSucc_lt_last (Fin.last r)))

theorem face_subset_prev {k r : ℕ} (C : FaceChain k (r + 1))
    (i : Fin (r + 2)) (hi : i ≠ Fin.last (r + 1)) :
    C.faces i ⊆ C.initialSegment.faces (Fin.last r) := by
  induction i using Fin.lastCases with
  | last => exact (hi rfl).elim
  | cast j =>
    change C.faces j.castSucc ⊆ C.faces (Fin.last r).castSucc
    by_cases hj : j = Fin.last r
    · simpa [hj]
    · have hjlt : j < Fin.last r := lt_of_le_of_ne (Fin.le_last j) hj
      exact (C.strict (Fin.castSucc_lt_castSucc_iff.mpr hjlt)).subset

theorem mixture_weight_at_last_gap {k r : ℕ} (C : FaceChain k (r + 1))
    (p : StdSimplex ℝ (Fin (r + 2))) (v : Fin (k + 1))
    (hv : v ∈ C.faces (Fin.last (r + 1)))
    (hnew : v ∉ C.initialSegment.faces (Fin.last r)) :
    (C.mixture p).weights v =
      p.weights (Fin.last (r + 1)) * ((C.faces (Fin.last (r + 1))).card : ℝ)⁻¹ := by
  rw [mixture, faceMixture_weight_apply]
  simpa only [if_pos hv] using
    (Finset.sum_eq_single (s := Finset.univ)
      (f := fun i : Fin (r + 2) =>
        p.weights i * (if v ∈ C.faces i then ((C.faces i).card : ℝ)⁻¹ else 0))
      (Fin.last (r + 1))
      (fun i hi hne => by
        have hnot : v ∉ C.faces i := fun hmem => hnew (C.face_subset_prev i hne hmem)
        simp [hnot])
      (by simp))

theorem mixture_weight_ge_last {k n : ℕ} (C : FaceChain k n)
    (p : StdSimplex ℝ (Fin (n + 1))) (v : Fin (k + 1))
    (hv : v ∈ C.faces (Fin.last n)) :
    p.weights (Fin.last n) * ((C.faces (Fin.last n)).card : ℝ)⁻¹ ≤
      (C.mixture p).weights v := by
  rw [mixture, faceMixture_weight_apply]
  let term : Fin (n + 1) → ℝ := fun i =>
    p.weights i * (if v ∈ C.faces i then ((C.faces i).card : ℝ)⁻¹ else 0)
  have hnonneg : ∀ i, 0 ≤ term i := by
    intro i
    dsimp [term]
    exact mul_nonneg (p.weights_nonneg i) (by split_ifs <;> positivity)
  have hle : term (Fin.last n) ≤ ∑ i, term i :=
    Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ _)
  simpa [term, hv] using hle

theorem mixture_support {k n : ℕ} (C : FaceChain k n)
    (p : StdSimplex ℝ (Fin (n + 1))) (hp : ∀ i, p.weights i ≠ 0)
    (v : Fin (k + 1)) :
    (C.mixture p).weights v ≠ 0 ↔ v ∈ C.faces (Fin.last n) := by
  classical
  by_cases hv : v ∈ C.faces (Fin.last n)
  · constructor
    · intro _
      exact hv
    · intro _
      rw [mixture, faceMixture_weight_apply]
      let term : Fin (n + 1) → ℝ := fun i =>
        p.weights i * (if v ∈ C.faces i then ((C.faces i).card : ℝ)⁻¹ else 0)
      have hterm_nonneg : ∀ i, 0 ≤ term i := by
        intro i
        dsimp [term]
        exact mul_nonneg (p.weights_nonneg i) (by split_ifs <;> positivity)
      have hlast_pos : 0 < term (Fin.last n) := by
        dsimp [term]
        rw [if_pos hv]
        have hp' : 0 < p.weights (Fin.last n) :=
          lt_of_le_of_ne (p.weights_nonneg _) (Ne.symm (hp _))
        have hcard : 0 < (C.faces (Fin.last n)).card :=
          Finset.card_pos.mpr (C.nonempty _)
        positivity
      have hle : term (Fin.last n) ≤ ∑ i, term i :=
        Finset.single_le_sum (fun i _ => hterm_nonneg i) (Finset.mem_univ _)
      have hsum_pos : 0 < ∑ i, term i := lt_of_lt_of_le hlast_pos hle
      simpa only [term] using (ne_of_gt hsum_pos)
  · constructor
    · intro hne
      by_contra hmem
      have hzero : (C.mixture p).weights v = 0 := by
        rw [mixture, faceMixture_weight_apply]
        have hnot (i : Fin (n + 1)) : v ∉ C.faces i :=
          fun hi => hv (C.face_subset_last i hi)
        simp [hnot]
      exact hne hzero
    · intro hmem
      exact (hv hmem).elim

theorem last_faces_eq_of_mixture_eq {k n m : ℕ}
    (A : FaceChain k n) (B : FaceChain k m)
    (p : StdSimplex ℝ (Fin (n + 1))) (q : StdSimplex ℝ (Fin (m + 1)))
    (hp : ∀ i, p.weights i ≠ 0) (hq : ∀ i, q.weights i ≠ 0)
    (hmix : A.mixture p = B.mixture q) :
    A.faces (Fin.last n) = B.faces (Fin.last m) := by
  ext v
  constructor
  · intro hv
    have hneA := (A.mixture_support p hp v).2 hv
    have hneB : (B.mixture q).weights v ≠ 0 := by
      rw [← hmix]
      exact hneA
    exact (B.mixture_support q hq v).1 hneB
  · intro hv
    have hneB := (B.mixture_support q hq v).2 hv
    have hneA : (A.mixture p).weights v ≠ 0 := by
      rw [hmix]
      exact hneB
    exact (A.mixture_support p hp v).1 hneA

theorem mixture_dim_zero_weight {k : ℕ} (A : FaceChain k 0)
    (p : StdSimplex ℝ (Fin 1)) (v : Fin (k + 1))
    (hv : v ∈ A.faces (Fin.last 0)) :
    (A.mixture p).weights v = ((A.faces (Fin.last 0)).card : ℝ)⁻¹ := by
  rw [mixture, faceMixture_weight_apply]
  have hp0 : p.weights (0 : Fin 1) = 1 := by simpa using (show p.weights (Fin.last 0) = 1 by simp)
  have hv0 : v ∈ A.faces (0 : Fin 1) := by simpa using hv
  simp [hp0, hv0]

theorem convexCombPair_right_cancel {M : Type u} (c : ℝ) (hc : 0 ≤ c) (hc' : c < 1)
    (x y z : StdSimplex ℝ M)
    (h : convexCombPair c (1 - c) hc (sub_pos.mpr hc').le (by ring) x y =
      convexCombPair c (1 - c) hc (sub_pos.mpr hc').le (by ring) x z) : y = z := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro w
  have he := congrArg (fun q : StdSimplex ℝ M => q.weights w) h
  simp only [StdSimplex.weights_convexCombPair, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul] at he
  exact (mul_right_inj' (ne_of_gt (sub_pos.mpr hc'))).mp (add_left_cancel he)

theorem convexCombPair_ext {M : Type u} {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hc' : c < 1) (hd' : d < 1)
    (x x' y y' : StdSimplex ℝ M) (hcd : c = d) (hx : x = x') (hy : y = y') :
    convexCombPair c (1 - c) hc (sub_pos.mpr hc').le (by ring) x y =
      convexCombPair d (1 - d) hd (sub_pos.mpr hd').le (by ring) x' y' := by
  cases hcd
  cases hx
  cases hy
  rfl

private theorem le_of_mul_pos_le_mul_pos {a b c : ℝ} (hc : 0 < c)
    (h : a * c ≤ b * c) : a ≤ b := by
  by_contra hn
  have hlt : b < a := lt_of_not_ge hn
  have hltmul := mul_lt_mul_of_pos_right hlt hc
  linarith

theorem last_coefficient_eq_of_mixture_eq {k r s : ℕ}
    (A : FaceChain k (r + 1)) (B : FaceChain k (s + 1))
    (p : StdSimplex ℝ (Fin (r + 2))) (q : StdSimplex ℝ (Fin (s + 2)))
    (hlast : A.faces (Fin.last (r + 1)) = B.faces (Fin.last (s + 1)))
    (hmix : A.mixture p = B.mixture q) :
    p.weights (Fin.last (r + 1)) = q.weights (Fin.last (s + 1)) := by
  have hcard : 0 < (A.faces (Fin.last (r + 1))).card :=
    Finset.card_pos.mpr (A.nonempty _)
  have hinv : 0 < ((A.faces (Fin.last (r + 1))).card : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast hcard)
  obtain ⟨vA, hvA, hnewA⟩ := exists_last_new_vertex A
  have hAw := mixture_weight_at_last_gap A p vA hvA hnewA
  have hBge := mixture_weight_ge_last B q vA (hlast ▸ hvA)
  have hscaled₁ :
      q.weights (Fin.last (s + 1)) * ((A.faces (Fin.last (r + 1))).card : ℝ)⁻¹ ≤
        p.weights (Fin.last (r + 1)) * ((A.faces (Fin.last (r + 1))).card : ℝ)⁻¹ := by
    calc
      _ ≤ (B.mixture q).weights vA := by simpa [hlast] using hBge
      _ = (A.mixture p).weights vA := congrArg (fun t : StdSimplex ℝ _ => t.weights vA) hmix.symm
      _ = _ := hAw
  have hqle : q.weights (Fin.last (s + 1)) ≤ p.weights (Fin.last (r + 1)) :=
    le_of_mul_pos_le_mul_pos hinv hscaled₁
  obtain ⟨vB, hvB, hnewB⟩ := exists_last_new_vertex B
  have hBw := mixture_weight_at_last_gap B q vB hvB hnewB
  have hAge := mixture_weight_ge_last A p vB (hlast.symm ▸ hvB)
  have hscaled₂ :
      p.weights (Fin.last (r + 1)) * ((A.faces (Fin.last (r + 1))).card : ℝ)⁻¹ ≤
        q.weights (Fin.last (s + 1)) * ((A.faces (Fin.last (r + 1))).card : ℝ)⁻¹ := by
    calc
      _ ≤ (A.mixture p).weights vB := by simpa using hAge
      _ = (B.mixture q).weights vB := congrArg (fun t : StdSimplex ℝ _ => t.weights vB) hmix
      _ = _ := by simpa [hlast] using hBw
  have hple : p.weights (Fin.last (r + 1)) ≤ q.weights (Fin.last (s + 1)) :=
    le_of_mul_pos_le_mul_pos hinv hscaled₂
  exact le_antisymm hple hqle

theorem initialSegment_mixture_eq_of_mixture_eq {k r s : ℕ}
    (A : FaceChain k (r + 1)) (B : FaceChain k (s + 1))
    (p : StdSimplex ℝ (Fin (r + 2))) (q : StdSimplex ℝ (Fin (s + 2)))
    (hp : ∀ i, p.weights i ≠ 0) (hq : ∀ i, q.weights i ≠ 0)
    (hlast : A.faces (Fin.last (r + 1)) = B.faces (Fin.last (s + 1)))
    (hmix : A.mixture p = B.mixture q) :
    A.initialSegment.mixture (normalizedPrefix p (last_weight_lt_one_of_nonzero p hp)) =
      B.initialSegment.mixture (normalizedPrefix q (last_weight_lt_one_of_nonzero q hq)) := by
  let hcₚ := last_weight_lt_one_of_nonzero p hp
  let hcq := last_weight_lt_one_of_nonzero q hq
  have hcoeff := last_coefficient_eq_of_mixture_eq A B p q hlast hmix
  have hsA := prefix_mixture_split A p hcₚ
  have hsB := prefix_mixture_split B q hcq
  have hpoints :
      barycentricPoint (B.faces (Fin.last (s + 1))) (B.nonempty _) =
        barycentricPoint (A.faces (Fin.last (r + 1))) (A.nonempty _) := by
    apply StdSimplex.ext
    apply Finsupp.ext
    intro v
    rw [barycentricPoint_weight_apply, barycentricPoint_weight_apply]
    simp [hlast]
  have hsB' :
      B.mixture q =
        convexCombPair (p.weights (Fin.last (r + 1)))
          (1 - p.weights (Fin.last (r + 1))) (p.weights_nonneg _)
          (sub_pos.mpr hcₚ).le (by ring)
          (barycentricPoint (A.faces (Fin.last (r + 1))) (A.nonempty _))
          (B.initialSegment.mixture (normalizedPrefix q hcq)) := by
    calc
      B.mixture q = _ := hsB
      _ = _ := convexCombPair_ext (q.weights_nonneg _) (p.weights_nonneg _)
        hcq hcₚ _ _ _ _ hcoeff.symm hpoints rfl
  have hcomb :
      convexCombPair (p.weights (Fin.last (r + 1)))
        (1 - p.weights (Fin.last (r + 1))) (p.weights_nonneg _)
        (sub_pos.mpr hcₚ).le (by ring)
        (barycentricPoint (A.faces (Fin.last (r + 1))) (A.nonempty _))
        (A.initialSegment.mixture (normalizedPrefix p hcₚ)) =
      convexCombPair (p.weights (Fin.last (r + 1)))
        (1 - p.weights (Fin.last (r + 1))) (p.weights_nonneg _)
        (sub_pos.mpr hcₚ).le (by ring)
        (barycentricPoint (A.faces (Fin.last (r + 1))) (A.nonempty _))
        (B.initialSegment.mixture (normalizedPrefix q hcq)) := by
    calc
      _ = A.mixture p := hsA.symm
      _ = B.mixture q := hmix
      _ = _ := hsB'
  exact convexCombPair_right_cancel _ (p.weights_nonneg _)
    (last_weight_lt_one_of_nonzero p hp)
    _ _ _ hcomb

theorem eq_of_mixture_eq {k n m : ℕ}
    (A : FaceChain k n) (B : FaceChain k m)
    (p : StdSimplex ℝ (Fin (n + 1))) (q : StdSimplex ℝ (Fin (m + 1)))
    (hp : ∀ i, p.weights i ≠ 0) (hq : ∀ i, q.weights i ≠ 0)
    (hmix : A.mixture p = B.mixture q) :
    n = m ∧ HEq A B ∧ HEq p q := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    have hlast := last_faces_eq_of_mixture_eq A B p q hp hq hmix
    cases n with
    | zero =>
      cases m with
      | zero =>
        have hfaces : ∀ i, A.faces i = B.faces i := by
          intro i
          have hi : i = Fin.last 0 := by
            apply Fin.ext
            omega
          subst i
          exact hlast
        have hchain := eq_of_faces_eq hfaces
        have hpq : p = q := by
          apply StdSimplex.ext
          apply Finsupp.ext
          intro i
          have hi : i = Fin.last 0 := by
            apply Fin.ext
            omega
          rw [hi]
          simp
        exact ⟨rfl, heq_of_eq hchain, heq_of_eq hpq⟩
      | succ m =>
        obtain ⟨v, hv, hnew⟩ := exists_last_new_vertex B
        have hvA : v ∈ A.faces (Fin.last 0) := by rw [hlast]; exact hv
        have hA := mixture_dim_zero_weight A p v hvA
        have hB := mixture_weight_at_last_gap B q v hv hnew
        have hinv : 0 < ((B.faces (Fin.last (m + 1))).card : ℝ)⁻¹ :=
          inv_pos.mpr (by exact_mod_cast (Finset.card_pos.mpr (B.nonempty _)))
        have hscale : (1 : ℝ) * ((B.faces (Fin.last (m + 1))).card : ℝ)⁻¹ =
            q.weights (Fin.last (m + 1)) * ((B.faces (Fin.last (m + 1))).card : ℝ)⁻¹ := by
          have heqv := congrArg (fun t : StdSimplex ℝ (Fin (k + 1)) => t.weights v) hmix
          rw [hA, hB] at heqv
          rw [hlast] at heqv
          simpa using heqv
        have hqone : (1 : ℝ) = q.weights (Fin.last (m + 1)) :=
          (mul_left_inj' (ne_of_gt hinv)).mp hscale
        have hlt := last_weight_lt_one_of_nonzero q hq
        rw [← hqone] at hlt
        exact (lt_irrefl _ hlt).elim
    | succ n =>
      cases m with
      | zero =>
        obtain ⟨v, hv, hnew⟩ := exists_last_new_vertex A
        have hvB : v ∈ B.faces (Fin.last 0) := by rw [hlast.symm]; exact hv
        have hA := mixture_weight_at_last_gap A p v hv hnew
        have hB := mixture_dim_zero_weight B q v hvB
        have hinv : 0 < ((A.faces (Fin.last (n + 1))).card : ℝ)⁻¹ :=
          inv_pos.mpr (by exact_mod_cast (Finset.card_pos.mpr (A.nonempty _)))
        have hscale : p.weights (Fin.last (n + 1)) *
            ((A.faces (Fin.last (n + 1))).card : ℝ)⁻¹ =
            (1 : ℝ) * ((A.faces (Fin.last (n + 1))).card : ℝ)⁻¹ := by
          have heqv := congrArg (fun t : StdSimplex ℝ (Fin (k + 1)) => t.weights v) hmix
          rw [hA, hB] at heqv
          rw [hlast.symm] at heqv
          simpa using heqv
        have hpone : p.weights (Fin.last (n + 1)) = 1 :=
          (mul_left_inj' (ne_of_gt hinv)).mp hscale
        have hlt := last_weight_lt_one_of_nonzero p hp
        rw [hpone] at hlt
        exact (lt_irrefl _ hlt).elim
      | succ m =>
        have hcoeff := last_coefficient_eq_of_mixture_eq A B p q hlast hmix
        have hprefix := initialSegment_mixture_eq_of_mixture_eq A B p q hp hq hlast hmix
        obtain ⟨hdim, hchainHEq, hpHEq⟩ :=
          ih n (Nat.lt_succ_self n) A.initialSegment B.initialSegment
            (normalizedPrefix p (last_weight_lt_one_of_nonzero p hp))
            (normalizedPrefix q (last_weight_lt_one_of_nonzero q hq))
          (normalizedPrefix_weights_ne_zero p (last_weight_lt_one_of_nonzero p hp) hp)
          (normalizedPrefix_weights_ne_zero q (last_weight_lt_one_of_nonzero q hq) hq)
          hprefix
        subst m
        have hchain : A.initialSegment = B.initialSegment := eq_of_heq hchainHEq
        have hnorm : normalizedPrefix p (last_weight_lt_one_of_nonzero p hp) =
            normalizedPrefix q (last_weight_lt_one_of_nonzero q hq) := eq_of_heq hpHEq
        have hfaces : ∀ i, A.faces i = B.faces i := by
          intro i
          induction i using Fin.lastCases with
          | last => exact hlast
          | cast j =>
            have hj := congrArg (fun C : FaceChain k n => C.faces j) hchain
            exact hj
        have hchainEq : A = B := eq_of_faces_eq hfaces
        have hpq : p = q := by
          apply StdSimplex.ext
          apply Finsupp.ext
          intro i
          induction i using Fin.lastCases with
          | last => exact hcoeff
          | cast j =>
            have hj := congrArg (fun t : StdSimplex ℝ (Fin (n + 1)) => t.weights j) hnorm
            rw [normalizedPrefix_weights, normalizedPrefix_weights] at hj
            rw [← hcoeff] at hj
            have hden : 1 - p.weights (Fin.last (n + 1)) ≠ 0 :=
              ne_of_gt (sub_pos.mpr (last_weight_lt_one_of_nonzero p hp))
            have hm := congrArg (fun a : ℝ => a * (1 - p.weights (Fin.last (n + 1)))) hj
            field_simp [hden] at hm
            exact hm
        exact ⟨rfl, heq_of_eq hchainEq, heq_of_eq hpq⟩

end FaceChain

end HomotopyHypothesis.Approximation.BarycentricCell
