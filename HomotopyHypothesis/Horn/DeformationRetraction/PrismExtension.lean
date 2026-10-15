import Mathlib.Topology.Piecewise
import HomotopyHypothesis.Realization.Boundary.HornPrism
import HomotopyHypothesis.Realization.Boundary.SimplexDisk
/-!
# Extending a homotopy across a horn

A horn-prism retraction extends homotopies with both endpoint maps prescribed.
-/

universe u

open CategoryTheory Limits Topology
open HomotopyHypothesis.Realization.Boundary

namespace HomotopyHypothesis.Horn.DeformationRetraction

/-- The midpoint of the interval. -/
noncomputable def intervalMidpoint : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

/-- At the midpoint, the prism projection lies in the horn. -/
theorem hornPrismProjectedCoords_midpoint_mem {n : ℕ} (hn : 0 < n)
    (k : Fin (n + 1)) (x : ClosedCoordSimplex n) :
    hornPrismProjectedCoords n hn k x intervalMidpoint ∈ coordinateHorn n k := by
  have h := hornPrismProjectedPair_mem hn k (x, intervalMidpoint)
  change (_ ∈ coordinateHorn n k) ∨ _ at h
  rcases h with h | h
  · exact h
  · change (hornPrismProjectedTime n hn k x intervalMidpoint : ℝ) = 0 ∨
      (hornPrismProjectedTime n hn k x intervalMidpoint : ℝ) = 1 at h
    norm_num [hornPrismProjectedTime, intervalMidpoint] at h

/-- A continuous retraction from the simplex onto a horn. -/
noncomputable def coordinateHornRetraction {n : ℕ} (hn : 0 < n) (k : Fin (n + 1)) :
    C(ClosedCoordSimplex n, coordinateHorn n k) where
  toFun x := ⟨hornPrismProjectedCoords n hn k x intervalMidpoint,
    hornPrismProjectedCoords_midpoint_mem hn k x⟩
  continuous_toFun :=
    ((hornPrismProjectedCoords_continuous hn k).comp
      (continuous_id.prodMk continuous_const)).subtype_mk _

@[simp]
theorem coordinateHornRetraction_fixed {n : ℕ} (hn : 0 < n) (k : Fin (n + 1))
    (x : coordinateHorn n k) : coordinateHornRetraction hn k x = x := by
  apply Subtype.ext
  exact congrArg Prod.fst (hornPrismProjectedPair_fixed hn k
    (x.val, intervalMidpoint) (Or.inl x.property))

/-- A coordinate horn is a closed union of faces. -/
theorem coordinateHorn_isClosed (n : ℕ) (k : Fin (n + 1)) :
    IsClosed (coordinateHorn n k) := by
  have heq : coordinateHorn n k =
      ⋃ i : {i : Fin (n + 1) // i ≠ k}, {x | hornPrismWeight n x i.val = 0} := by
    ext x
    simp [coordinateHorn]
  rw [heq]
  exact isClosed_iUnion_of_finite fun i => isClosed_eq (hornPrismWeight_continuous n i.val)
    continuous_const

/-- Extend a homotopy on the horn while prescribing both endpoint maps on the simplex. -/
theorem coordinateHorn_path_extension {Z : Type u} [TopologicalSpace Z]
    {n : ℕ} (hn : 0 < n) (k : Fin (n + 1))
    (a : C(coordinateHorn n k × unitInterval, Z))
    (b₀ b₁ : C(ClosedCoordSimplex n, Z))
    (h₀ : ∀ x : coordinateHorn n k, a (x, 0) = b₀ x)
    (h₁ : ∀ x : coordinateHorn n k, a (x, 1) = b₁ x) :
    ∃ H : C(ClosedCoordSimplex n × unitInterval, Z),
      (∀ (x : coordinateHorn n k) t, H (x.val, t) = a (x, t)) ∧
      (∀ x, H (x, 0) = b₀ x) ∧ (∀ x, H (x, 1) = b₁ x) := by
  classical
  let middle : C(ClosedCoordSimplex n × unitInterval, Z) :=
    a.comp (((coordinateHornRetraction hn k).comp ContinuousMap.fst).prodMk ContinuousMap.snd)
  let G : ClosedCoordSimplex n × unitInterval → Z := fun z =>
    if z.2 = 0 then b₀ z.1 else if z.2 = 1 then b₁ z.1 else middle z
  let S : Set (ClosedCoordSimplex n × unitInterval) :=
    {z | z.1 ∈ coordinateHorn n k}
  let T₀ : Set (ClosedCoordSimplex n × unitInterval) := {z | z.2 = 0}
  let T₁ : Set (ClosedCoordSimplex n × unitInterval) := {z | z.2 = 1}
  have hS : IsClosed S := (coordinateHorn_isClosed n k).preimage continuous_fst
  have hT₀ : IsClosed T₀ := isClosed_eq continuous_snd continuous_const
  have hT₁ : IsClosed T₁ := isClosed_eq continuous_snd continuous_const
  have hmiddle (x : coordinateHorn n k) (t : unitInterval) :
      middle (x.val, t) = a (x, t) := by
    change a (coordinateHornRetraction hn k x.val, t) = a (x, t)
    rw [coordinateHornRetraction_fixed]
  have hGS : ContinuousOn G S := by
    apply middle.continuous.continuousOn.congr
    rintro ⟨x, t⟩ hx
    let x' : coordinateHorn n k := ⟨x, hx⟩
    change (if t = 0 then b₀ x else if t = 1 then b₁ x else middle (x, t)) = middle (x, t)
    split_ifs with hzero hone
    · subst t
      exact (h₀ x').symm.trans (hmiddle x' 0).symm
    · subst t
      exact (h₁ x').symm.trans (hmiddle x' 1).symm
    · rfl
  have hGT₀ : ContinuousOn G T₀ := by
    apply (b₀.continuous.comp continuous_fst).continuousOn.congr
    intro z hz
    change z.2 = 0 at hz
    simp only [G, hz, ite_true, Function.comp_apply]
  have hGT₁ : ContinuousOn G T₁ := by
    apply (b₁.continuous.comp continuous_fst).continuousOn.congr
    intro z hz
    change z.2 = 1 at hz
    simp only [G, hz, one_ne_zero, ite_false, ite_true, Function.comp_apply]
  have hprism : coordinateHornPrism n k = (S ∪ T₀) ∪ T₁ := by
    ext z
    change (_ ∨ ((z.2 : ℝ) = 0 ∨ (z.2 : ℝ) = 1)) ↔ ((_ ∨ z.2 = 0) ∨ z.2 = 1)
    have hzero : (z.2 : ℝ) = 0 ↔ z.2 = 0 := by constructor <;> intro h <;> simpa using h
    have hone : (z.2 : ℝ) = 1 ↔ z.2 = 1 := by constructor <;> intro h <;> simpa using h
    rw [hzero, hone, or_assoc]
    rfl
  have hG : ContinuousOn G (coordinateHornPrism n k) := by
    rw [hprism]
    exact (hGS.union_of_isClosed hGT₀ hS hT₀).union_of_isClosed hGT₁
      (hS.union hT₀) hT₁
  let g : C(coordinateHornPrism n k, Z) := ⟨fun z => G z.val, hG.domRestrict⟩
  let R : C(ClosedCoordSimplex n × unitInterval, coordinateHornPrism n k) :=
    ⟨fun z => ⟨hornPrismProjectedPair n hn k z, hornPrismProjectedPair_mem hn k z⟩,
      (hornPrismProjectedPair_continuous hn k).subtype_mk _⟩
  let H := g.comp R
  have hfixed (z : ClosedCoordSimplex n × unitInterval) (hz : z ∈ coordinateHornPrism n k) :
      H z = G z := congrArg G (hornPrismProjectedPair_fixed hn k z hz)
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x t
    rw [hfixed (x.val, t) (Or.inl x.property)]
    change (if t = 0 then b₀ x.val else if t = 1 then b₁ x.val else middle (x.val, t)) = _
    split_ifs with hzero hone
    · subst t; exact (h₀ x).symm
    · subst t; exact (h₁ x).symm
    · exact hmiddle x t
  · intro x
    rw [hfixed (x, 0) (Or.inr (Or.inl rfl))]
    simp only [G, ite_true]
  · intro x
    rw [hfixed (x, 1) (Or.inr (Or.inr rfl))]
    simp only [G, one_ne_zero, ite_false, ite_true]

end HomotopyHypothesis.Horn.DeformationRetraction
