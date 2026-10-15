import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Completion.Compression.Converse
import HomotopyHypothesis.Completion.Compression.DiskZero
import HomotopyHypothesis.Completion.Compression.Glue
import HomotopyHypothesis.Completion.Compression.PiZero
import HomotopyHypothesis.Completion.Compression.Transport
/-
# The compression criterion for weak homotopy equivalences

A continuous map is a weak homotopy equivalence (bijective on path components
and on all homotopy groups) if and only if it has the relative lifting property
up to homotopy relative to the boundary against every sphere-to-disk inclusion.
This is the classical compression lemma underlying the comparison between
cylinder categories and spaces.
-/
noncomputable section

namespace HomotopyHypothesis.Completion.Compression

universe u

open CategoryTheory

/-- Forward direction on `π₀`, surjectivity: from the `n = 0` lifting property. -/
theorem henry_imp_zeroth_surjective {X Y : TopCat.{u}} (f : X ⟶ Y)
    (H : Henry.Top.weakEquivalences.{u} f) :
    Function.Surjective (HomotopyHypothesis.zerothHomotopyMap f) := by
  apply zeroth_surjective_of_joined
  intro y
  exact henry_zero_surjective f (fun a b _ => H 0 a b (by
    -- the `n = 0` commutativity is automatic; both sides come from the empty sphere
    exact boundary_zero_subsingleton _ _ _)) y

/-- Forward direction on `π₀`, injectivity: from the `n = 1` lifting property. -/
theorem henry_imp_zeroth_injective {X Y : TopCat.{u}} (f : X ⟶ Y)
    (H : Henry.Top.weakEquivalences.{u} f) :
    Function.Injective (HomotopyHypothesis.zerothHomotopyMap f) := by
  apply zeroth_injective_of_joined
  intro x₀ x₁ h
  exact henry_one_injective f (fun a b hcomm => H 1 a b hcomm) h

/-- Forward direction on `π₀`, bijectivity. -/
theorem henry_imp_zeroth_bijective {X Y : TopCat.{u}} (f : X ⟶ Y)
    (H : Henry.Top.weakEquivalences.{u} f) :
    Function.Bijective (HomotopyHypothesis.zerothHomotopyMap f) :=
  ⟨henry_imp_zeroth_injective f H, henry_imp_zeroth_surjective f H⟩

/-- Forward direction: the lifting property gives bijections on `π₀` and all
`π_{n+1}`, via the disk-cube correspondence and face-gluing. -/
theorem henry_imp_weak {X Y : TopCat.{u}} (f : X ⟶ Y)
    (H : Henry.Top.weakEquivalences.{u} f) :
    weakHomotopyEquivalences.{u} f := by
  constructor
  · exact henry_imp_zeroth_bijective f H
  · intro n x
    exact ⟨henry_imp_injective_pi f H n x, henry_imp_surjective_pi f H n x⟩

/-- Converse at `n = 0`: surjectivity on path components gives the filler. -/
theorem weak_n0_filler {X Y : TopCat.{u}} (f : X ⟶ Y)
    (H : weakHomotopyEquivalences.{u} f)
    (a : TopCat.diskBoundary.{u} 0 ⟶ X) (b : TopCat.disk.{u} 0 ⟶ Y)
    (_hcomm : a ≫ f = TopCat.diskBoundaryInclusion 0 ≫ b) :
    ∃ l : TopCat.disk.{u} 0 ⟶ X, TopCat.diskBoundaryInclusion 0 ≫ l = a ∧
      (l ≫ f).hom.HomotopicRel b.hom
        (Set.range (TopCat.diskBoundaryInclusion.{u} 0)) := by
  have hsurj : Function.Surjective (HomotopyHypothesis.zerothHomotopyMap f) := H.1.2
  obtain ⟨x, hx⟩ : ∃ x : X, Joined (f x) (b diskZeroPt) := by
    obtain ⟨p, hp⟩ := hsurj (ZerothHomotopy.mk (b diskZeroPt))
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective (X := X) p
    have hmap : ZerothHomotopy.mk (f x) = ZerothHomotopy.mk (b diskZeroPt) := hp
    exact ⟨x, Quotient.exact hmap⟩
  refine ⟨diskZeroMap X x, boundary_zero_subsingleton _ _ _, ?_⟩
  have hrange : Set.range (TopCat.diskBoundaryInclusion.{u} 0).hom = ∅ :=
    range_inclusion_zero_empty
  rw [hrange, ContinuousMap.homotopicRel_empty]
  have hconst_lf : ((diskZeroMap X x ≫ f).hom : C(TopCat.disk.{u} 0, Y)) =
      ContinuousMap.const _ (f x) := by
    apply ContinuousMap.ext
    intro p
    rfl
  have hconst_b : (b.hom : C(TopCat.disk.{u} 0, Y)) = ContinuousMap.const _ (b diskZeroPt) := by
    apply ContinuousMap.ext
    intro p
    have hpt : p = diskZeroPt := Subsingleton.elim _ _
    rw [hpt]
    rfl
  rw [hconst_lf, hconst_b, ContinuousMap.homotopic_const_iff]
  exact hx

/-- Converse direction: bijections on `π₀` and all `π_{n+1}` give fillers with
exact boundary and homotopy relative to the boundary, via the homotopy
extension property of the sphere-to-disk inclusions. -/
theorem weak_imp_henry {X Y : TopCat.{u}} (f : X ⟶ Y)
    (H : weakHomotopyEquivalences.{u} f) :
    Henry.Top.weakEquivalences.{u} f := by
  intro m a b hcomm
  match m, a, b, hcomm with
  | 0, a, b, hcomm => exact weak_n0_filler f H a b hcomm
  | 1, a, b, hcomm =>
    obtain ⟨l₀, hl₀⟩ := exists_extension_one f H.1.1 a b hcomm
    exact liftsAt_of_extension f 0 a l₀ hl₀ (fun x => (H.2 0 x).2) b hcomm
  | n + 2, a, b, hcomm =>
    obtain ⟨l₀, hl₀⟩ := exists_extension_succ_succ f n (fun x => (H.2 n x).1) a b hcomm
    exact liftsAt_of_extension f (n + 1) a l₀ hl₀ (fun x => (H.2 (n + 1) x).2) b hcomm

/-- Compression criterion: Henry's lifting-property weak equivalences coincide
with the classical weak homotopy equivalences. -/
theorem compression_criterion_proof :
    Henry.Top.weakEquivalences.{u} = weakHomotopyEquivalences.{u} := by
  apply CategoryTheory.MorphismProperty.ext
  intro X Y f
  constructor
  · intro H
    exact henry_imp_weak f H
  · intro H
    exact weak_imp_henry f H

end HomotopyHypothesis.Completion.Compression
