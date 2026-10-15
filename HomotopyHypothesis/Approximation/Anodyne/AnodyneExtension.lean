import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Anodyne

open HomotopyHypothesis.Henry
open SemiSSet

theorem isKan_extension_of_anodyne_proof {X : SemiSSet.{u}} (hX : X.IsKan)
    {A B : SemiSSet.{u}} (j : A ⟶ B) (hj : anodyne j) (a : A ⟶ X) :
    ∃ b : B ⟶ X, j ≫ b = a := by
  let T : MorphismProperty SemiSSet.{u} := MorphismProperty.single (terminal.from X)
  have hHorn : hornInclusions ≤ T.llp := by
    change MorphismProperty.ofHoms
      (fun i : Σ n : ℕ, Fin (n + 2) => (horn.{u} (i.1 + 1) i.2).ι) ≤ T.llp
    apply (MorphismProperty.ofHoms_le_iff
      (fun i : Σ n : ℕ, Fin (n + 2) => (horn.{u} (i.1 + 1) i.2).ι) T.llp).2
    rintro ⟨n, k⟩
    change (MorphismProperty.single (terminal.from X)).llp ((horn (n + 1) k).ι)
    rw [MorphismProperty.llp_ofHoms_iff_hasLiftingProperty Unit]
    refine ⟨?_⟩
    intro f g sq
    obtain ⟨σ, hσ⟩ := hX n k f
    exact CommSq.HasLift.mk' ⟨σ, hσ, terminal.hom_ext _ _⟩
  have hIso : MorphismProperty.isomorphisms SemiSSet.{u} ≤ T.llp := by
    intro Y₀ Y₁ i hi
    letI := hi
    exact MorphismProperty.llp_of_isIso T i
  have hPush : hornInclusions.pushouts ≤ T.llp :=
    (MorphismProperty.pushouts_le_iff).2 hHorn
  let G : MorphismProperty SemiSSet.{u} :=
    hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}
  have hG : G ≤ T.llp := by
    dsimp [G]
    exact sup_le hPush hIso
  have hjLift : T.llp j := by
    exact (MorphismProperty.multiplicativeClosure_le_iff G T.llp).2 hG j hj
  have hLP : HasLiftingProperty j (terminal.from X) := by
    change (MorphismProperty.single (terminal.from X)).llp j at hjLift
    exact (MorphismProperty.llp_ofHoms_iff_hasLiftingProperty Unit j
      (terminal.from X)).1 hjLift
  let sq : CommSq a j (terminal.from X) (terminal.from B) :=
    ⟨terminal.hom_ext _ _⟩
  let hLift := hLP.sq_hasLift sq
  exact ⟨hLift.exists_lift.some.l, hLift.exists_lift.some.fac_left⟩

#print axioms isKan_extension_of_anodyne_proof

end HomotopyHypothesis.Approximation.Anodyne
