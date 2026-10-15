import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismRelative.Proof
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism

/-!
# `anodyne_dprismLan_rel`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- **The derived cylinder collapses onto its derived end relative to a semi-simplicial subset**
(Rourke–Sanderson, Lemma 4.3): for finite `W` and `J ⊆ W`, `W' ⊔_{J'} D J ⟶ D W` is anodyne.
Proof: attach the simplices of `W` not in `J` one at a time in order of dimension; the derived
cylinder and the derived subdivision, being left Kan extensions along the Yoneda embedding, carry
the attaching pushout `∂Δ_k ⟶ Δ_k` to pushouts, so each step is a pushout of
`dprismBdryι k` (`anodyne_dprismBdryι`). Frozen helper statement. -/
theorem anodyne_dprismLan_rel (W : SemiSSet.{u}) (J : Subfunctor W) (hW : W.IsFinite) :
    anodyne (pushout.desc (sdLanToDprism.app W) (dprismLan.map J.ι)
      (sdLanToDprism.naturality J.ι) :
      pushout (sdLan.map J.ι) (sdLanToDprism.app J.toFunctor) ⟶ dprismLan.obj W) := by apply @_root_.HomotopyHypothesis.Approximation.DerivedPrismRelative.anodyne_dprismLan_rel_proof <;> assumption
