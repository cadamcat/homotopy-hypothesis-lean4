import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.HelperStatements.SharpExistsNormalForm
import HomotopyHypothesis.Approximation.Topological.NormalForm.NF
import HomotopyHypothesis.Approximation.Topological.NormalForm.Nf2

/-!
# `sharpMk_nf`

One declaration of `HomotopyHypothesis.Approximation.Topological.NormalForm`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

theorem sharpMk_nf {X : SemiSSet.{u}} {n : ℕ}
    (e : (sharp X).obj (op (Henry.SemiSimplexCategory.mk n))) :
    sharpMk (nf e).v (nf e).x = e :=
  (sharp_exists_normalForm e).choose_spec.choose_spec.choose_spec.2
