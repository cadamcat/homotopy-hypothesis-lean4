import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.HelperStatements.SharpExistsNormalForm
import HomotopyHypothesis.Approximation.Topological.NormalForm.NF

/-!
# `nf`

One declaration of `HomotopyHypothesis.Approximation.Topological.NormalForm`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The chosen normal form of a simplex of `X♯`. -/
noncomputable def nf {X : SemiSSet.{u}} {n : ℕ}
    (e : (sharp X).obj (op (Henry.SemiSimplexCategory.mk n))) : NF X n :=
  let h := sharp_exists_normalForm e
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.1⟩
