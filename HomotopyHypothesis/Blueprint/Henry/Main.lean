import HomotopyHypothesis.Blueprint.Henry.Main.Part1
import HomotopyHypothesis.Blueprint.Henry.Main.Part2
import HomotopyHypothesis.Blueprint.Henry.Main.Part3

/-!
# The comparison of cylinder coherators with spaces

Assembly of H Thm 5.1.2(5) (H:2765–2798) from the packages: for every cylinder coherator `𝒜`
(essentially small, in the universes of spaces) and every cellular realization `G` of `𝒜` whose
value at the marked object is contractible, the fundamental `∞`-groupoid functor
`π_∞ = R_G : TopCat ⥤ 𝒜̃` sends weak homotopy equivalences to weak equivalences and induces an
equivalence between the localizations.

Route: `C^Δ` is a cylinder coherator with an acyclic standard realization `R` (H §5.2); a morphism
`Φ : 𝒜 ⥤ C^Δ` preserving the marked objects is acyclic (H Prop 4.3.2), so `Φ ⋙ R` is acyclic; any
other `G` with contractible `G o` is then acyclic as well (H Thm 5.1.2(5)); finally an acyclic
cellular realization induces an equivalence of localizations with spaces. The last step factors
`π_∞ = R_G` as the restriction `TopCat ⥤ FinCell̃` followed by `F^* : FinCell̃ ⥤ 𝒜̃` for the
corestriction `F : 𝒜 ⥤ FinCell` of `G`: `F_! ⊣ F^*` is a Quillen equivalence of semi-model
categories (H Prop 2.4.16(3)), and `TopCat ⥤ FinCell̃` induces an equivalence of localizations by
the restricted Hom adjunction (H Prop 2.4.18, repaired without a model structure on spaces).
-/

/-! This file is split into the modules `HomotopyHypothesis.Blueprint.Henry.Main.Part*` so that the modules of the development form an acyclic import graph. -/
