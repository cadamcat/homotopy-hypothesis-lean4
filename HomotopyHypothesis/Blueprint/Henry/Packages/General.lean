import HomotopyHypothesis.Blueprint.Henry.Packages.General.IsPreCylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.General.WeakEquivalenceCobaseChange
import HomotopyHypothesis.Blueprint.Henry.Packages.General.RelHomotopicEquivalence
import HomotopyHypothesis.Blueprint.Henry.Packages.General.WeakEquivalenceIff
import HomotopyHypothesis.Blueprint.Henry.Packages.General.IsAcyclicId
import HomotopyHypothesis.Blueprint.Henry.Packages.General.IsAcyclicTwoOutOfSix
import HomotopyHypothesis.Blueprint.Henry.Packages.General.CompletionIsSemiModelCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.General.LocalizationOfIsQuillenEquivalence
import HomotopyHypothesis.Blueprint.Henry.Packages.General.ToTerminalCatIsLiftingTarget
import HomotopyHypothesis.Blueprint.Henry.Packages.General.PathObjIsLiftingTarget
import HomotopyHypothesis.Blueprint.Henry.Packages.General.IsAcyclicIffOfIsCylinderCoherator
import HomotopyHypothesis.Blueprint.Henry.Packages.General.SliceObjIsLiftingTarget
import HomotopyHypothesis.Blueprint.Henry.Packages.General.SliceObjForgetIsAcyclicIff

/-!
# Packages: the general theory of cylinder categories

Results of H §2 (cylinder categories, acyclic morphisms, completion) and H §4 (pre-fibrations,
path categories, homotopy slices) used on the way to the comparison with spaces; each is proved in the module
it imports. Each docstring names the source (`H:<line>`) and the repair it includes.
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Blueprint.Henry.Packages.General.*`, one declaration per module. -/
