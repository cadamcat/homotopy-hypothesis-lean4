import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.DiskBoundaryIsFiniteCellComplex
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.CompactSpaceOfIsFiniteCellComplex
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.IsCellularRealizationFinCellIota
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.FinCellEssentiallySmall
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeFiniteCellComplexHomotopyExtension
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeLiftOfHomotopyEquivalence
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.HomotopyEquivalenceOfIsPushout
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeLiftOfWeakEquivalence
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.ExistsFactorizationOfCompactSpace
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.FinCellHomotopicRelIff

/-!
# Packages: finite cell complexes and relative homotopy classes

The classical topology used to compare spaces with the completion of the cylinder category of finite
cell complexes, without a model structure on spaces: finite cell complexes (finitely many cells
attached along arbitrary continuous maps, in any order of dimensions), the homotopy extension
property of relative finite cell complexes, the transport of relative homotopy classes along
homotopy equivalences and along weak homotopy equivalences (the latter in the compression form used
to define `Top.weakEquivalences`), compact support in transfinite cell complexes, and the
identification of relative cylinders of finite cell complexes with homotopies relative to a
subspace.

References: A. Hatcher, *Algebraic Topology*, Ch. 0 and §4.1; R. Brown, *Topology and Groupoids*,
§§7.2–7.5; P. Hirschhorn, *The Quillen model category of topological spaces*, §4.
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Blueprint.Henry.Packages.Topology.*`, one declaration per module. -/
