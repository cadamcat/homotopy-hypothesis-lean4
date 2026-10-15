import HomotopyHypothesis.Approximation.Topological.NormalForm.SharpNormalFormFace
import HomotopyHypothesis.Approximation.Topological.NormalForm.VertexMapSimplexCharEqOfSharpMkEq
import HomotopyHypothesis.Approximation.Topological.NormalForm.NF
import HomotopyHypothesis.Approximation.Topological.NormalForm.Nf2
import HomotopyHypothesis.Approximation.Topological.NormalForm.SharpMkNf
import HomotopyHypothesis.Approximation.Topological.NormalForm.SemiSimplexHomExtOfSurjective

/-!
# Normal forms of formal degeneracies

Every simplex of `X♯` has a unique representative `(v, x)` with surjective vertex map `v`; the
representative of a face is obtained from that of the simplex through an increasing injection
`ι` of the image. This file chooses the normal forms and states the face relation (frozen helper
statements `sharp_normalForm_face` and `vertexMap_simplexChar_eq_of_sharpMk_eq`).
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Approximation.Topological.NormalForm.*`, one declaration per module. -/
