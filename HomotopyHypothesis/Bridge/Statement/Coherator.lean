import HomotopyHypothesis.Bridge.Statement.Back
import HomotopyHypothesis.Bridge.Statement.Equivalence
import HomotopyHypothesis.Bridge.Statement.Shapes
import HomotopyHypothesis.Bridge.Statement.Theory
import HomotopyHypothesis.Challenge
/-!
# Coherators transport

A cellular presentation of a globular theory on the statement's shapes gives a cellular
presentation of the transported theory, so coherators transport.
-/

noncomputable section

namespace HomotopyHypothesis.Bridge.Statement

open CategoryTheory

universe v

theorem conj_globe (A : Grothendieck.TheoryData.{v}) {n : ℕ} {T T' : Grothendieck.Shape}
    (q : T' = T) (x : A.Hom (Grothendieck.Shape.globe n) T) :
    conj A (eS (Grothendieck.Shape.globe n)) q x = A.comp x (A.base (eqToHom q.symm)) := by
  unfold conj
  rw [show A.base (eqToHom (eS (Grothendieck.Shape.globe n))) =
    A.id (Grothendieck.Shape.globe n) from A.base_id _]
  exact A.id_comp _

theorem parallel_comp {A : Grothendieck.GlobularTheory.{v}} {S T : Grothendieck.Shape} (n : ℕ)
    (s t : A.Hom (Grothendieck.Shape.globe n) S) (w : A.Hom S T) (h : A.Parallel n s t) :
    A.Parallel n (A.comp s w) (A.comp t w) := by
  cases n with
  | zero => trivial
  | succ k =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨by rw [← A.assoc, ← A.assoc, h1], by rw [← A.assoc, ← A.assoc, h2]⟩

/-- Admissible pairs transport. -/
def pairToOAI {A : Grothendieck.GlobularTheory.{v}} (p : A.AdmissiblePair) :
    (theoryToOAI A).AdmissiblePair where
  n := p.n
  arity := shapeToOAI p.arity
  height := (height_tableToOAI p.arity.2).trans_le p.height
  source := A.comp p.source (A.base (eqToHom (eS p.arity).symm))
  target := A.comp p.target (A.base (eqToHom (eS p.arity).symm))
  parallel := (parallel_theoryToOAI_iff p.n _ _).2 (parallel_comp p.n p.source p.target _ p.parallel)

/-- Fillers transport. -/
def fillerToOAI {A : Grothendieck.GlobularTheory.{v}} {k : ℕ} {T : Grothendieck.Shape}
    (z : A.Hom (Grothendieck.Shape.globe k) T) :
    (theoryToOAI A).Hom (OAI.Grothendieck.Shape.globe k) (shapeToOAI T) :=
  A.comp z (A.base (eqToHom (eS T).symm))

theorem fills_toOAI {A D : Grothendieck.GlobularTheory.{v}}
    (f : Grothendieck.GlobularTheory.Morphism A D) (p : A.AdmissiblePair)
    (z : D.Hom (Grothendieck.Shape.globe (p.n + 1)) p.arity)
    (hz : Grothendieck.GlobularTheory.Fills f p z) :
    OAI.Grothendieck.GlobularTheory.Fills (morphToOAI f) (pairToOAI p) (fillerToOAI z) := by
  have h1 : D.comp (D.base (Grothendieck.Shape.face (Nat.lt_succ_self p.n) false)) z =
      f.map p.source := hz.1
  have h2 : D.comp (D.base (Grothendieck.Shape.face (Nat.lt_succ_self p.n) true)) z =
      f.map p.target := hz.2
  change D.comp (D.base (shapeFunctor.map
        (OAI.Grothendieck.Shape.face (Nat.lt_succ_self p.n) false)))
        (D.comp z (D.base (eqToHom (eS p.arity).symm))) =
      f.map (A.comp p.source (A.base (eqToHom (eS p.arity).symm))) ∧
    D.comp (D.base (shapeFunctor.map
        (OAI.Grothendieck.Shape.face (Nat.lt_succ_self p.n) true)))
        (D.comp z (D.base (eqToHom (eS p.arity).symm))) =
      f.map (A.comp p.target (A.base (eqToHom (eS p.arity).symm)))
  rw [shapeFunctor_face, shapeFunctor_face, f.map_comp, f.map_comp, f.map_base]
  exact ⟨(D.assoc _ _ _).symm.trans (congrArg (D.comp · _) h1),
    (D.assoc _ _ _).symm.trans (congrArg (D.comp · _) h2)⟩

theorem homTo_map_globe {A : Grothendieck.GlobularTheory.{v}}
    {E : OAI.Grothendieck.GlobularTheory.{v}}
    (m : OAI.Grothendieck.GlobularTheory.Morphism (theoryToOAI A) E) {k : ℕ}
    {T : Grothendieck.Shape} (z : A.Hom (Grothendieck.Shape.globe k) T) :
    (homEquiv m).map z = m.map (fillerToOAI z) :=
  congrArg m.map (conj_globe A.toTheoryData (eS T) z)

theorem fills_homEquiv {A : Grothendieck.GlobularTheory.{v}}
    {E : OAI.Grothendieck.GlobularTheory.{v}}
    (m : OAI.Grothendieck.GlobularTheory.Morphism (theoryToOAI A) E) (p : A.AdmissiblePair)
    (z : E.Hom (OAI.Grothendieck.Shape.globe (p.n + 1)) (shapeToOAI p.arity)) :
    Grothendieck.GlobularTheory.Fills (homEquiv m) p z ↔
      OAI.Grothendieck.GlobularTheory.Fills m (pairToOAI p) z := by
  change E.comp (E.base (shapeBack.map
        (Grothendieck.Shape.face (Nat.lt_succ_self p.n) false))) z = (homEquiv m).map p.source ∧
      E.comp (E.base (shapeBack.map
        (Grothendieck.Shape.face (Nat.lt_succ_self p.n) true))) z = (homEquiv m).map p.target ↔
    E.comp (E.base (OAI.Grothendieck.Shape.face (Nat.lt_succ_self p.n) false)) z =
        m.map (fillerToOAI p.source) ∧
      E.comp (E.base (OAI.Grothendieck.Shape.face (Nat.lt_succ_self p.n) true)) z =
        m.map (fillerToOAI p.target)
  rw [shapeBack_face, shapeBack_face, homTo_map_globe, homTo_map_globe]
  exact Iff.rfl

theorem homEquiv_eq_iff {A B : Grothendieck.GlobularTheory.{v}}
    {E : OAI.Grothendieck.GlobularTheory.{v}} (f : Grothendieck.GlobularTheory.Morphism A B)
    (b : OAI.Grothendieck.GlobularTheory.Morphism (theoryToOAI B) E)
    (a : OAI.Grothendieck.GlobularTheory.Morphism (theoryToOAI A) E) :
    (morphToOAI f).comp b = a ↔ f.comp (homEquiv b) = homEquiv a := by
  rw [← homEquiv_comp]
  exact homEquiv.apply_eq_iff_eq.symm

/-- Cellular presentations transport. -/
def cellularPresentationToOAI {C : Grothendieck.GlobularTheory.{v}}
    (P : C.CellularPresentation) : (theoryToOAI C).CellularPresentation where
  stage r := theoryToOAI (P.stage r)
  initial D := (P.initial (theoryOfOAI D)).map fun u => @Equiv.unique _ _ u homEquiv
  step r := morphToOAI (P.step r)
  generators := P.generators
  pair r g := pairToOAI (P.pair r g)
  filler r g := fillerToOAI (P.filler r g)
  free r := by
    refine ⟨fun g => fills_toOAI _ _ _ ((P.free r).1 g), fun E a chosen hchosen => ?_⟩
    have H := (P.free r).2 (theoryOfOAI E) (homEquiv a) chosen
      (fun g => (fills_homEquiv a (P.pair r g) (chosen g)).2 (hchosen g))
    refine (homEquiv.existsUnique_congr fun b => ?_).2 H
    refine and_congr (homEquiv_eq_iff _ _ _) (forall_congr' fun g => ?_)
    exact (congrArg (fun w => w = chosen g) (homTo_map_globe b (P.filler r g))).symm.to_iff
  inclusion r := morphToOAI (P.inclusion r)
  compatible r := congrArg morphToOAI (P.compatible r)
  colimit D a ha := by
    have H := P.colimit (theoryOfOAI D) (fun r => homEquiv (a r))
      (fun r => (homEquiv_eq_iff _ _ _).1 (ha r))
    exact (homEquiv.existsUnique_congr fun b =>
      forall_congr' fun r => homEquiv_eq_iff _ _ _).2 H

theorem cellularPresentation_theoryToOAI {C : Grothendieck.GlobularTheory.{v}}
    (P : C.CellularPresentation) : Nonempty (theoryToOAI C).CellularPresentation :=
  ⟨cellularPresentationToOAI P⟩

theorem isCoherator_theoryToOAI {C : Grothendieck.GlobularTheory.{v}} (hC : C.IsCoherator) :
    (theoryToOAI C).IsCoherator :=
  ⟨hC.1.elim cellularPresentation_theoryToOAI, fillers_theoryToOAI hC⟩

end HomotopyHypothesis.Bridge.Statement
