import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Carriers of relative derived simplices

Every relative derived simplex is contained in an original simplex: its
last exterior face if it has one, and its retained face otherwise. Thus
all its vertices have positions in a common simplex.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A retained vertex or exterior face lies in an original simplex. -/
def RelativeVertex.CarriedBy {K : SemiSSet.{u}} {L : Subfunctor K} {m : ℕ}
    (v : RelativeVertex K L) (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) : Prop :=
  match v with
  | .inl w => ∃ θ : Henry.SemiSimplexCategory.mk 0 ⟶ Henry.SemiSimplexCategory.mk m,
      K.map θ.op y = w.val
  | .inr s => ∃ θ : Henry.SemiSimplexCategory.mk s.val.1 ⟶ Henry.SemiSimplexCategory.mk m,
      K.map θ.op y = s.val.2

/-- All vertices of an admissible relative derived tuple lie in a common original simplex. -/
theorem exists_relativeCarrier {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : Fin (n + 1) → RelativeVertex K L) (ha : RelativeAdmissible a) :
    ∃ s : Simplex K, ∀ i, RelativeVertex.CarriedBy (a i) s.2 := by
  cases hlast : a (Fin.last n) with
  | inl v =>
    let w : Fin (n + 1) → L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0)) :=
      fun i => match a i with | .inl u => u | .inr _ => v
    have hw (i : Fin (n + 1)) : a i = .inl (w i) := by
      by_cases hi : i = Fin.last n
      · subst i
        simp only [w, hlast]
      · have hb := ha.2.1 i (Fin.last n) (lt_of_le_of_ne (Fin.le_last i) hi)
        cases he : a i with
        | inl u => simp only [w, he]
        | inr s =>
          simp only [he, hlast, RelativeVertex.Precedes] at hb
    obtain ⟨x, hx⟩ := ha.2.2 n (𝟙 _) w hw
    refine ⟨⟨n, x.val⟩, ?_⟩
    intro i
    rw [hw i]
    change ∃ θ : Henry.SemiSimplexCategory.mk 0 ⟶ Henry.SemiSimplexCategory.mk n,
      K.map θ.op x.val = (w i).val
    exact ⟨vertexInclusion i, congrArg Subtype.val (hx i)⟩
  | inr s =>
    refine ⟨s.val, ?_⟩
    intro i
    by_cases hi : i = Fin.last n
    · subst i
      rw [hlast]
      change ∃ θ : Henry.SemiSimplexCategory.mk s.val.1 ⟶
        Henry.SemiSimplexCategory.mk s.val.1, K.map θ.op s.val.2 = s.val.2
      exact ⟨𝟙 _, by simp⟩
    · have hb := ha.2.1 i (Fin.last n) (lt_of_le_of_ne (Fin.le_last i) hi)
      rw [hlast] at hb
      cases he : a i with
      | inl v =>
        simpa only [he, RelativeVertex.Precedes, RelativeVertex.CarriedBy] using hb
      | inr t =>
        simp only [he, RelativeVertex.Precedes] at hb
        simpa only [he, RelativeVertex.CarriedBy] using hb.2

/-- Choose an original carrier for a relative derived simplex. -/
noncomputable def relativeCarrier {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) : Simplex K :=
  Classical.choose (exists_relativeCarrier a.val a.property)

/-- Each vertex of the relative derived simplex is carried by its chosen carrier. -/
theorem relativeCarrier_spec {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) (i : Fin (n + 1)) :
    RelativeVertex.CarriedBy (a.val i) (relativeCarrier a).2 :=
  Classical.choose_spec (exists_relativeCarrier a.val a.property) i

/-- A carrier remains a carrier after inclusion into a larger original face. -/
theorem carriedBy_of_face {K : SemiSSet.{u}} {L : Subfunctor K} {m k : ℕ}
    {y : K.obj (op (Henry.SemiSimplexCategory.mk m))}
    {z : K.obj (op (Henry.SemiSimplexCategory.mk k))}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : K.map θ.op z = y) {v : RelativeVertex K L}
    (hv : RelativeVertex.CarriedBy v y) : RelativeVertex.CarriedBy v z := by
  cases v with
  | inl w =>
    obtain ⟨η, hη⟩ := hv
    refine ⟨η ≫ θ, ?_⟩
    rw [op_comp, K.map_comp_apply, hθ, hη]
  | inr s =>
    obtain ⟨η, hη⟩ := hv
    refine ⟨η ≫ θ, ?_⟩
    rw [op_comp, K.map_comp_apply, hθ, hη]

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_relativeCarrier
#print axioms HomotopyHypothesis.Approximation.Zeeman.carriedBy_of_face
