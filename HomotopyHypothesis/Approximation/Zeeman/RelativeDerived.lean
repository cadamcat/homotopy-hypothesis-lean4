import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.RelativePrism
/-!
# Combinatorics of relative derived subdivision

The vertices of a derived subdivision modulo a subcomplex are the vertices
of the subcomplex and the barycentres of simplices outside it. A simplex
consists of an ordered face of the subcomplex followed by a strictly nested
chain of exterior faces containing that face.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- All simplices, with their dimensions retained. -/
abbrev Simplex (K : SemiSSet.{u}) :=
  Σ n : ℕ, K.obj (op (Henry.SemiSimplexCategory.mk n))

/-- The inclusion of one vertex of a simplex. -/
def vertexInclusion {n : ℕ} (i : Fin (n + 1)) :
    Henry.SemiSimplexCategory.mk 0 ⟶ Henry.SemiSimplexCategory.mk n :=
  ⟨SimplexCategory.const _ _ i, by
    change Mono (SimplexCategory.const _ _ i)
    rw [SimplexCategory.mono_iff_injective]
    change Function.Injective (fun _ : Fin 1 => i)
    exact fun _ _ _ => Subsingleton.elim _ _⟩

/-- The combinatorial vertex of a simplex. -/
def vertex {K : SemiSSet.{u}} {n : ℕ}
    (x : K.obj (op (Henry.SemiSimplexCategory.mk n))) (i : Fin (n + 1)) :
    K.obj (op (Henry.SemiSimplexCategory.mk 0)) :=
  K.map (vertexInclusion i).op x

/-- Vertices retained from the subcomplex and barycentres of exterior faces. -/
abbrev RelativeVertex (K : SemiSSet.{u}) (L : Subfunctor K) :=
  L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0)) ⊕
    {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))}

/-- The allowable order of two vertices in a relative derived simplex. -/
def RelativeVertex.Precedes {K : SemiSSet.{u}} {L : Subfunctor K} :
    RelativeVertex K L → RelativeVertex K L → Prop
  | .inl _, .inl _ => True
  | .inl v, .inr s => ∃ θ : Henry.SemiSimplexCategory.mk 0 ⟶
      Henry.SemiSimplexCategory.mk s.val.1, K.map θ.op s.val.2 = v.val
  | .inr _, .inl _ => False
  | .inr s, .inr t => s.val.1 < t.val.1 ∧
      ∃ θ : Henry.SemiSimplexCategory.mk s.val.1 ⟶
        Henry.SemiSimplexCategory.mk t.val.1, K.map θ.op t.val.2 = s.val.2

/-- A tuple of subdivision vertices whose retained vertices form an ordered face.
The face condition is stated for every retained subtuple so it is preserved
directly under restriction. -/
def RelativeAdmissible {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : Fin (n + 1) → RelativeVertex K L) : Prop :=
  Function.Injective a ∧
    (∀ i j : Fin (n + 1), i < j → RelativeVertex.Precedes (a i) (a j)) ∧
    ∀ (m : ℕ) (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n)
      (w : Fin (m + 1) → L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0))),
      (∀ i, a (θ.hom.toOrderHom i) = .inl (w i)) →
        ∃ x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk m)),
          ∀ i, vertex x i = w i

private theorem relativeAdmissible_restrict {K : SemiSSet.{u}} {L : Subfunctor K}
    {n m : ℕ} {a : Fin (n + 1) → RelativeVertex K L}
    (ha : RelativeAdmissible a)
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    RelativeAdmissible (a ∘ θ.hom.toOrderHom) := by
  have hθ : Function.Injective θ.hom.toOrderHom :=
    SimplexCategory.mono_iff_injective.mp θ.property
  refine ⟨ha.1.comp hθ, ?_, ?_⟩
  · intro i j hij
    exact ha.2.1 _ _ (θ.hom.toOrderHom.monotone.strictMono_of_injective hθ hij)
  · intro k η w hw
    exact ha.2.2 k (η ≫ θ) w hw

/-- The relative derived complex, described by its ordered vertex tuples. -/
def relativeDerived (K : SemiSSet.{u}) (L : Subfunctor K) : SemiSSet.{u} where
  obj X := {a : Fin (X.unop.obj.len + 1) → RelativeVertex K L // RelativeAdmissible a}
  map θ := ↾fun a =>
    ⟨a.val ∘ θ.unop.hom.toOrderHom, relativeAdmissible_restrict a.property θ.unop⟩
  map_id X := rfl
  map_comp θ η := rfl

/-- A finite semi-simplicial set has finitely many simplices in total. -/
theorem simplex_finite {K : SemiSSet.{u}} (hK : K.IsFinite) :
    Finite (Simplex K) := by
  rcases hK with ⟨hfin, N, hN⟩
  letI : ∀ n : ℕ, Finite (K.obj (op (Henry.SemiSimplexCategory.mk n))) := hfin
  have hd (s : Simplex K) : s.1 ≤ N := by
    by_contra hn
    haveI := hN s.1 (lt_of_not_ge hn)
    exact isEmptyElim s.2
  let enc : Simplex K → Σ n : Fin (N + 1),
      K.obj (op (Henry.SemiSimplexCategory.mk n.val)) :=
    fun s => ⟨⟨s.1, Nat.lt_succ_of_le (hd s)⟩, s.2⟩
  apply Finite.of_injective enc
  intro s t h
  exact congrArg (fun q : Σ n : Fin (N + 1),
      K.obj (op (Henry.SemiSimplexCategory.mk n.val)) => (⟨q.1.val, q.2⟩ : Simplex K)) h

/-- The relative derived complex has finitely many simplices. -/
theorem relativeDerived_isFinite {K : SemiSSet.{u}} (hK : K.IsFinite) (L : Subfunctor K) :
    (relativeDerived K L).IsFinite := by
  haveI : Finite (Simplex K) := simplex_finite hK
  haveI : Finite (K.obj (op (Henry.SemiSimplexCategory.mk 0))) := hK.1 0
  haveI : Finite (L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0))) := by
    change Finite {x : K.obj (op (Henry.SemiSimplexCategory.mk 0)) //
      x ∈ L.obj (op (Henry.SemiSimplexCategory.mk 0))}
    infer_instance
  haveI : Finite (RelativeVertex K L) := by
    dsimp only [RelativeVertex]
    infer_instance
  letI : Fintype (RelativeVertex K L) := Fintype.ofFinite _
  refine ⟨?_, ⟨Fintype.card (RelativeVertex K L), ?_⟩⟩
  · intro n
    change Finite {a : Fin (n + 1) → RelativeVertex K L // RelativeAdmissible a}
    infer_instance
  intro n hn
  refine ⟨fun a => ?_⟩
  have hc := Fintype.card_le_of_injective a.val a.property.1
  simp only [Fintype.card_fin] at hc
  omega

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeDerived_isFinite
