import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.MixedOriginalPrefix
import HomotopyHypothesis.Approximation.Zeeman.MixedPairInsertionStatement
import HomotopyHypothesis.Approximation.Zeeman.MixedPrefixIncidence
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Inserting the barycentre of an original prefix

For a mixed flag whose original prefix lies outside the fixed subcomplex,
inserting that prefix's barycentre immediately after the prefix preserves
admissibility whenever the barycentre is not already present.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Simplicial.MixedPairs

open Henry Henry.SemiSSet Approximation.Zeeman

/-- Inserting an absent value into an injective tuple yields an injective tuple. -/
theorem insertNth_injective_of_absent {n : ℕ} {α : Type*}
    (k : Fin (n + 1)) (v : α) (f : Fin n → α)
    (hf : Function.Injective f) (hv : v ∉ Set.range f) :
    Function.Injective (Fin.insertNth k v f) := by
  intro i j hij
  induction i using k.succAboveCases with
  | x =>
    induction j using k.succAboveCases with
    | x => rfl
    | p j =>
      rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hij
      exact (hv ⟨j, hij.symm⟩).elim
  | p i =>
    induction j using k.succAboveCases with
    | x =>
      rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same] at hij
      exact (hv ⟨i, hij⟩).elim
    | p j =>
      rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove] at hij
      rw [hf hij]

/-- The inserted barycentre satisfies the precedence conditions with all other vertices. -/
theorem insertNth_precedes {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : MixedOriginalPrefix a)
    (hp : p.face ∉ L.obj (op (Henry.SemiSimplexCategory.mk p.last.val)))
    (hv : (Sum.inr ⟨⟨p.last.val, p.face⟩, hp⟩ : MixedVertex K L) ∉ Set.range a.val) :
    let v : MixedVertex K L := .inr ⟨⟨p.last.val, p.face⟩, hp⟩
    let b : Fin (n + 2) → MixedVertex K L := Fin.insertNth p.last.succ v a.val
    ∀ i j : Fin (n + 2), i < j → MixedVertex.Precedes (b i) (b j) := by
  intro v b i j hij
  let k : Fin (n + 2) := p.last.succ
  induction i using k.succAboveCases with
  | x =>
    induction j using k.succAboveCases with
    | x =>
      exact (lt_irrefl _ hij).elim
    | p j₀ =>
      have hklt : k < k.succAbove j₀ := hij
      have hlt_succ : p.last < j₀ := by
        have hle := (Fin.lt_succAbove_iff_le_castSucc k j₀).mp hklt
        change p.last.val + 1 ≤ j₀.val at hle
        exact Fin.lt_def.mpr (by omega)
      cases hs : a.val j₀ with
      | inl w =>
        have hle := (p.maximal j₀).mp ⟨w, hs⟩
        have hlt_val : p.last.val < j₀.val := hlt_succ
        have hle_val : j₀.val ≤ p.last.val := hle
        omega
      | inr s =>
        dsimp only [b]
        rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, hs]
        dsimp only [v, MixedVertex.Precedes]
        refine ⟨mixedOriginalPrefix_dim_lt_exterior_of_absent hK a p hp hv j₀ s hs, ?_⟩
        obtain ⟨θ, hθ, _⟩ := mixedOriginalPrefix_faceMap_to_exterior hK a p j₀ s hs
        exact ⟨θ, hθ⟩
  | p i₀ =>
    induction j using k.succAboveCases with
    | x =>
      have hlt_k : k.succAbove i₀ < k := hij
      have hle_cast : i₀.castSucc < k :=
        (Fin.succAbove_lt_iff_castSucc_lt k i₀).mp hlt_k
      have hle_val : i₀.val ≤ p.last.val := by
        change i₀.val < p.last.val + 1 at hle_cast
        omega
      let i₁ : Fin (p.last.val + 1) := ⟨i₀.val, Nat.lt_succ_of_le hle_val⟩
      have hi₁ : (initialSegmentInclusion p.last).hom.toOrderHom i₁ = i₀ := by
        apply Fin.ext
        rfl
      have hai₀ : a.val i₀ = Sum.inl (vertex p.face i₁) := by
        rw [← hi₁]
        exact p.vertices i₁
      dsimp only [b]
      rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same, hai₀]
      dsimp only [v, MixedVertex.Precedes]
      refine ⟨vertexInclusion i₁, ?_⟩
      rfl
    | p j₀ =>
      have hij₀ : i₀ < j₀ := (Fin.succAboveOrderEmb k).lt_iff_lt.mp hij
      dsimp only [b]
      rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
      exact a.property.2.1 i₀ j₀ hij₀

/-- Every original subtuple factors through the omission of the inserted exterior barycentre. -/
theorem insertNth_simplex_admissible {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : MixedOriginalPrefix a)
    (hp : p.face ∉ L.obj (op (Henry.SemiSimplexCategory.mk p.last.val))) :
    let v : MixedVertex K L := .inr ⟨⟨p.last.val, p.face⟩, hp⟩
    let b : Fin (n + 2) → MixedVertex K L := Fin.insertNth p.last.succ v a.val
    ∀ (m : ℕ) (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk (n + 1))
      (w : Fin (m + 1) → K.obj (op (Henry.SemiSimplexCategory.mk 0))),
      (∀ i, b (θ.hom.toOrderHom i) = Sum.inl (w i)) →
        ∃ x : K.obj (op (Henry.SemiSimplexCategory.mk m)), ∀ i, vertex x i = w i := by
  intro v b m θ w hw
  let k : Fin (n + 2) := p.last.succ
  have hne (i : Fin (m + 1)) : θ.hom.toOrderHom i ≠ k := by
    intro heq
    have hval := hw i
    dsimp only [b] at hval
    rw [heq, Fin.insertNth_apply_same] at hval
    exact Sum.inr_ne_inl hval
  have hj (i : Fin (m + 1)) : ∃ j : Fin (n + 1), k.succAbove j = θ.hom.toOrderHom i := by
    have hmem : θ.hom.toOrderHom i ∈ ({k} : Set (Fin (n + 2)))ᶜ := hne i
    rw [← Fin.range_succAboveOrderEmb k] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj⟩
  choose f hf using hj
  have hf_mono : StrictMono f := by
    intro i₁ i₂ hlt
    have hθ_mono : θ.hom.toOrderHom i₁ < θ.hom.toOrderHom i₂ :=
      θ.hom.toOrderHom.monotone.strictMono_of_injective
        (SimplexCategory.mono_iff_injective.mp θ.property) hlt
    rw [← hf i₁, ← hf i₂] at hθ_mono
    exact (Fin.succAboveOrderEmb k).lt_iff_lt.mp hθ_mono
  let ψ_hom : SimplexCategory.mk m ⟶ SimplexCategory.mk n :=
    SimplexCategory.Hom.mk ⟨f, hf_mono.monotone⟩
  have hmono : Mono ψ_hom := by
    change Mono (show SimplexCategory.mk m ⟶ SimplexCategory.mk n from
      SimplexCategory.Hom.mk ⟨f, hf_mono.monotone⟩)
    rw [SimplexCategory.mono_iff_injective]
    exact hf_mono.injective
  let ψ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n :=
    ⟨ψ_hom, hmono⟩
  have haw (i : Fin (m + 1)) : a.val (ψ.hom.toOrderHom i) = Sum.inl (w i) := by
    change a.val (f i) = Sum.inl (w i)
    have hb := hw i
    dsimp only [b] at hb
    rw [← hf i, Fin.insertNth_apply_succAbove] at hb
    exact hb
  exact a.property.2.2 m ψ w haw

/-- Inserting an absent exterior prefix barycentre immediately after the prefix yields an admissible mixed flag. -/
theorem mixedPairInsertionStatement_proof : MixedPairInsertionStatement.{u} := by
  intro K hK L n a p hp v hv
  refine ⟨?_, ?_, ?_⟩
  · exact insertNth_injective_of_absent p.last.succ v a.val a.property.1 hv
  · exact insertNth_precedes hK a p hp hv
  · exact insertNth_simplex_admissible a p hp

example : MixedPairInsertionStatement.{u} :=
  mixedPairInsertionStatement_proof

end HomotopyHypothesis.Simplicial.MixedPairs

#print axioms HomotopyHypothesis.Simplicial.MixedPairs.mixedPairInsertionStatement_proof
