import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
/-!
# Ordered simplicial complexes as semi-simplicial sets

An ordered simplicial complex on a linearly ordered vertex type `V`, given by a downward closed
family `S` of finite vertex sets, is the semi-simplicial set whose `k`-simplices are the strictly
increasing maps `[k] ⟶ V` with image in `S`; faces are restrictions.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The underlying monotone map of a map of the semi-simplicial category is strictly monotone. -/
theorem SemiSimplexCategory.strictMono {X Y : Henry.SemiSimplexCategory} (θ : X ⟶ Y) :
    StrictMono θ.1.toOrderHom := by
  have : Mono θ.1 := θ.2
  exact θ.1.toOrderHom.monotone.strictMono_of_injective
    (SimplexCategory.mono_iff_injective.1 this)

/-- A downward closed family of finite subsets of `V`. -/
structure Complex (V : Type) [LinearOrder V] where
  /-- the simplices, as vertex sets -/
  S : Finset V → Prop
  down : ∀ ⦃A B : Finset V⦄, A ⊆ B → S B → S A

variable {V : Type} [LinearOrder V]

/-- The simplices of dimension `k` of an ordered simplicial complex. -/
def Complex.Simplex (K : Complex V) (k : ℕ) : Type :=
  {f : Fin (k + 1) → V // StrictMono f ∧ K.S (Finset.univ.image f)}

/-- The semi-simplicial set of an ordered simplicial complex. -/
def Complex.toSemiSSet (K : Complex V) : SemiSSet.{u} where
  obj k := ULift.{u} (K.Simplex k.unop.obj.len)
  map {k k'} θ := TypeCat.ofHom fun σ => ULift.up (show K.Simplex k'.unop.obj.len from
    ⟨σ.down.1 ∘ θ.unop.1.toOrderHom, σ.down.2.1.comp (SemiSimplexCategory.strictMono θ.unop),
      K.down (by
        intro a ha
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply] at ha ⊢
        obtain ⟨i, rfl⟩ := ha
        exact ⟨_, rfl⟩) σ.down.2.2⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A map of ordered simplicial complexes: a vertex map that is strictly monotone on every simplex
and sends simplices to simplices. -/
structure Complex.Hom {V' : Type} [LinearOrder V'] (K : Complex V) (K' : Complex V') where
  /-- the vertex map -/
  f : V → V'
  strictMonoOn : ∀ A, K.S A → StrictMonoOn f A
  map_S : ∀ A, K.S A → K'.S (A.image f)

/-- The map of semi-simplicial sets induced by a map of ordered simplicial complexes. -/
def Complex.Hom.toSemiSSet {V' : Type} [LinearOrder V'] {K : Complex V} {K' : Complex V'}
    (φ : K.Hom K') : K.toSemiSSet.{u} ⟶ K'.toSemiSSet.{u} where
  app k := TypeCat.ofHom fun σ => ULift.up (show K'.Simplex k.unop.obj.len from
    ⟨φ.f ∘ σ.down.1, by
      intro a b hab
      apply φ.strictMonoOn _ σ.down.2.2
      · simp
      · simp
      · exact σ.down.2.1 hab,
     by
      have := φ.map_S _ σ.down.2.2
      simpa [Finset.image_image] using this⟩)
  naturality _ _ _ := rfl

/-- The `n`-simplex of an ordered simplicial complex given by a strictly increasing map. -/
def Complex.simplexMap (K : Complex V) {n : ℕ} (f : Fin (n + 1) → V) (hf : StrictMono f)
    (hS : K.S (Finset.univ.image f)) :
    stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ K.toSemiSSet.{u} :=
  uliftYonedaEquiv.symm (show ULift.{u} (K.Simplex n) from ULift.up ⟨f, hf, hS⟩)

end HomotopyHypothesis.Approximation.Topological
