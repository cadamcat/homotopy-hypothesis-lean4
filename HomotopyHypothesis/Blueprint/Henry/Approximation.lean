import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
/-!
# Geometric vocabulary for simplicial approximation in semi-simplicial sets

Definitions used to state the steps of Rourke–Sanderson's relative simplicial approximation
theorem for semi-simplicial sets (C. P. Rourke, B. J. Sanderson, *Δ-sets I: homotopy theory*,
Q. J. Math. 22 (1971), §§4–5) and Zeeman's relative simplicial approximation theorem
(E. C. Zeeman, *Relative simplicial approximation*, Proc. Camb. Phil. Soc. 60 (1964)):

* finite semi-simplicial sets;
* the characteristic map `|Δ^n| ⟶ ‖Y‖` of a simplex and the affine map `|Δ^n| ⟶ |Δ^m|` of an
  arbitrary vertex map;
* the formal degeneracies `X♯` of a semi-simplicial set (vertex maps need not be injective or
  monotone) and simplicial maps `‖Y‖ ⟶ ‖X‖`: maps given coherently, by a map `Y ⟶ X♯`, on each
  simplex by the affine extension of a vertex map into a simplex of `X`;
* linear embeddings of simplices and subdivisions relative to a semi-simplicial subset `J`, together
  with a prism between the subdivision and the original set that is pinched over `J` and collapses
  onto the subdivided end; relative prisms, which keep only the prism; the second derived
  subdivision with its prism;
* semi-simplicial sets that are ordered simplicial complexes;
* anodyne maps: finite composites of pushouts of horn inclusions (inverse collapses).
-/

universe u

open CategoryTheory Limits Opposite Convexity

namespace HomotopyHypothesis.Henry

/-- Finite nonempty ordinals `[n] = {0, …, n}` with all functions between them (the index
category of "symmetric" simplicial sets). -/
structure FinFun where
  /-- the ordinal `[n]` -/
  n : ℕ

instance : Category FinFun where
  Hom a b := Fin (a.n + 1) → Fin (b.n + 1)
  id _ := id
  comp f g := g ∘ f

/-- The inclusion of the semi-simplicial category (injective monotone maps) into `FinFun`. -/
def SemiSimplexCategory.toFinFun : SemiSimplexCategory ⥤ FinFun where
  obj X := ⟨X.obj.len⟩
  map θ := fun i => θ.1.toOrderHom i
  map_id _ := rfl
  map_comp _ _ := rfl

namespace SemiSSet

/-- The formal degeneracies `X♯` of a semi-simplicial set `X`: its left Kan extension along the
inclusion into all maps of finite ordinals, restricted back to the semi-simplicial category. An
`n`-simplex of `X♯` is represented by a pair `(v, x)` of an `m`-simplex `x` of `X` and an arbitrary
vertex map `v : [n] ⟶ [m]`, modulo the faces of `x`. -/
noncomputable def sharp (X : SemiSSet.{u}) : SemiSSet.{u} :=
  SemiSimplexCategory.toFinFun.op ⋙ SemiSimplexCategory.toFinFun.op.leftKanExtension X

/-- The inclusion `X ⟶ X♯` (simplices with identity vertex maps). -/
noncomputable def toSharp (X : SemiSSet.{u}) : X ⟶ sharp X :=
  SemiSimplexCategory.toFinFun.op.leftKanExtensionUnit X

/-- The simplex of `X♯` represented by a vertex map `v : [n] ⟶ [m]` and an `m`-simplex of `X`. -/
noncomputable def sharpMk {X : SemiSSet.{u}} {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (x : X.obj (op (SemiSimplexCategory.mk m))) : (sharp X).obj (op (SemiSimplexCategory.mk n)) :=
  (SemiSimplexCategory.toFinFun.op.leftKanExtension X).map
    (Quiver.Hom.op (show (⟨n⟩ : FinFun) ⟶ ⟨m⟩ from v)) ((toSharp X).app _ x)

/-- A finite semi-simplicial set: finitely many simplices in each dimension and none above some
dimension. -/
def IsFinite (X : SemiSSet.{u}) : Prop :=
  (∀ n : ℕ, Finite (X.obj (op (SemiSimplexCategory.mk n)))) ∧
    ∃ N : ℕ, ∀ n : ℕ, N < n → IsEmpty (X.obj (op (SemiSimplexCategory.mk n)))

/-- The characteristic map `|Δ^n| ⟶ ‖Y‖` of an `n`-simplex `y` of `Y`. -/
noncomputable def simplexChar {Y : SemiSSet.{u}} {n : ℕ}
    (y : stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ Y) :
    toTop.obj (SemiSimplexCategory.mk n) ⟶ realization.obj Y :=
  (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app (SemiSimplexCategory.mk n) ≫
    realization.map y

/-- The affine map `|Δ^n| ⟶ |Δ^m|` extending a vertex map `Fin (n + 1) → Fin (m + 1)` (not
necessarily injective or order preserving). -/
noncomputable def vertexMap {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    toTop.{u}.obj (SemiSimplexCategory.mk n) ⟶ toTop.{u}.obj (SemiSimplexCategory.mk m) :=
  TopCat.uliftFunctor.{u}.map
    (TopCat.ofHom ⟨StdSimplex.map (R := ℝ) v, StdSimplex.continuous_map ℝ v⟩)

/-- The `i`-th vertex of the topological simplex `|Δ^n|`. -/
noncomputable def simplexVertex {n : ℕ} (i : Fin (n + 1)) :
    toTop.{u}.obj (SemiSimplexCategory.mk n) :=
  ULift.up (StdSimplex.single (R := ℝ) i)

/-- A continuous map `f : ‖Y‖ ⟶ ‖X‖` is simplicial (Rourke–Sanderson §4) if it is, coherently,
on every simplex of `Y` the affine extension of a vertex map into some simplex of `X`: there is a
map of semi-simplicial sets `φ : Y ⟶ X♯` into the formal degeneracies of `X` such that the
realization of every simplex `y` of `Y` composed with `f` is `|v| ≫ |x|` for a representative
`(v, x)` of `φ y`. (Different representatives of `φ y` give the same affine map.) -/
def IsSimplicial {Y X : SemiSSet.{u}} (f : realization.obj Y ⟶ realization.obj X) : Prop :=
  ∃ φ : Y ⟶ sharp X, ∀ (n : ℕ) (y : stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ Y),
    ∃ (m : ℕ) (x : stdSimplex.obj (SemiSimplexCategory.mk m) ⟶ X)
      (v : Fin (n + 1) → Fin (m + 1)),
      φ.app (op (SemiSimplexCategory.mk n)) (uliftYonedaEquiv y) = sharpMk v (uliftYonedaEquiv x) ∧
        simplexChar y ≫ f = vertexMap v ≫ simplexChar x

/-- An injective affine map `|Δ^n| ⟶ |Δ^m|`. -/
def IsLinearEmbedding {n m : ℕ}
    (e : toTop.{u}.obj (SemiSimplexCategory.mk n) ⟶ toTop.{u}.obj (SemiSimplexCategory.mk m)) :
    Prop :=
  IsAffineMap ℝ (fun x : StdSimplex ℝ (Fin (n + 1)) =>
    (ULift.down (e.hom (ULift.up x)) : StdSimplex ℝ (Fin (m + 1)))) ∧
    Function.Injective e.hom

/-- A semi-simplicial set is an ordered simplicial complex: the vertices of each simplex are
distinct points of the realization, and a simplex is determined by its set of vertices. -/
def IsSimplicialComplex (K : SemiSSet.{u}) : Prop :=
  (∀ (n : ℕ) (σ : stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ K),
    Function.Injective fun i : Fin (n + 1) => (simplexChar σ).hom (simplexVertex i)) ∧
  ∀ (n : ℕ) (σ τ : stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ K),
    (Set.range fun i : Fin (n + 1) => (simplexChar σ).hom (simplexVertex i)) =
      (Set.range fun i : Fin (n + 1) => (simplexChar τ).hom (simplexVertex i)) → σ = τ

/-- The horn inclusions `Λ^{n+1}_k ⟶ Δ_{n+1}`. -/
def hornInclusions : MorphismProperty SemiSSet.{u} :=
  MorphismProperty.ofHoms fun p : Σ n : ℕ, Fin (n + 2) => (horn.{u} (p.1 + 1) p.2).ι

/-- Anodyne maps: finite composites of isomorphisms and pushouts of horn inclusions. An elementary
collapse `X ↘ X − {σ, τ}` (`τ` a free face of `σ`) is the inverse of such a pushout, so `j` is
anodyne exactly when its target collapses onto its image (Rourke–Sanderson §4). -/
def anodyne : MorphismProperty SemiSSet.{u} :=
  (hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}).multiplicativeClosure

/-- A subdivision `Y'` of `Y` relative to a semi-simplicial subset `J` (Rourke–Sanderson §4, with
`J` not subdivided), together with a prism `C` between `Y'` and `Y`:

* `h : ‖Y'‖ ≅ ‖Y‖` maps each simplex of `Y'` by a linear embedding into a simplex of `Y`;
* `j : J ⟶ Y'` is the unsubdivided copy of `J`, with `‖j‖ ≫ h = ‖J ↪ Y‖`;
* `C` contains `Y'` (by the anodyne map `c₀`, i.e. `C` collapses onto `Y'`) and `Y` (by `c₁`),
  the two copies of `J` being identified (the prism is pinched over `J`);
* `ρ : ‖C‖ ⟶ ‖Y'‖` projects the prism onto its subdivided end, the original end going by `h⁻¹`.

Such prisms are built from the derived cylinders of Rourke–Sanderson, Lemma 4.3. -/
structure RelSubdivision (Y : SemiSSet.{u}) (J : Subfunctor Y) where
  /-- the subdivided semi-simplicial set -/
  Y' : SemiSSet.{u}
  finite : Y'.IsFinite
  /-- the identification of the realizations -/
  h : realization.obj Y' ≅ realization.obj Y
  linear : ∀ (n : ℕ) (y' : stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ Y'),
    ∃ (m : ℕ) (y : stdSimplex.obj (SemiSimplexCategory.mk m) ⟶ Y)
      (e : toTop.obj (SemiSimplexCategory.mk n) ⟶ toTop.obj (SemiSimplexCategory.mk m)),
      IsLinearEmbedding e ∧ simplexChar y' ≫ h.hom = e ≫ simplexChar y
  /-- the unsubdivided copy of `J` -/
  j : J.toFunctor ⟶ Y'
  mono_j : Mono j
  hj : realization.map j ≫ h.hom = realization.map J.ι
  /-- the prism between `Y'` and `Y`, pinched over `J` -/
  C : SemiSSet.{u}
  /-- the subdivided end of the prism -/
  c₀ : Y' ⟶ C
  /-- the original end of the prism -/
  c₁ : Y ⟶ C
  hc : j ≫ c₀ = J.ι ≫ c₁
  anodyne_c₀ : anodyne c₀
  /-- the projection of the prism onto its subdivided end -/
  ρ : realization.obj C ⟶ realization.obj Y'
  hρ₀ : realization.map c₀ ≫ ρ = 𝟙 _
  hρ₁ : realization.map c₁ ≫ ρ = h.inv

/-- A relative prism of `Y` relative to `J`: a finite semi-simplicial set `Y'` containing an
unsubdivided copy of `J`, and a prism `C` containing `Y'` and `Y`, pinched over `J`, which
collapses onto `Y'`, with a retraction `ρ` of the realized collapse. Unlike a relative subdivision,
`‖Y'‖` is not identified with `‖Y‖`: when the target of an approximation is subdivided, `J` has to
be subdivided too, and the unsubdivided copy of `J` is reattached through a collar. -/
structure RelPrism (Y : SemiSSet.{u}) (J : Subfunctor Y) where
  /-- the resolved semi-simplicial set -/
  Y' : SemiSSet.{u}
  finite : Y'.IsFinite
  /-- the unsubdivided copy of `J` -/
  j : J.toFunctor ⟶ Y'
  mono_j : Mono j
  /-- the prism between `Y'` and `Y`, pinched over `J` -/
  C : SemiSSet.{u}
  /-- the end `Y'` of the prism -/
  c₀ : Y' ⟶ C
  /-- the end `Y` of the prism -/
  c₁ : Y ⟶ C
  hc : j ≫ c₀ = J.ι ≫ c₁
  anodyne_c₀ : anodyne c₀
  /-- a retraction of the realized collapse -/
  ρ : realization.obj C ⟶ realization.obj Y'
  hρ₀ : realization.map c₀ ≫ ρ = 𝟙 _

/-- A relative subdivision is a relative prism. -/
@[simps]
def RelSubdivision.toRelPrism {Y : SemiSSet.{u}} {J : Subfunctor Y} (S : RelSubdivision Y J) :
    RelPrism Y J where
  Y' := S.Y'
  finite := S.finite
  j := S.j
  mono_j := S.mono_j
  C := S.C
  c₀ := S.c₀
  c₁ := S.c₁
  hc := S.hc
  anodyne_c₀ := S.anodyne_c₀
  ρ := S.ρ
  hρ₀ := S.hρ₀

/-- The second derived subdivision `F` (Rourke–Sanderson §4) with its prism:

* `e : ‖F W‖ ≅ ‖W‖` natural and the natural last vertex map `lv`, carrying each simplex of `F W`
  linearly, respectively through a vertex map, into one and the same simplex of `W`; `F` preserves
  finiteness and monomorphisms, and `F W` is an ordered simplicial complex for finite `W`;
* `H`, the natural straight-line homotopy from `lv` to `e`;
* a natural prism `P W` with ends `F W` (`top`) and `W` (`bot`), collapsing onto `F W` relative to
  the prism over any `J ⊆ W` (two derived cylinders, each collapsing onto its derived end);
* `pr : ‖P W‖ ⟶ ‖W‖`, simplicial, equal to `lv` on `F W` and to the identity on `W`; `πe`, equal to
  `e` on `F W` and to the identity on `W`; and `K`, a homotopy from `pr` to `πe` relative to `W`,
  equal to `H` on `F W`. -/
structure DerivedSubdivision where
  /-- the second derived subdivision -/
  F : SemiSSet.{u} ⥤ SemiSSet.{u}
  e : F ⋙ realization ≅ realization
  /-- the last vertex map -/
  lv : F ⋙ realization ⟶ realization
  finite_complex : ∀ W : SemiSSet.{u}, W.IsFinite →
    (F.obj W).IsFinite ∧ (F.obj W).IsSimplicialComplex
  mono_map : ∀ {A B : SemiSSet.{u}} (φ : A ⟶ B), Mono φ → Mono (F.map φ)
  simplex : ∀ (W : SemiSSet.{u}) (n : ℕ) (y : stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ F.obj W),
    ∃ (m : ℕ) (w : stdSimplex.obj (SemiSimplexCategory.mk m) ⟶ W)
      (le : toTop.obj (SemiSimplexCategory.mk n) ⟶ toTop.obj (SemiSimplexCategory.mk m))
      (v : Fin (n + 1) → Fin (m + 1)),
      IsLinearEmbedding le ∧ simplexChar y ≫ e.hom.app W = le ≫ simplexChar w ∧
        simplexChar y ≫ lv.app W = vertexMap v ≫ simplexChar w
  /-- the straight-line homotopy from `lv` to `e` -/
  H : ∀ W : SemiSSet.{u}, ContinuousMap.Homotopy (lv.app W).hom (e.hom.app W).hom
  H_natural : ∀ {W W' : SemiSSet.{u}} (φ : W ⟶ W') (t : unitInterval)
    (x : realization.obj (F.obj W)),
    H W' (t, (realization.map (F.map φ)).hom x) = (realization.map φ).hom (H W (t, x))
  /-- the prism between `F W` and `W` -/
  P : SemiSSet.{u} ⥤ SemiSSet.{u}
  top : F ⟶ P
  bot : 𝟭 SemiSSet.{u} ⟶ P
  mono_bot : ∀ W : SemiSSet.{u}, Mono (bot.app W)
  finite_P : ∀ W : SemiSSet.{u}, W.IsFinite → (P.obj W).IsFinite
  anodyne_top : ∀ (W : SemiSSet.{u}) (J : Subfunctor W), W.IsFinite →
    anodyne (pushout.desc (top.app W) (P.map J.ι) (top.naturality J.ι) :
      pushout (F.map J.ι) (top.app J.toFunctor) ⟶ P.obj W)
  /-- the simplicial projection of the prism -/
  pr : P ⋙ realization ⟶ realization
  pr_simplex : ∀ (W : SemiSSet.{u}) (n : ℕ)
    (z : stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ P.obj W),
    ∃ (m : ℕ) (w : stdSimplex.obj (SemiSimplexCategory.mk m) ⟶ W)
      (v : Fin (n + 1) → Fin (m + 1)), simplexChar z ≫ pr.app W = vertexMap v ≫ simplexChar w
  top_pr : ∀ W : SemiSSet.{u}, realization.map (top.app W) ≫ pr.app W = lv.app W
  bot_pr : ∀ W : SemiSSet.{u}, realization.map (bot.app W) ≫ pr.app W = 𝟙 _
  /-- the affine projection of the prism -/
  πe : P ⋙ realization ⟶ realization
  top_πe : ∀ W : SemiSSet.{u}, realization.map (top.app W) ≫ πe.app W = e.hom.app W
  bot_πe : ∀ W : SemiSSet.{u}, realization.map (bot.app W) ≫ πe.app W = 𝟙 _
  /-- the straight-line homotopy from `pr` to `πe` -/
  K : ∀ W : SemiSSet.{u}, ContinuousMap.HomotopyRel (pr.app W).hom (πe.app W).hom
    (Set.range (realization.map (bot.app W)).hom)
  K_top : ∀ (W : SemiSSet.{u}) (t : unitInterval) (x : realization.obj (F.obj W)),
    K W (t, (realization.map (top.app W)).hom x) = H W (t, x)

end SemiSSet

end HomotopyHypothesis.Henry
