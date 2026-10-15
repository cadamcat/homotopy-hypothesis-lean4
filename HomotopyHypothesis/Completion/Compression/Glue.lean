import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Completion.Compression.DiskCube
import HomotopyHypothesis.Completion.Compression.Transport
/-
# Face-gluing for injectivity on higher homotopy groups

To show `f` induces injections on `π_{n+1}`, two cube loops with homotopic
images are glued (along faces, affine and explicit) into a cube-boundary map
that extends over the cube, is transported to a disk square, filled by Henry's
property, and transported back to a homotopy of the original loops.
-/
noncomputable section

namespace HomotopyHypothesis.Completion.Compression

universe u

open CategoryTheory TopCat Topology

/-! ### The glued cube-boundary map -/

/-- Restriction dropping the last coordinate. -/
def glueRest (n : ℕ) (c : Fin (n + 2) → unitInterval) : Fin (n + 1) → unitInterval :=
  fun j => c j.castSucc

/-- Last coordinate, as a real number. -/
def glueLast (n : ℕ) (c : Fin (n + 2) → unitInterval) : ℝ :=
  ((c (Fin.last (n + 1))).val : ℝ)

lemma continuous_glueRest (n : ℕ) :
    Continuous (fun z : ↥(Cube.boundary (Fin (n + 2))) => glueRest n z.val) := by
  rw [continuous_pi_iff]
  intro j
  show Continuous fun (a : ↥(Cube.boundary (Fin (n + 2)))) => (a.val) (Fin.castSucc j)
  exact (continuous_apply _).comp continuous_subtype_val

lemma continuous_glueLast (n : ℕ) :
    Continuous (fun z : ↥(Cube.boundary (Fin (n + 2))) =>
      glueLast n z.val) := by
  show Continuous fun (z : ↥(Cube.boundary (Fin (n + 2)))) =>
    (((z.val (Fin.last (n + 1))).val : ℝ))
  exact continuous_subtype_val.comp
    ((continuous_apply (Fin.last (n + 1))).comp continuous_subtype_val)

/-- The bottom closed half (in the boundary subtype). -/
def glueBot (n : ℕ) : Set ↥(Cube.boundary (Fin (n + 2))) :=
  {z | glueLast n z.val ≤ 1 / 2}

/-- The top closed half. -/
def glueTop (n : ℕ) : Set ↥(Cube.boundary (Fin (n + 2))) :=
  {z | (1 : ℝ) / 2 ≤ glueLast n z.val}

lemma isClosed_glueBot (n : ℕ) : IsClosed (glueBot n) :=
  IsClosed.preimage (continuous_glueLast n) isClosed_Iic

lemma isClosed_glueTop (n : ℕ) : IsClosed (glueTop n) :=
  IsClosed.preimage (continuous_glueLast n) isClosed_Ici

lemma glue_cover (n : ℕ) : glueBot n ∪ glueTop n = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  rcases le_total (glueLast n z.val) (1 / 2) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Agreement on the middle slice: both sides give the base point. -/
lemma glue_agree_mid (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₀ k₁ : GenLoop (Fin (n + 1)) X x)
    (z : ↥(Cube.boundary (Fin (n + 2))))
    (hmid : glueLast n z.val = 1 / 2) :
    k₀.1 (glueRest n z.val) = k₁.1 (glueRest n z.val) := by
  have hx0 : k₀.1 (glueRest n z.val) = x := by
    apply k₀.2
    obtain ⟨i, hi | hi⟩ := z.property
    · have hne : i ≠ Fin.last (n + 1) := by
        intro heq
        subst heq
        have e1 : (((z.val (Fin.last (n + 1))).val : ℝ)) = 0 := by
          rw [hi]
          rfl
        have gmid : (((z.val (Fin.last (n + 1))).val : ℝ)) = 1 / 2 := hmid
        rw [e1] at gmid
        norm_num at gmid
      have hlt : i.val < n + 1 := by
        have h1 : i.val < n + 2 := i.isLt
        have h2 : i.val ≠ n + 1 := by
          intro hcon
          apply hne
          apply Fin.val_injective
          rw [hcon]
          exact Fin.val_last _
        omega
      refine ⟨⟨i.val, hlt⟩, ?_⟩
      have hcast : Fin.castSucc ⟨i.val, hlt⟩ = i := by
        apply Fin.val_injective
        rw [Fin.val_castSucc]
      show (z.val (Fin.castSucc ⟨i.val, hlt⟩)) = 0 ∨ (z.val (Fin.castSucc ⟨i.val, hlt⟩)) = 1
      rw [hcast]
      exact Or.inl hi
    · have hne : i ≠ Fin.last (n + 1) := by
        intro heq
        subst heq
        have e1 : (((z.val (Fin.last (n + 1))).val : ℝ)) = 1 := by
          rw [hi]
          rfl
        have gmid : (((z.val (Fin.last (n + 1))).val : ℝ)) = 1 / 2 := hmid
        rw [e1] at gmid
        norm_num at gmid
      have hlt : i.val < n + 1 := by
        have h1 : i.val < n + 2 := i.isLt
        have h2 : i.val ≠ n + 1 := by
          intro hcon
          apply hne
          apply Fin.val_injective
          rw [hcon]
          exact Fin.val_last _
        omega
      refine ⟨⟨i.val, hlt⟩, ?_⟩
      have hcast : Fin.castSucc ⟨i.val, hlt⟩ = i := by
        apply Fin.val_injective
        rw [Fin.val_castSucc]
      show (z.val (Fin.castSucc ⟨i.val, hlt⟩)) = 0 ∨ (z.val (Fin.castSucc ⟨i.val, hlt⟩)) = 1
      rw [hcast]
      exact Or.inr hi
  have hx1 : k₁.1 (glueRest n z.val) = x := by
    apply k₁.2
    obtain ⟨i, hi | hi⟩ := z.property
    · have hne : i ≠ Fin.last (n + 1) := by
        intro heq
        subst heq
        have e1 : (((z.val (Fin.last (n + 1))).val : ℝ)) = 0 := by
          rw [hi]
          rfl
        have gmid : (((z.val (Fin.last (n + 1))).val : ℝ)) = 1 / 2 := hmid
        rw [e1] at gmid
        norm_num at gmid
      have hlt : i.val < n + 1 := by
        have h1 : i.val < n + 2 := i.isLt
        have h2 : i.val ≠ n + 1 := by
          intro hcon
          apply hne
          apply Fin.val_injective
          rw [hcon]
          exact Fin.val_last _
        omega
      refine ⟨⟨i.val, hlt⟩, ?_⟩
      have hcast : Fin.castSucc ⟨i.val, hlt⟩ = i := by
        apply Fin.val_injective
        rw [Fin.val_castSucc]
      show (z.val (Fin.castSucc ⟨i.val, hlt⟩)) = 0 ∨ (z.val (Fin.castSucc ⟨i.val, hlt⟩)) = 1
      rw [hcast]
      exact Or.inl hi
    · have hne : i ≠ Fin.last (n + 1) := by
        intro heq
        subst heq
        have e1 : (((z.val (Fin.last (n + 1))).val : ℝ)) = 1 := by
          rw [hi]
          rfl
        have gmid : (((z.val (Fin.last (n + 1))).val : ℝ)) = 1 / 2 := hmid
        rw [e1] at gmid
        norm_num at gmid
      have hlt : i.val < n + 1 := by
        have h1 : i.val < n + 2 := i.isLt
        have h2 : i.val ≠ n + 1 := by
          intro hcon
          apply hne
          apply Fin.val_injective
          rw [hcon]
          exact Fin.val_last _
        omega
      refine ⟨⟨i.val, hlt⟩, ?_⟩
      have hcast : Fin.castSucc ⟨i.val, hlt⟩ = i := by
        apply Fin.val_injective
        rw [Fin.val_castSucc]
      show (z.val (Fin.castSucc ⟨i.val, hlt⟩)) = 0 ∨ (z.val (Fin.castSucc ⟨i.val, hlt⟩)) = 1
      rw [hcast]
      exact Or.inr hi
  rw [hx0, hx1]

/-- Bottom global map (total, no branching). -/
def glueBotF (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₀ : GenLoop (Fin (n + 1)) X x) :
    ↥(Cube.boundary (Fin (n + 2))) → X :=
  fun z => k₀.1 (glueRest n z.val)

/-- Top global map. -/
def glueTopF (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₁ : GenLoop (Fin (n + 1)) X x) :
    ↥(Cube.boundary (Fin (n + 2))) → X :=
  fun z => k₁.1 (glueRest n z.val)

lemma continuous_glueBotF (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₀ : GenLoop (Fin (n + 1)) X x) :
    Continuous (glueBotF n k₀) := by
  unfold glueBotF
  exact k₀.1.continuous.comp (continuous_glueRest n)

lemma continuous_glueTopF (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₁ : GenLoop (Fin (n + 1)) X x) :
    Continuous (glueTopF n k₁) := by
  unfold glueTopF
  exact k₁.1.continuous.comp (continuous_glueRest n)

/-- Frontier points have middle last-coordinate. -/
lemma frontier_glueBot_sub (n : ℕ) :
    frontier (glueBot n) ⊆ {z | glueLast n z.val = 1 / 2} := by
  intro a ha
  rw [frontier_eq_closure_inter_closure] at ha
  obtain ⟨hcl, hco⟩ := ha
  have hle : glueLast n a.val ≤ 1 / 2 := by
    have hsub : closure (glueBot n) ⊆ glueBot n :=
      closure_minimal subset_rfl (isClosed_glueBot n)
    exact hsub hcl
  have hge : (1 : ℝ) / 2 ≤ glueLast n a.val := by
    have hsub : closure (glueBot n)ᶜ ⊆ glueTop n :=
      closure_minimal (fun z hz => by
        show (1 : ℝ) / 2 ≤ glueLast n z.val
        have h : ¬ glueLast n z.val ≤ 1 / 2 := hz
        exact le_of_not_ge h) (isClosed_glueTop n)
    exact hsub hco
  exact le_antisymm hle hge

/-- Agreement on the frontier. -/
lemma glue_agree_frontier (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₀ k₁ : GenLoop (Fin (n + 1)) X x) :
    ∀ a ∈ frontier (glueBot n),
      (glueBotF n k₀) a = (glueTopF n k₁) a := by
  intro a ha
  have hmid : glueLast n a.val = 1 / 2 := frontier_glueBot_sub n ha
  show k₀.1 (glueRest n a.val) = k₁.1 (glueRest n a.val)
  exact glue_agree_mid n k₀ k₁ a hmid

/-- The glued continuous map on the cube boundary. -/
def glueMapC (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₀ k₁ : GenLoop (Fin (n + 1)) X x) :
    C(↥(Cube.boundary (Fin (n + 2))), X) := by
  classical
  refine ⟨(glueBot n).piecewise (glueBotF n k₀) (glueTopF n k₁), ?_⟩
  exact Continuous.piecewise (glue_agree_frontier n k₀ k₁)
    (continuous_glueBotF n k₀) (continuous_glueTopF n k₁)

/-- Value on bottom-face points. -/
lemma glueMapC_bot (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₀ k₁ : GenLoop (Fin (n + 1)) X x)
    (z : ↥(Cube.boundary (Fin (n + 2))))
    (h0 : glueLast n z.val = 0) :
    glueMapC n k₀ k₁ z = k₀.1 (glueRest n z.val) := by
  classical
  have hm : z ∈ glueBot n := by
    show glueLast n z.val ≤ 1 / 2
    rw [h0]
    norm_num
  show (glueBot n).piecewise _ _ z = _
  rw [Set.piecewise_eq_of_mem _ _ _ hm]
  rfl

/-- Value on top-face points. -/
lemma glueMapC_top (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₀ k₁ : GenLoop (Fin (n + 1)) X x)
    (z : ↥(Cube.boundary (Fin (n + 2))))
    (h1 : glueLast n z.val = 1) :
    glueMapC n k₀ k₁ z = k₁.1 (glueRest n z.val) := by
  classical
  have hm : z ∉ glueBot n := by
    show ¬ glueLast n z.val ≤ 1 / 2
    rw [h1]
    norm_num
  show (glueBot n).piecewise _ _ z = _
  unfold Set.piecewise
  rw [ite_eq_right hm]
  rfl

/-! ### Reindexing between `I^{n+2}` and `I × I^{n+1}` -/

/-- Reindexing cube to cylinder (explicit formula). -/
def reidxFun (n : ℕ) (c : Fin (n + 2) → unitInterval) :
    unitInterval × (Fin (n + 1) → unitInterval) :=
  (c (Fin.last (n + 1)), fun j => c j.castSucc)

/-- Reindexing cylinder to cube (explicit formula). -/
def reidxInvFun (n : ℕ) (p : unitInterval × (Fin (n + 1) → unitInterval)) :
    Fin (n + 2) → unitInterval := fun i =>
  if h : i = Fin.last (n + 1) then p.1
  else p.2 ⟨i.val, by
    have h1 : i.val < n + 2 := i.isLt
    have h2 : i.val ≠ n + 1 := by
      intro hcon
      apply h
      apply Fin.val_injective
      rw [hcon]
      exact Fin.val_last _
    omega⟩

lemma continuous_reidxFun (n : ℕ) : Continuous (reidxFun n) := by
  refine Continuous.prodMk ?_ ?_
  · show Continuous fun (c : Fin (n + 2) → unitInterval) => c (Fin.last (n + 1))
    fun_prop
  · rw [continuous_pi_iff]
    intro j
    show Continuous fun (c : Fin (n + 2) → unitInterval) => c (Fin.castSucc j)
    fun_prop

lemma continuous_reidxInvFun (n : ℕ) :
    Continuous (reidxInvFun n) := by
  rw [continuous_pi_iff]
  intro i
  by_cases hi : i = Fin.last (n + 1)
  · have e : (fun p : unitInterval × (Fin (n + 1) → unitInterval) =>
        reidxInvFun n p i) = fun p => p.1 := by
      funext p
      show (if h : i = Fin.last (n + 1) then p.1 else _) = p.1
      rw [dite_eq_left hi]
    rw [e]
    fun_prop
  · have e : (fun p : unitInterval × (Fin (n + 1) → unitInterval) =>
        reidxInvFun n p i) = fun p => p.2 ⟨i.val, by
      have h1 : i.val < n + 2 := i.isLt
      have h2 : i.val ≠ n + 1 := by
        intro hcon
        apply hi
        apply Fin.val_injective
        rw [hcon]
        exact Fin.val_last _
      omega⟩ := by
      funext p
      show (if h : i = Fin.last (n + 1) then p.1 else _) = _
      rw [dite_eq_right hi]
    rw [e]
    fun_prop

def reidxCMap (n : ℕ) : C(Fin (n + 2) → unitInterval,
    unitInterval × (Fin (n + 1) → unitInterval)) :=
  ⟨reidxFun n, continuous_reidxFun n⟩

def reidxInvCMap (n : ℕ) : C(unitInterval × (Fin (n + 1) → unitInterval),
    Fin (n + 2) → unitInterval) :=
  ⟨reidxInvFun n, continuous_reidxInvFun n⟩

/-! ### The cube map from a homotopy, and exactness -/

/-- Cube map built from a cylinder homotopy by reindexing. -/
def cubeBMap (n : ℕ) {Y : TopCat.{u}}
    (Kcm : C(unitInterval × (Fin (n + 1) → unitInterval), Y)) :
    C(Fin (n + 2) → unitInterval, Y) :=
  Kcm.comp (reidxCMap n)

/-- Bottom face value. -/
lemma cubeBMap_bot (n : ℕ) {X Y : TopCat.{u}} (f : X ⟶ Y)
    {x : X} (k₀ : GenLoop (Fin (n + 1)) X x)
    (Kcm : C(unitInterval × (Fin (n + 1) → unitInterval), Y))
    (Kz : ∀ s, Kcm (0, s) = f.hom (k₀.1 s))
    (c : Fin (n + 2) → unitInterval)
    (h0 : ((c (Fin.last (n + 1))).val : ℝ) = 0) :
    cubeBMap n Kcm c = f.hom (k₀.1 (glueRest n c)) := by
  have e : cubeBMap n Kcm c = Kcm ((c (Fin.last (n + 1))), glueRest n c) := rfl
  rw [e]
  have h00 : c (Fin.last (n + 1)) = 0 := Subtype.ext h0
  rw [h00]
  exact Kz _

/-- Top face value. -/
lemma cubeBMap_top (n : ℕ) {X Y : TopCat.{u}} (f : X ⟶ Y)
    {x : X} (k₁ : GenLoop (Fin (n + 1)) X x)
    (Kcm : C(unitInterval × (Fin (n + 1) → unitInterval), Y))
    (Ko : ∀ s, Kcm (1, s) = f.hom (k₁.1 s))
    (c : Fin (n + 2) → unitInterval)
    (h1 : ((c (Fin.last (n + 1))).val : ℝ) = 1) :
    cubeBMap n Kcm c = f.hom (k₁.1 (glueRest n c)) := by
  have e : cubeBMap n Kcm c = Kcm ((c (Fin.last (n + 1))), glueRest n c) := rfl
  rw [e]
  have h11 : c (Fin.last (n + 1)) = 1 := Subtype.ext h1
  rw [h11]
  exact Ko _

/-- Side values are constant (from fixedness on the boundary). -/
lemma cubeBMap_side (n : ℕ) {X Y : TopCat.{u}} (f : X ⟶ Y)
    {x : X} (k₀ : GenLoop (Fin (n + 1)) X x)
    (Kcm : C(unitInterval × (Fin (n + 1) → unitInterval), Y))
    (Kfix : ∀ t (s : Fin (n + 1) → unitInterval),
      s ∈ Cube.boundary (Fin (n + 1)) → Kcm (t, s) = f.hom (k₀.1 s))
    (c : Fin (n + 2) → unitInterval)
    (hs : glueRest n c ∈ Cube.boundary (Fin (n + 1))) :
    cubeBMap n Kcm c = f x := by
  have e : cubeBMap n Kcm c = Kcm ((c (Fin.last (n + 1))), glueRest n c) := rfl
  rw [e]
  have hfx : f.hom (k₀.1 (glueRest n c)) = f x := by
    have h := k₀.2 _ hs
    -- h : k₀.1 _ = x; goal after show needs f.hom applied
    show f.hom _ = f x
    rw [h]
  rw [Kfix _ _ hs]
  exact hfx

/-- Exactness on the cube boundary: `f ∘ A = B`. -/
lemma cube_exact (n : ℕ) {X Y : TopCat.{u}} (f : X ⟶ Y)
    {x : X} (k₀ k₁ : GenLoop (Fin (n + 1)) X x)
    (Kcm : C(unitInterval × (Fin (n + 1) → unitInterval), Y))
    (Kz : ∀ s, Kcm (0, s) = f.hom (k₀.1 s))
    (Ko : ∀ s, Kcm (1, s) = f.hom (k₁.1 s))
    (Kfix : ∀ t (s : Fin (n + 1) → unitInterval),
      s ∈ Cube.boundary (Fin (n + 1)) → Kcm (t, s) = f.hom (k₀.1 s))
    (c : ↥(Cube.boundary (Fin (n + 2)))) :
    f (glueMapC n k₀ k₁ c) = cubeBMap n Kcm c.val := by
  classical
  have hB : cubeBMap n Kcm c.val = Kcm ((c.val (Fin.last (n + 1))), glueRest n c.val) := rfl
  rw [hB]
  by_cases hle : glueLast n c.val ≤ 1 / 2
  · -- bottom branch: A = k₀-part
    have hA : glueMapC n k₀ k₁ c = k₀.1 (glueRest n c.val) := by
      have hm : c ∈ glueBot n := hle
      show (glueBot n).piecewise _ _ c = _
      rw [Set.piecewise_eq_of_mem _ _ _ hm]
      rfl
    rw [hA]
    -- B side: case on whether the endpoint coord is last
    obtain ⟨i, hi | hi⟩ := c.property
    · by_cases hlast : i = Fin.last (n + 1)
      · subst hlast
        rw [hi]
        exact (Kz _).symm
      · -- endpoint elsewhere: rest is on the boundary, K fixed
        have hrest : glueRest n c.val ∈ Cube.boundary (Fin (n + 1)) := by
          have hlt : i.val < n + 1 := by
            have h1 : i.val < n + 2 := i.isLt
            have h2 : i.val ≠ n + 1 := by
              intro hcon
              apply hlast
              apply Fin.val_injective
              rw [hcon]
              exact Fin.val_last _
            omega
          refine ⟨⟨i.val, hlt⟩, ?_⟩
          have hcast : Fin.castSucc ⟨i.val, hlt⟩ = i := by
            apply Fin.val_injective
            rw [Fin.val_castSucc]
          show (c.val (Fin.castSucc ⟨i.val, hlt⟩)) = 0 ∨
            (c.val (Fin.castSucc ⟨i.val, hlt⟩)) = 1
          rw [hcast]
          exact Or.inl hi
        exact (Kfix _ _ hrest).symm
    · by_cases hlast : i = Fin.last (n + 1)
      · subst hlast
        -- last-val = 1 contradicts last ≤ 1/2
        have hv1 : (((c.val (Fin.last (n + 1))).val : ℝ)) = 1 := by
          rw [hi]
          rfl
        have hle' : (((c.val (Fin.last (n + 1))).val : ℝ)) ≤ 1 / 2 := by
          have e : glueLast n c.val = ((c.val (Fin.last (n + 1))).val : ℝ) := rfl
          rw [e] at hle
          exact hle
        rw [hv1] at hle'
        norm_num at hle'
      · -- endpoint elsewhere: rest is on the boundary, K fixed
        have hrest : glueRest n c.val ∈ Cube.boundary (Fin (n + 1)) := by
          have hlt : i.val < n + 1 := by
            have h1 : i.val < n + 2 := i.isLt
            have h2 : i.val ≠ n + 1 := by
              intro hcon
              apply hlast
              apply Fin.val_injective
              rw [hcon]
              exact Fin.val_last _
            omega
          refine ⟨⟨i.val, hlt⟩, ?_⟩
          have hcast : Fin.castSucc ⟨i.val, hlt⟩ = i := by
            apply Fin.val_injective
            rw [Fin.val_castSucc]
          show (c.val (Fin.castSucc ⟨i.val, hlt⟩)) = 0 ∨
            (c.val (Fin.castSucc ⟨i.val, hlt⟩)) = 1
          rw [hcast]
          exact Or.inr hi
        exact (Kfix _ _ hrest).symm
  · -- top branch (last > 1/2): A = k₁-part
    have hA : glueMapC n k₀ k₁ c = k₁.1 (glueRest n c.val) := by
      have hm : c ∉ glueBot n := by
        show ¬ glueLast n c.val ≤ 1 / 2
        exact hle
      show (glueBot n).piecewise _ _ c = _
      unfold Set.piecewise
      rw [ite_eq_right hm]
      rfl
    rw [hA]
    obtain ⟨i, hi | hi⟩ := c.property
    · by_cases hlast : i = Fin.last (n + 1)
      · subst hlast
        -- last-val = 0 contradicts last > 1/2
        have hv0 : (((c.val (Fin.last (n + 1))).val : ℝ)) = 0 := by
          rw [hi]
          rfl
        have hle' : glueLast n c.val ≤ 1 / 2 := by
          have e : glueLast n c.val = ((c.val (Fin.last (n + 1))).val : ℝ) := rfl
          rw [e, hv0]
          norm_num
        exact absurd hle' hle
      · have hrest : glueRest n c.val ∈ Cube.boundary (Fin (n + 1)) := by
          have hlt : i.val < n + 1 := by
            have h1 : i.val < n + 2 := i.isLt
            have h2 : i.val ≠ n + 1 := by
              intro hcon
              apply hlast
              apply Fin.val_injective
              rw [hcon]
              exact Fin.val_last _
            omega
          refine ⟨⟨i.val, hlt⟩, ?_⟩
          have hcast : Fin.castSucc ⟨i.val, hlt⟩ = i := by
            apply Fin.val_injective
            rw [Fin.val_castSucc]
          show (c.val (Fin.castSucc ⟨i.val, hlt⟩)) = 0 ∨
            (c.val (Fin.castSucc ⟨i.val, hlt⟩)) = 1
          rw [hcast]
          exact Or.inl hi
        have e0 : k₀.1 (glueRest n c.val) = x := k₀.2 _ hrest
        have e1 : k₁.1 (glueRest n c.val) = x := k₁.2 _ hrest
        have hK := Kfix (c.val (Fin.last (n + 1))) _ hrest
        -- goal: f (k₁.1 rest) = Kcm (last, rest); Kfix gives Kcm = f.hom (k₀.1 rest)
        rw [e1]
        rw [← e0]
        exact hK.symm
    · by_cases hlast : i = Fin.last (n + 1)
      · subst hlast
        rw [hi]
        exact (Ko _).symm
      · have hrest : glueRest n c.val ∈ Cube.boundary (Fin (n + 1)) := by
          have hlt : i.val < n + 1 := by
            have h1 : i.val < n + 2 := i.isLt
            have h2 : i.val ≠ n + 1 := by
              intro hcon
              apply hlast
              apply Fin.val_injective
              rw [hcon]
              exact Fin.val_last _
            omega
          refine ⟨⟨i.val, hlt⟩, ?_⟩
          have hcast : Fin.castSucc ⟨i.val, hlt⟩ = i := by
            apply Fin.val_injective
            rw [Fin.val_castSucc]
          show (c.val (Fin.castSucc ⟨i.val, hlt⟩)) = 0 ∨
            (c.val (Fin.castSucc ⟨i.val, hlt⟩)) = 1
          rw [hcast]
          exact Or.inr hi
        have e0 : k₀.1 (glueRest n c.val) = x := k₀.2 _ hrest
        have e1 : k₁.1 (glueRest n c.val) = x := k₁.2 _ hrest
        have hK := Kfix (c.val (Fin.last (n + 1))) _ hrest
        rw [e1]
        rw [← e0]
        exact hK.symm

/-! ### Disk conversion for injectivity -/

/-- Sphere-to-ball inclusion (subtype level). -/
def sphSubCMap (m : ℕ) : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  ⟨fun s => ⟨s.val, by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h : ‖s.val‖ = 1 := by
      have h2 : dist s.val 0 = 1 := Metric.mem_sphere.mp s.property
      rwa [dist_zero_right] at h2
    exact le_of_eq h⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩

/-- Sphere-to-ball inclusion at ULift level. -/
def sphBallULiftCMap (n : ℕ) :
    C(TopCat.diskBoundary.{u} (n + 2), TopCat.disk.{u} (n + 2)) :=
  (uliftUpCMap _).comp ((sphSubCMap (n + 2)).comp (uliftDownCMap _))

lemma continuous_sphSubCMap (m : ℕ) : Continuous (sphSubCMap m) := by
  unfold sphSubCMap
  apply Continuous.subtype_mk
  exact continuous_subtype_val

lemma continuous_sphBallULiftCMap (n : ℕ) :
    Continuous (sphBallULiftCMap n) :=
  (sphBallULiftCMap n).continuous

lemma continuous_diskToCubeULiftCMap (n : ℕ) :
    Continuous (diskToCubeULiftCMap n) :=
  (diskToCubeULiftCMap n).continuous

/-- Forward sphere-to-cube-boundary map. -/
def sphFwdCMap (n : ℕ) :
    C(TopCat.diskBoundary.{u} (n + 2), ↥(Cube.boundary (Fin (n + 2)))) := by
  refine ⟨fun q => ⟨diskToCubeULiftCMap (n + 2) (sphBallULiftCMap n q), ?_⟩, ?_⟩
  · have hvec : ((sphBallULiftCMap n q).down.val :
        EuclideanSpace ℝ (Fin (n + 2))) = (ULift.down q).val := rfl
    have hnorm : ‖((sphBallULiftCMap n q).down.val :
        EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := by
      rw [hvec]
      have hmem : (ULift.down q).val ∈ Metric.sphere
          (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := (ULift.down q).property
      rw [Metric.mem_sphere, dist_zero_right] at hmem
      exact hmem
    have e : diskToCubeULiftCMap (n + 2) (sphBallULiftCMap n q) =
        diskToCubeFun (n + 2) ((sphBallULiftCMap n q).down) := rfl
    rw [e]
    exact diskToCube_mem_boundary _ _ hnorm
  · apply Continuous.subtype_mk
    exact (continuous_diskToCubeULiftCMap _).comp (continuous_sphBallULiftCMap _)

/-- The ULift sphere-to-ball map is the boundary inclusion. -/
lemma sphBall_eq_inclusion (n : ℕ) :
    (sphBallULiftCMap.{u} n) = (TopCat.diskBoundaryInclusion.{u} (n + 2)).hom := by
  apply ContinuousMap.ext
  intro q
  apply ULift.ext
  apply Subtype.ext
  rfl

/-- Disk-boundary map from the glued cube-boundary map. -/
def glueADiscCMap (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₀ k₁ : GenLoop (Fin (n + 1)) X x) :
    C(TopCat.diskBoundary.{u} (n + 2), X) :=
  (glueMapC n k₀ k₁).comp (sphFwdCMap n)

/-- Disk map from the cube map. -/
def cubeBDiscCMap (n : ℕ) {Y : TopCat.{u}}
    (Kcm : C(unitInterval × (Fin (n + 1) → unitInterval), Y)) :
    C(TopCat.disk.{u} (n + 2), Y) :=
  (cubeBMap n Kcm).comp (diskToCubeULiftCMap (n + 2))

/-- The disk square commutes: `f ∘ A = B` on the sphere. -/
lemma glue_comm_disk (n : ℕ) {X Y : TopCat.{u}} (f : X ⟶ Y)
    {x : X} (k₀ k₁ : GenLoop (Fin (n + 1)) X x)
    (Kcm : C(unitInterval × (Fin (n + 1) → unitInterval), Y))
    (Kz : ∀ s, Kcm (0, s) = f.hom (k₀.1 s))
    (Ko : ∀ s, Kcm (1, s) = f.hom (k₁.1 s))
    (Kfix : ∀ t (s : Fin (n + 1) → unitInterval),
      s ∈ Cube.boundary (Fin (n + 1)) → Kcm (t, s) = f.hom (k₀.1 s))
    (q : TopCat.diskBoundary.{u} (n + 2)) :
    f.hom ((glueADiscCMap n k₀ k₁) q) =
      (cubeBDiscCMap n Kcm) ((TopCat.diskBoundaryInclusion.{u} (n + 2)).hom q) := by
  have hexact := cube_exact n f k₀ k₁ Kcm Kz Ko Kfix (sphFwdCMap n q)
  have eA : (glueADiscCMap n k₀ k₁) q = glueMapC n k₀ k₁ (sphFwdCMap n q) := rfl
  have eB : (cubeBDiscCMap n Kcm) ((TopCat.diskBoundaryInclusion.{u} (n + 2)).hom q) =
      cubeBMap n Kcm ((sphFwdCMap n q).val) := by
    have heq : (TopCat.diskBoundaryInclusion.{u} (n + 2)).hom q =
        sphBallULiftCMap n q := by rw [← sphBall_eq_inclusion]
    rw [heq]
    rfl
  rw [eA, eB]
  exact hexact

/-- TopCat disk-boundary map from the glued map. -/
def glueADisc (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₀ k₁ : GenLoop (Fin (n + 1)) X x) :
    TopCat.diskBoundary.{u} (n + 2) ⟶ X :=
  TopCat.ofHom (glueADiscCMap n k₀ k₁)

/-- TopCat disk map from the cube map. -/
def cubeBDisc (n : ℕ) {Y : TopCat.{u}}
    (Kcm : C(unitInterval × (Fin (n + 1) → unitInterval), Y)) :
    TopCat.disk.{u} (n + 2) ⟶ Y :=
  TopCat.ofHom (cubeBDiscCMap n Kcm)

/-- The TopCat disk square commutes. -/
lemma glue_comm_disk_mor (n : ℕ) {X Y : TopCat.{u}} (f : X ⟶ Y)
    {x : X} (k₀ k₁ : GenLoop (Fin (n + 1)) X x)
    (Kcm : C(unitInterval × (Fin (n + 1) → unitInterval), Y))
    (Kz : ∀ s, Kcm (0, s) = f.hom (k₀.1 s))
    (Ko : ∀ s, Kcm (1, s) = f.hom (k₁.1 s))
    (Kfix : ∀ t (s : Fin (n + 1) → unitInterval),
      s ∈ Cube.boundary (Fin (n + 1)) → Kcm (t, s) = f.hom (k₀.1 s)) :
    glueADisc n k₀ k₁ ≫ f = TopCat.diskBoundaryInclusion (n + 2) ≫ cubeBDisc n Kcm := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  show f.hom ((glueADiscCMap n k₀ k₁) q) = (cubeBDiscCMap n Kcm) _
  exact glue_comm_disk n f k₀ k₁ Kcm Kz Ko Kfix q

/-- Return cube map from a disk filler. -/
def retCubeCMap (n : ℕ) {X : TopCat.{u}} (l : TopCat.disk.{u} (n + 2) ⟶ X) :
    C(Fin (n + 2) → unitInterval, X) :=
  l.hom.comp (cubeToDiskULiftCMap (n + 2))

/-- The return cube map extends the glued boundary map. -/
lemma retCube_extends (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₀ k₁ : GenLoop (Fin (n + 1)) X x)
    (l : TopCat.disk.{u} (n + 2) ⟶ X)
    (hl : TopCat.diskBoundaryInclusion (n + 2) ≫ l = glueADisc n k₀ k₁)
    (c : ↥(Cube.boundary (Fin (n + 2)))) :
    retCubeCMap n l c.val = glueMapC n k₀ k₁ c := by
  obtain ⟨p, hp⟩ := bwdU_mem_range (n + 2) c.val c.property
  have hlapp : l ((TopCat.diskBoundaryInclusion (n + 2)) p) = (glueADisc n k₀ k₁) p := by
    have h : (TopCat.diskBoundaryInclusion (n + 2) ≫ l) p = (glueADisc n k₀ k₁) p := by
      rw [hl]
    simpa [TopCat.comp_app] using h
  have e1 : (cubeToDiskULiftCMap (n + 2)) c.val =
      (TopCat.diskBoundaryInclusion (n + 2)) p := hp.symm
  have e2 : retCubeCMap n l c.val = (glueADisc n k₀ k₁) p := by
    show l.hom ((cubeToDiskULiftCMap (n + 2)) c.val) = _
    rw [e1]
    exact hlapp
  have e3 : (glueADisc n k₀ k₁) p = glueMapC n k₀ k₁ c := by
    show (glueMapC n k₀ k₁) (sphFwdCMap n p) = glueMapC n k₀ k₁ c
    congr 1
    apply Subtype.ext
    show diskToCubeULiftCMap (n + 2) (sphBallULiftCMap n p) = c.val
    have heq : sphBallULiftCMap n p =
        (TopCat.diskBoundaryInclusion (n + 2)).hom p := by
      rw [sphBall_eq_inclusion]
    rw [heq, hp]
    exact fwdBwdCube_apply (n + 2) c.val
  rw [e2, e3]

/-! ### Reindexing identities and the return homotopy -/

lemma reidxInv_last (n : ℕ) (t : unitInterval) (s : Fin (n + 1) → unitInterval) :
    reidxInvFun n (t, s) (Fin.last (n + 1)) = t := by
  show (if h : Fin.last (n + 1) = Fin.last (n + 1) then t else _) = t
  rw [dite_eq_left rfl]

lemma reidxInv_castSucc (n : ℕ) (t : unitInterval) (s : Fin (n + 1) → unitInterval)
    (j : Fin (n + 1)) :
    reidxInvFun n (t, s) j.castSucc = s j := by
  have hne : j.castSucc ≠ Fin.last (n + 1) := by
    intro hcon
    have hval : (j.castSucc : Fin (n + 2)).val = ((Fin.last (n + 1) : Fin (n + 2))).val := by
      rw [hcon]
    rw [Fin.val_castSucc, Fin.val_last] at hval
    omega
  rw [show reidxInvFun n (t, s) j.castSucc =
    s ⟨j.castSucc.val, by
      have h1 : j.castSucc.val < n + 2 := j.castSucc.isLt
      have h2 : j.castSucc.val ≠ n + 1 := by
        intro hcon
        apply hne
        apply Fin.val_injective
        rw [hcon]
        exact Fin.val_last _
      omega⟩ from dite_eq_right hne]
  rfl

lemma glueRest_reidxInv (n : ℕ) (t : unitInterval) (s : Fin (n + 1) → unitInterval) :
    glueRest n (reidxInvFun n (t, s)) = s := by
  funext j
  show reidxInvFun n (t, s) j.castSucc = s j
  exact reidxInv_castSucc n t s j

lemma glueLast_reidxInv (n : ℕ) (t : unitInterval) (s : Fin (n + 1) → unitInterval) :
    glueLast n (reidxInvFun n (t, s)) = ((t.val : ℝ)) := by
  show (((reidxInvFun n (t, s) (Fin.last (n + 1))).val : ℝ)) = _
  rw [reidxInv_last]

/-- The reindexed return map gives a homotopy relative to the boundary. -/
lemma retHomotopyRel (n : ℕ) {X : TopCat.{u}} {x : X}
    (k₀ k₁ : GenLoop (Fin (n + 1)) X x)
    (l : TopCat.disk.{u} (n + 2) ⟶ X)
    (hl : TopCat.diskBoundaryInclusion (n + 2) ≫ l = glueADisc n k₀ k₁) :
    (k₀.1.HomotopicRel k₁.1 (Cube.boundary (Fin (n + 1)))) := by
  classical
  let Hcm : C(unitInterval × (Fin (n + 1) → unitInterval), X) :=
    (retCubeCMap n l).comp (reidxInvCMap n)
  have H0 : ∀ s, Hcm (0, s) = k₀.1 s := by
    intro s
    have hc : reidxInvFun n ((0 : unitInterval), s) ∈ Cube.boundary (Fin (n + 2)) := by
      refine ⟨Fin.last (n + 1), Or.inl ?_⟩
      show reidxInvFun n ((0 : unitInterval), s) (Fin.last (n + 1)) = 0
      rw [reidxInv_last]
    have hret := retCube_extends n k₀ k₁ l hl ⟨_, hc⟩
    have eH : Hcm (0, s) = retCubeCMap n l (reidxInvFun n (0, s)) := rfl
    rw [eH, hret]
    have hbot : glueMapC n k₀ k₁ ⟨_, hc⟩ = k₀.1 s := by
      have hlast0 : glueLast n ((⟨_, hc⟩ : ↥(Cube.boundary (Fin (n + 2)))).val) = 0 := by
        have h : glueLast n (reidxInvFun n ((0 : unitInterval), s)) = 0 := by
          rw [glueLast_reidxInv]
          rfl
        exact h
      have hmem : (⟨_, hc⟩ : ↥(Cube.boundary (Fin (n + 2)))) ∈ glueBot n := by
        show glueLast _ _ ≤ 1 / 2
        rw [hlast0]
        norm_num
      have e := glueMapC_bot n k₀ k₁ ⟨_, hc⟩ hlast0
      rw [e]
      have hrest : glueRest n (reidxInvFun n ((0 : unitInterval), s)) = s :=
        glueRest_reidxInv n _ _
      rw [hrest]
    exact hbot
  have H1 : ∀ s, Hcm (1, s) = k₁.1 s := by
    intro s
    have hc : reidxInvFun n ((1 : unitInterval), s) ∈ Cube.boundary (Fin (n + 2)) := by
      refine ⟨Fin.last (n + 1), Or.inr ?_⟩
      show reidxInvFun n ((1 : unitInterval), s) (Fin.last (n + 1)) = 1
      rw [reidxInv_last]
    have hret := retCube_extends n k₀ k₁ l hl ⟨_, hc⟩
    have eH : Hcm (1, s) = retCubeCMap n l (reidxInvFun n (1, s)) := rfl
    rw [eH, hret]
    have htop : glueMapC n k₀ k₁ ⟨_, hc⟩ = k₁.1 s := by
      have hlast1 : glueLast n ((⟨_, hc⟩ : ↥(Cube.boundary (Fin (n + 2)))).val) = 1 := by
        have h : glueLast n (reidxInvFun n ((1 : unitInterval), s)) = 1 := by
          rw [glueLast_reidxInv]
          rfl
        exact h
      have e := glueMapC_top n k₀ k₁ ⟨_, hc⟩ hlast1
      rw [e]
      have hrest : glueRest n (reidxInvFun n ((1 : unitInterval), s)) = s :=
        glueRest_reidxInv n _ _
      rw [hrest]
    exact htop
  have Hfix : ∀ t (s : Fin (n + 1) → unitInterval),
      s ∈ Cube.boundary (Fin (n + 1)) → Hcm (t, s) = k₀.1 s := by
    intro t s hs
    have hc : reidxInvFun n (t, s) ∈ Cube.boundary (Fin (n + 2)) := by
      obtain ⟨j, hj | hj⟩ := hs
      · refine ⟨j.castSucc, Or.inl ?_⟩
        rw [reidxInv_castSucc]
        exact hj
      · refine ⟨j.castSucc, Or.inr ?_⟩
        rw [reidxInv_castSucc]
        exact hj
    have hret := retCube_extends n k₀ k₁ l hl ⟨_, hc⟩
    have eH : Hcm (t, s) = retCubeCMap n l (reidxInvFun n (t, s)) := rfl
    rw [eH, hret]
    by_cases hle : glueLast n (reidxInvFun n (t, s)) ≤ 1 / 2
    · have hA : glueMapC n k₀ k₁ ⟨_, hc⟩ = k₀.1 s := by
        have hm : (⟨_, hc⟩ : ↥(Cube.boundary (Fin (n + 2)))) ∈ glueBot n := hle
        show (glueBot n).piecewise _ _ _ = _
        rw [Set.piecewise_eq_of_mem _ _ _ hm]
        show k₀.1 (glueRest n _) = _
        rw [glueRest_reidxInv]
      exact hA
    · have hA : glueMapC n k₀ k₁ ⟨_, hc⟩ = k₁.1 s := by
        have hm : (⟨_, hc⟩ : ↥(Cube.boundary (Fin (n + 2)))) ∉ glueBot n := by
          show ¬ glueLast _ _ ≤ 1 / 2
          exact hle
        show (glueBot n).piecewise _ _ _ = _
        unfold Set.piecewise
        rw [ite_eq_right hm]
        show k₁.1 (glueRest n _) = _
        rw [glueRest_reidxInv]
      have e0 : k₀.1 s = x := k₀.2 s hs
      have e1 : k₁.1 s = x := k₁.2 s hs
      exact hA.trans (e1.trans e0.symm)
  exact ⟨⟨Hcm, H0, H1⟩, Hfix⟩

/-- Injectivity on higher homotopy groups from the compression property. -/
theorem henry_imp_injective_pi {X Y : TopCat.{u}} (f : X ⟶ Y)
    (H : Henry.Top.weakEquivalences.{u} f) (n : ℕ) (x : X) :
    Function.Injective (homotopyGroupMap (Fin (n + 1)) f x) := by
  intro a b hab
  obtain ⟨k₀, rfl⟩ := Quotient.exists_rep a
  obtain ⟨k₁, rfl⟩ := Quotient.exists_rep b
  have hmap0 : homotopyGroupMap (Fin (n + 1)) f x ⟦k₀⟧ =
      ⟦⟨f.hom.comp k₀.1, fun y hy => by simp [k₀.2 y hy]⟩⟧ :=
    Quotient.map_mk _ _ _
  have hmap1 : homotopyGroupMap (Fin (n + 1)) f x ⟦k₁⟧ =
      ⟦⟨f.hom.comp k₁.1, fun y hy => by simp [k₁.2 y hy]⟩⟧ :=
    Quotient.map_mk _ _ _
  rw [hmap0, hmap1] at hab
  have hrel : (⟨f.hom.comp k₀.1, fun y hy => by simp [k₀.2 y hy]⟩ :
      GenLoop (Fin (n + 1)) Y (f x)).1.HomotopicRel
      (⟨f.hom.comp k₁.1, fun y hy => by simp [k₁.2 y hy]⟩ :
        GenLoop (Fin (n + 1)) Y (f x)).1
      (Cube.boundary (Fin (n + 1))) :=
    Quotient.exact hab
  obtain ⟨K⟩ := hrel
  let Kcm : C(unitInterval × (Fin (n + 1) → unitInterval), Y) := K.toContinuousMap
  have Kz : ∀ s, Kcm (0, s) = f.hom (k₀.1 s) := fun s => K.apply_zero s
  have Ko : ∀ s, Kcm (1, s) = f.hom (k₁.1 s) := fun s => K.apply_one s
  have Kfix : ∀ t (s : Fin (n + 1) → unitInterval),
      s ∈ Cube.boundary (Fin (n + 1)) → Kcm (t, s) = f.hom (k₀.1 s) := by
    intro t s hs
    have h := K.eq_fst t hs
    calc Kcm (t, s) = K (t, s) := rfl
      _ = (f.hom.comp k₀.1) s := h
      _ = f.hom (k₀.1 s) := rfl
  have hcomm : glueADisc n k₀ k₁ ≫ f = TopCat.diskBoundaryInclusion (n + 2) ≫ cubeBDisc n Kcm :=
    glue_comm_disk_mor n f k₀ k₁ Kcm Kz Ko Kfix
  obtain ⟨l, hl, _⟩ := H (n + 2) (glueADisc n k₀ k₁) (cubeBDisc n Kcm) hcomm
  have hhom : k₀.1.HomotopicRel k₁.1 (Cube.boundary (Fin (n + 1))) :=
    retHomotopyRel n k₀ k₁ l hl
  exact Quotient.sound hhom

end HomotopyHypothesis.Completion.Compression
