import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Category.SemiModelStructure.CylinderFacts
import HomotopyHypothesis.Category.SemiModelConstruction.RelativeHomotopy
import HomotopyHypothesis.Category.SemiModelConstruction.WeakEquivalences
/-!
# Two-out-of-three for weak equivalences of the completion

Left cancellation: if `f` and `f ≫ g` are weak equivalences of the completion, so is `g`. The proof
transports relative homotopy classes along an absolute homotopy of the base point
(Henry, *Algebraic models of homotopy types*, Prop 2.4.9–Cor 2.4.11).
-/

universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelStructure

open Henry Category.SemiModelConstruction

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C]

theorem presheafRelHomotopic_precomp {A B A' B' : C} {i : A ⟶ B}
    {i' : A' ⟶ B'} (a : A' ⟶ A) (v : B' ⟶ B)
    (hsq : i' ≫ v = a ≫ i) (hi' : cofibrations C i')
    {X : Completion.{w} C} {x y : X.obj.obj (op B)}
    (h : PresheafRelHomotopic i X x y) :
    PresheafRelHomotopic i' X (X.obj.map v.op x) (X.obj.map v.op y) := by
  obtain ⟨cyl, H, h₀, h₁⟩ := h
  have hab : RelHomotopic i (cyl.j₀ ≫ cyl.c) (cyl.j₁ ≫ cyl.c) :=
    ⟨cyl, 𝟙 cyl.I, by simp, by simp⟩
  obtain ⟨given, F, hF₀, hF₁⟩ := relHomotopic_precomp i i' a v hsq hi' hab
  refine ⟨given, X.obj.map F.op H, ?_, ?_⟩
  · change (X.obj.map F.op ≫ X.obj.map (given.j₀ ≫ given.c).op) H =
      X.obj.map v.op x
    rw [← X.obj.map_comp, ← op_comp, Category.assoc, hF₀]
    calc
      X.obj.map (v ≫ cyl.j₀ ≫ cyl.c).op H =
          X.obj.map v.op (X.obj.map (cyl.j₀ ≫ cyl.c).op H) := by
        change (X.obj.map (v ≫ cyl.j₀ ≫ cyl.c).op) H =
          (X.obj.map (cyl.j₀ ≫ cyl.c).op ≫ X.obj.map v.op) H
        rw [← X.obj.map_comp, ← op_comp]
      _ = X.obj.map v.op x := congrArg (X.obj.map v.op) h₀
  · change (X.obj.map F.op ≫ X.obj.map (given.j₁ ≫ given.c).op) H =
      X.obj.map v.op y
    rw [← X.obj.map_comp, ← op_comp, Category.assoc, hF₁]
    calc
      X.obj.map (v ≫ cyl.j₁ ≫ cyl.c).op H =
          X.obj.map v.op (X.obj.map (cyl.j₁ ≫ cyl.c).op H) := by
        change (X.obj.map (v ≫ cyl.j₁ ≫ cyl.c).op) H =
          (X.obj.map (cyl.j₁ ≫ cyl.c).op ≫ X.obj.map v.op) H
        rw [← X.obj.map_comp, ← op_comp]
      _ = X.obj.map v.op y := congrArg (X.obj.map v.op) h₁

theorem presheafRelHomotopic_of_relHomotopic {A B E : C} {i : A ⟶ B}
    {f g : B ⟶ E} {X : Completion.{w} C} (x : X.obj.obj (op E))
    (h : RelHomotopic i f g) :
    PresheafRelHomotopic i X (X.obj.map f.op x) (X.obj.map g.op x) := by
  obtain ⟨cyl, H, h₀, h₁⟩ := h
  refine ⟨cyl, X.obj.map H.op x, ?_, ?_⟩
  · change (X.obj.map H.op ≫ X.obj.map (cyl.j₀ ≫ cyl.c).op) x = _
    rw [← X.obj.map_comp, ← op_comp, Category.assoc, h₀]
  · change (X.obj.map H.op ≫ X.obj.map (cyl.j₁ ≫ cyl.c).op) x = _
    rw [← X.obj.map_comp, ← op_comp, Category.assoc, h₁]

theorem presheafRelHomotopic_trivialCofibration {K' P L : C}
    {Z : Completion.{w} C} (ι : K' ⟶ P) (φ : P ⟶ L)
    (hι : cofibrations C ι) (hφ : cofibrations C φ)
    (hφw : weakEquivalences C φ) (U V : Z.obj.obj (op L))
    (h : PresheafRelHomotopic ι Z (Z.obj.map φ.op U) (Z.obj.map φ.op V)) :
    PresheafRelHomotopic (ι ≫ φ) Z U V := by
  obtain ⟨ρ, hρ⟩ := IsCylinderCategory.exists_retraction φ hφ hφw
  have hj : cofibrations C (ι ≫ φ) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem ι φ hι hφ
  have hraw : RelHomotopic φ (ρ ≫ φ) (𝟙 L) :=
    trivialCofibration_relHomotopic φ hφ hφw (ρ ≫ φ) (𝟙 L) (by
      calc
        φ ≫ (ρ ≫ φ) = (φ ≫ ρ) ≫ φ := by simp [Category.assoc]
        _ = 𝟙 P ≫ φ := by rw [hρ]
        _ = φ ≫ 𝟙 L := by simp)
  have hUraw := presheafRelHomotopic_of_relHomotopic U hraw
  have hVraw := presheafRelHomotopic_of_relHomotopic V hraw
  have hU : PresheafRelHomotopic φ Z (Z.obj.map (ρ ≫ φ).op U) U := by
    simpa using hUraw
  have hV : PresheafRelHomotopic φ Z (Z.obj.map (ρ ≫ φ).op V) V := by
    simpa using hVraw
  let j := ι ≫ φ
  have hjbase : j ≫ 𝟙 L = ι ≫ φ := by simp [j]
  have hUj := presheafRelHomotopic_precomp (i := φ) (i' := j)
    ι (𝟙 L) hjbase hj hU
  have hVj := presheafRelHomotopic_precomp (i := φ) (i' := j)
    ι (𝟙 L) hjbase hj hV
  have hsq : j ≫ ρ = 𝟙 K' ≫ ι := by
    simp [j, Category.assoc, hρ]
  have hmid := presheafRelHomotopic_precomp (i := ι) (i' := j)
    (𝟙 K') ρ hsq hj h
  have hρU : Z.obj.map ρ.op (Z.obj.map φ.op U) = Z.obj.map (ρ ≫ φ).op U := by
    change (Z.obj.map φ.op ≫ Z.obj.map ρ.op) U = _
    rw [← Z.obj.map_comp, ← op_comp]
  have hρV : Z.obj.map ρ.op (Z.obj.map φ.op V) = Z.obj.map (ρ ≫ φ).op V := by
    change (Z.obj.map φ.op ≫ Z.obj.map ρ.op) V = _
    rw [← Z.obj.map_comp, ← op_comp]
  have hmid' : PresheafRelHomotopic j Z (Z.obj.map (ρ ≫ φ).op U)
      (Z.obj.map (ρ ≫ φ).op V) := by
    simpa only [hρU, hρV] using hmid
  exact presheafRelHomotopic_trans hj
    (presheafRelHomotopic_symm (by simpa [j] using hUj))
    (presheafRelHomotopic_trans hj hmid' (by simpa [j] using hVj))

theorem presheafMap_comp_apply {A B D : C} (X : Completion.{w} C)
    (f : A ⟶ B) (g : B ⟶ D) (x : X.obj.obj (op D)) :
    X.obj.map (f ≫ g).op x = X.obj.map f.op (X.obj.map g.op x) := by
  simp only [op_comp, Functor.map_comp_apply]

theorem presheafRelHomotopic_pushout {K L K' P : C} (j : K ⟶ L)
    (κ : K ⟶ K') (l : L ⟶ P) (ι : K' ⟶ P)
    (hP : IsPushout j κ l ι) (hj : cofibrations C j)
    {Z : Completion.{w} C} {u v : Z.obj.obj (op P)}
    (hbound : Z.obj.map ι.op u = Z.obj.map ι.op v)
    (h : PresheafRelHomotopic j Z (Z.obj.map l.op u) (Z.obj.map l.op v)) :
    PresheafRelHomotopic ι Z u v := by
  obtain ⟨cyl, H, h₀, h₁⟩ := h
  let e₀ := cyl.j₀ ≫ cyl.c
  let e₁ := cyl.j₁ ≫ cyl.c
  have he := relativeCylinder_endpoint_properties hj cyl
  have hγcof : cofibrations C (j ≫ e₀) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem j e₀ hj he.1.1
  have hγ1 : j ≫ e₁ = j ≫ e₀ := by
    dsimp [e₀, e₁]
    simpa [Category.assoc] using
      congrArg (fun q => q ≫ cyl.c) cyl.isPushout.w.symm
  let γ := j ≫ e₀
  have hι : cofibrations C ι :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hP.flip hj
  letI : HasPushout γ κ := IsCofibrationCategory.hasPushout (C := C) γ κ hγcof
  let N := pushout γ κ
  let nI : cyl.I ⟶ N := pushout.inl γ κ
  let nK : K' ⟶ N := pushout.inr γ κ
  let hN : IsPushout γ κ nI nK := IsPushout.of_hasPushout γ κ
  have hcompat₀ : j ≫ (e₀ ≫ nI) = κ ≫ nK := by
    calc
      j ≫ (e₀ ≫ nI) = γ ≫ nI := by simp [γ, Category.assoc]
      _ = κ ≫ nK := hN.w
  let n₀ : P ⟶ N := hP.desc (e₀ ≫ nI) nK hcompat₀
  have hn₀L : l ≫ n₀ = e₀ ≫ nI := by simp [n₀, hP]
  have hn₀K : ι ≫ n₀ = nK := by simp [n₀, hP]
  have hcompat₁ : j ≫ (e₁ ≫ nI) = κ ≫ nK := by
    calc
      j ≫ (e₁ ≫ nI) = (j ≫ e₁) ≫ nI := by simp [Category.assoc]
      _ = (j ≫ e₀) ≫ nI := by rw [hγ1]
      _ = γ ≫ nI := rfl
      _ = κ ≫ nK := hN.w
  let n₁ : P ⟶ N := hP.desc (e₁ ≫ nI) nK hcompat₁
  have hn₁L : l ≫ n₁ = e₁ ≫ nI := by simp [n₁, hP]
  have hn₁K : ι ≫ n₁ = nK := by simp [n₁, hP]

  letI : HasPushout ι ι := IsCofibrationCategory.hasPushout (C := C) ι ι hι
  let Q := pushout ι ι
  let q₀ : P ⟶ Q := pushout.inl ι ι
  let q₁ : P ⟶ Q := pushout.inr ι ι
  let hQ : IsPushout ι ι q₀ q₁ := IsPushout.of_hasPushout ι ι
  have hcompatQ : ι ≫ n₀ = ι ≫ n₁ := by rw [hn₀K, hn₁K]
  let d : Q ⟶ N := hQ.desc n₀ n₁ hcompatQ
  have hd₀ : q₀ ≫ d = n₀ := by simp [d, hQ]
  have hd₁ : q₁ ≫ d = n₁ := by simp [d, hQ]

  have hqcompat : j ≫ (l ≫ q₀) = j ≫ (l ≫ q₁) := by
    calc
      j ≫ (l ≫ q₀) = (j ≫ l) ≫ q₀ := by simp [Category.assoc]
      _ = (κ ≫ ι) ≫ q₀ := by rw [hP.w]
      _ = κ ≫ (ι ≫ q₀) := by rw [Category.assoc]
      _ = κ ≫ (ι ≫ q₁) := by rw [hQ.w]
      _ = (κ ≫ ι) ≫ q₁ := by rw [Category.assoc]
      _ = (j ≫ l) ≫ q₁ := by rw [hP.w]
      _ = j ≫ (l ≫ q₁) := by simp [Category.assoc]
  let q : cyl.P ⟶ Q := cyl.isPushout.desc (l ≫ q₀) (l ≫ q₁) hqcompat
  have hq₀ : cyl.j₀ ≫ q = l ≫ q₀ := by simp [q, cyl.isPushout]
  have hq₁ : cyl.j₁ ≫ q = l ≫ q₁ := by simp [q, cyl.isPushout]
  have hsq : cyl.c ≫ nI = q ≫ d := by
    apply cyl.isPushout.hom_ext
    · calc
        cyl.j₀ ≫ cyl.c ≫ nI = e₀ ≫ nI := by simp [e₀, Category.assoc]
        _ = l ≫ n₀ := hn₀L.symm
        _ = l ≫ (q₀ ≫ d) := by rw [hd₀]
        _ = cyl.j₀ ≫ q ≫ d := by
          calc
            l ≫ (q₀ ≫ d) = (l ≫ q₀) ≫ d := by simp [Category.assoc]
            _ = (cyl.j₀ ≫ q) ≫ d := by rw [← hq₀]
            _ = cyl.j₀ ≫ q ≫ d := by simp [Category.assoc]
    · calc
        cyl.j₁ ≫ cyl.c ≫ nI = e₁ ≫ nI := by simp [e₁, Category.assoc]
        _ = l ≫ n₁ := hn₁L.symm
        _ = l ≫ (q₁ ≫ d) := by rw [hd₁]
        _ = cyl.j₁ ≫ q ≫ d := by
          calc
            l ≫ (q₁ ≫ d) = (l ≫ q₁) ≫ d := by simp [Category.assoc]
            _ = (cyl.j₁ ≫ q) ≫ d := by rw [← hq₁]
            _ = cyl.j₁ ≫ q ≫ d := by simp [Category.assoc]
  let cocone : PushoutCocone cyl.c q := PushoutCocone.mk nI d hsq
  have hpush : IsPushout cyl.c q nI d := by
    have hc : IsColimit cocone := by
      apply PushoutCocone.isColimitAux' cocone
      intro s
      let rK : K' ⟶ s.pt := ι ≫ q₀ ≫ s.inr
      have hrK : ι ≫ q₀ ≫ s.inr = ι ≫ q₁ ≫ s.inr := by
        rw [← Category.assoc, hQ.w, Category.assoc]
      have hq₀s : cyl.j₀ ≫ q ≫ s.inr = l ≫ q₀ ≫ s.inr := by
        calc
          cyl.j₀ ≫ q ≫ s.inr = (cyl.j₀ ≫ q) ≫ s.inr := by simp [Category.assoc]
          _ = (l ≫ q₀) ≫ s.inr := by rw [hq₀]
          _ = l ≫ q₀ ≫ s.inr := by simp [Category.assoc]
      have hq₁s : cyl.j₁ ≫ q ≫ s.inr = l ≫ q₁ ≫ s.inr := by
        calc
          cyl.j₁ ≫ q ≫ s.inr = (cyl.j₁ ≫ q) ≫ s.inr := by simp [Category.assoc]
          _ = (l ≫ q₁) ≫ s.inr := by rw [hq₁]
          _ = l ≫ q₁ ≫ s.inr := by simp [Category.assoc]
      have hglue : γ ≫ s.inl = κ ≫ rK := by
        calc
          γ ≫ s.inl = (j ≫ e₀) ≫ s.inl := by rfl
          _ = j ≫ (cyl.j₀ ≫ cyl.c ≫ s.inl) := by simp [e₀, Category.assoc]
          _ = j ≫ (cyl.j₀ ≫ q ≫ s.inr) := by rw [s.condition]
          _ = j ≫ (l ≫ q₀ ≫ s.inr) := congrArg (fun t => j ≫ t) hq₀s
          _ = (j ≫ l) ≫ (q₀ ≫ s.inr) := by simp [Category.assoc]
          _ = (κ ≫ ι) ≫ (q₀ ≫ s.inr) := by rw [hP.w]
          _ = κ ≫ (ι ≫ q₀ ≫ s.inr) := by simp [Category.assoc]
          _ = κ ≫ rK := rfl
      let m : N ⟶ s.pt := hN.desc s.inl rK hglue
      have hmI : nI ≫ m = s.inl := by simp [m, hN]
      have hmK : nK ≫ m = rK := by simp [m, hN]
      have hn₀m : n₀ ≫ m = q₀ ≫ s.inr := by
        apply hP.hom_ext
        · calc
            l ≫ n₀ ≫ m = (l ≫ n₀) ≫ m := by simp [Category.assoc]
            _ = (e₀ ≫ nI) ≫ m := by rw [hn₀L]
            _ = e₀ ≫ s.inl := by rw [Category.assoc, hmI]
            _ = cyl.j₀ ≫ q ≫ s.inr := by
              calc
                e₀ ≫ s.inl = cyl.j₀ ≫ cyl.c ≫ s.inl := by simp [e₀, Category.assoc]
                _ = cyl.j₀ ≫ q ≫ s.inr := by rw [s.condition]
            _ = l ≫ q₀ ≫ s.inr := hq₀s
        · calc
            ι ≫ n₀ ≫ m = (ι ≫ n₀) ≫ m := by simp [Category.assoc]
            _ = nK ≫ m := by rw [hn₀K]
            _ = rK := hmK
            _ = ι ≫ q₀ ≫ s.inr := rfl
      have hn₁m : n₁ ≫ m = q₁ ≫ s.inr := by
        apply hP.hom_ext
        · calc
            l ≫ n₁ ≫ m = (l ≫ n₁) ≫ m := by simp [Category.assoc]
            _ = (e₁ ≫ nI) ≫ m := by rw [hn₁L]
            _ = e₁ ≫ s.inl := by rw [Category.assoc, hmI]
            _ = cyl.j₁ ≫ q ≫ s.inr := by
              calc
                e₁ ≫ s.inl = cyl.j₁ ≫ cyl.c ≫ s.inl := by simp [e₁, Category.assoc]
                _ = cyl.j₁ ≫ q ≫ s.inr := by rw [s.condition]
            _ = l ≫ q₁ ≫ s.inr := hq₁s
        · calc
          ι ≫ n₁ ≫ m = (ι ≫ n₁) ≫ m := by simp [Category.assoc]
            _ = nK ≫ m := by rw [hn₁K]
            _ = rK := hmK
            _ = ι ≫ q₁ ≫ s.inr := hrK
      refine ⟨m, hmI, ?_, ?_⟩
      · apply hQ.hom_ext
        · calc
            q₀ ≫ d ≫ m = (q₀ ≫ d) ≫ m := by simp [Category.assoc]
            _ = n₀ ≫ m := by rw [hd₀]
            _ = q₀ ≫ s.inr := hn₀m
        · calc
            q₁ ≫ d ≫ m = (q₁ ≫ d) ≫ m := by simp [Category.assoc]
            _ = n₁ ≫ m := by rw [hd₁]
            _ = q₁ ≫ s.inr := hn₁m
      · intro m' hm'I hm'Q
        change N ⟶ s.pt at m'
        change nI ≫ m' = s.inl at hm'I
        change d ≫ m' = s.inr at hm'Q
        apply hN.hom_ext
        · exact hm'I.trans hmI.symm
        · have hn₀m' : n₀ ≫ m' = q₀ ≫ s.inr := by
            calc
              n₀ ≫ m' = (q₀ ≫ d) ≫ m' := by rw [← hd₀]
              _ = q₀ ≫ (d ≫ m') := by simp [Category.assoc]
              _ = q₀ ≫ s.inr := by rw [hm'Q]
          have hm'K : nK ≫ m' = rK := by
            calc
              nK ≫ m' = (ι ≫ n₀) ≫ m' := by rw [← hn₀K]
              _ = ι ≫ (n₀ ≫ m') := by simp [Category.assoc]
              _ = ι ≫ (q₀ ≫ s.inr) := by rw [hn₀m']
              _ = rK := rfl
          exact hm'K.trans hmK.symm
    exact IsPushout.of_isColimit hc

  have htotal₀ : IsPushout (j ≫ e₀) κ nI (ι ≫ n₀) := by
    rw [hn₀K]
    exact hN
  have htotal₁ : IsPushout (j ≫ e₁) κ nI (ι ≫ n₁) := by
    rw [hγ1, hn₁K]
    exact hN
  have hn₀push : IsPushout e₀ l nI n₀ :=
    IsPushout.of_left htotal₀ hn₀L.symm hP
  have hn₁push : IsPushout e₁ l nI n₁ :=
    IsPushout.of_left htotal₁ hn₁L.symm hP
  have hn₀w : weakEquivalences C n₀ :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      e₀ l nI n₀ hn₀push he.1.1 he.1.2
  have hn₁w : weakEquivalences C n₁ :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      e₁ l nI n₁ hn₁push he.2.1 he.2.2

  have he₀p : e₀ ≫ cyl.p = 𝟙 L := by
    simpa [e₀, Category.assoc] using cyl.j₀_c_p
  have he₁p : e₁ ≫ cyl.p = 𝟙 L := by
    simpa [e₁, Category.assoc] using cyl.j₁_c_p
  have hrcompat : γ ≫ (cyl.p ≫ l) = κ ≫ ι := by
    calc
      γ ≫ (cyl.p ≫ l) = j ≫ (e₀ ≫ (cyl.p ≫ l)) := by simp [γ, Category.assoc]
      _ = j ≫ ((e₀ ≫ cyl.p) ≫ l) := by simp [Category.assoc]
      _ = j ≫ ((𝟙 L) ≫ l) := by rw [he₀p]
      _ = j ≫ l := by simp
      _ = κ ≫ ι := hP.w
  let r : N ⟶ P := hN.desc (cyl.p ≫ l) ι hrcompat
  have hrI : nI ≫ r = cyl.p ≫ l := by simp [r, hN]
  have hrK : nK ≫ r = ι := by simp [r, hN]
  have hn₀r : n₀ ≫ r = 𝟙 P := by
    apply hP.hom_ext
    · calc
        l ≫ n₀ ≫ r = (l ≫ n₀) ≫ r := by simp [Category.assoc]
        _ = (e₀ ≫ nI) ≫ r := by rw [hn₀L]
        _ = e₀ ≫ (nI ≫ r) := by simp [Category.assoc]
        _ = e₀ ≫ (cyl.p ≫ l) := by rw [hrI]
        _ = l ≫ 𝟙 P := by
          calc
            e₀ ≫ (cyl.p ≫ l) = (e₀ ≫ cyl.p) ≫ l := by simp [Category.assoc]
            _ = (𝟙 L) ≫ l := by rw [he₀p]
            _ = l ≫ 𝟙 P := by simp
    · calc
        ι ≫ n₀ ≫ r = (ι ≫ n₀) ≫ r := by simp [Category.assoc]
        _ = nK ≫ r := by rw [hn₀K]
        _ = ι ≫ 𝟙 P := by simpa using hrK
  have hn₁r : n₁ ≫ r = 𝟙 P := by
    apply hP.hom_ext
    · calc
        l ≫ n₁ ≫ r = (l ≫ n₁) ≫ r := by simp [Category.assoc]
        _ = (e₁ ≫ nI) ≫ r := by rw [hn₁L]
        _ = e₁ ≫ (nI ≫ r) := by simp [Category.assoc]
        _ = e₁ ≫ (cyl.p ≫ l) := by rw [hrI]
        _ = l ≫ 𝟙 P := by
          calc
            e₁ ≫ (cyl.p ≫ l) = (e₁ ≫ cyl.p) ≫ l := by simp [Category.assoc]
            _ = (𝟙 L) ≫ l := by rw [he₁p]
            _ = l ≫ 𝟙 P := by simp
    · calc
        ι ≫ n₁ ≫ r = (ι ≫ n₁) ≫ r := by simp [Category.assoc]
        _ = nK ≫ r := by rw [hn₁K]
        _ = ι ≫ 𝟙 P := by simpa using hrK
  have hid : weakEquivalences C (𝟙 P) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 P)
      (MorphismProperty.isomorphisms.infer_property (𝟙 P))
  have hrw := IsCylinderCategory.twoOutOfSix (C := C) (𝟙 P) n₀ r
    (by simpa using hn₀w) (by simpa [hn₀r] using hid)
  let cyl' : RelativeCylinder ι :=
    { P := Q
      j₀ := q₀
      j₁ := q₁
      isPushout := hQ
      I := N
      c := d
      p := r
      c_mem := (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
        hpush.flip cyl.c_mem
      p_mem := hrw.2.2.1
      j₀_c_p := by
        calc
          q₀ ≫ d ≫ r = (q₀ ≫ d) ≫ r := by simp [Category.assoc]
          _ = n₀ ≫ r := by rw [hd₀]
          _ = 𝟙 P := hn₀r
      j₁_c_p := by
        calc
          q₁ ≫ d ≫ r = (q₁ ≫ d) ≫ r := by simp [Category.assoc]
          _ = n₁ ≫ r := by rw [hd₁]
          _ = 𝟙 P := hn₁r }

  have hglue : Z.obj.map (j ≫ e₀).op H = Z.obj.map κ.op (Z.obj.map ι.op u) := by
    calc
      Z.obj.map (j ≫ e₀).op H = Z.obj.map j.op (Z.obj.map e₀.op H) :=
        presheafMap_comp_apply Z j e₀ H
      _ = Z.obj.map j.op (Z.obj.map l.op u) := congrArg (Z.obj.map j.op) h₀
      _ = Z.obj.map (j ≫ l).op u :=
        (presheafMap_comp_apply Z j l u).symm
      _ = Z.obj.map (κ ≫ ι).op u :=
        congrArg (fun f => Z.obj.map f.op u) hP.w
      _ = Z.obj.map κ.op (Z.obj.map ι.op u) := presheafMap_comp_apply Z κ ι u
  obtain ⟨H', hH'I, hH'K⟩ := Types.exists_of_isPullback
    (Z.property.2 (j ≫ e₀) κ nI nK hN hγcof) H (Z.obj.map ι.op u) hglue
  have h₀end : Z.obj.map (q₀ ≫ d).op H' = u := by
    apply Types.ext_of_isPullback (Z.property.2 j κ l ι hP hj)
    · calc
        Z.obj.map l.op (Z.obj.map (q₀ ≫ d).op H') =
            Z.obj.map (l ≫ (q₀ ≫ d)).op H' := (presheafMap_comp_apply Z l (q₀ ≫ d) H').symm
        _ = Z.obj.map (e₀ ≫ nI).op H' := by
          exact congrArg (fun (f : L ⟶ N) => Z.obj.map f.op H') (by
            calc
              l ≫ (q₀ ≫ d) = l ≫ n₀ := by rw [hd₀]
              _ = e₀ ≫ nI := hn₀L)
        _ = Z.obj.map e₀.op (Z.obj.map nI.op H') := presheafMap_comp_apply Z e₀ nI H'
        _ = Z.obj.map e₀.op H := congrArg (Z.obj.map e₀.op) hH'I
        _ = Z.obj.map l.op u := h₀
    · calc
        Z.obj.map ι.op (Z.obj.map (q₀ ≫ d).op H') =
            Z.obj.map (ι ≫ (q₀ ≫ d)).op H' := (presheafMap_comp_apply Z ι (q₀ ≫ d) H').symm
        _ = Z.obj.map nK.op H' := by
          exact congrArg (fun (f : K' ⟶ N) => Z.obj.map f.op H') (by
            calc
              ι ≫ (q₀ ≫ d) = ι ≫ n₀ := by rw [hd₀]
              _ = nK := hn₀K)
        _ = Z.obj.map ι.op u := hH'K
  have h₁end : Z.obj.map (q₁ ≫ d).op H' = v := by
    apply Types.ext_of_isPullback (Z.property.2 j κ l ι hP hj)
    · calc
        Z.obj.map l.op (Z.obj.map (q₁ ≫ d).op H') =
            Z.obj.map (l ≫ (q₁ ≫ d)).op H' := (presheafMap_comp_apply Z l (q₁ ≫ d) H').symm
        _ = Z.obj.map (e₁ ≫ nI).op H' := by
          exact congrArg (fun (f : L ⟶ N) => Z.obj.map f.op H') (by
            calc
              l ≫ (q₁ ≫ d) = l ≫ n₁ := by rw [hd₁]
              _ = e₁ ≫ nI := hn₁L)
        _ = Z.obj.map e₁.op (Z.obj.map nI.op H') := presheafMap_comp_apply Z e₁ nI H'
        _ = Z.obj.map e₁.op H := congrArg (Z.obj.map e₁.op) hH'I
        _ = Z.obj.map l.op v := h₁
    · calc
        Z.obj.map ι.op (Z.obj.map (q₁ ≫ d).op H') =
            Z.obj.map (ι ≫ (q₁ ≫ d)).op H' := (presheafMap_comp_apply Z ι (q₁ ≫ d) H').symm
        _ = Z.obj.map nK.op H' := by
          exact congrArg (fun (f : K' ⟶ N) => Z.obj.map f.op H') (by
            calc
              ι ≫ (q₁ ≫ d) = ι ≫ n₁ := by rw [hd₁]
              _ = nK := hn₁K)
        _ = Z.obj.map ι.op u := hH'K
        _ = Z.obj.map ι.op v := hbound
  exact ⟨cyl', H', h₀end, h₁end⟩

/-- Left cancellation for weak equivalences of the completion. -/
theorem completion_weakEquivalence_of_precomp {X Y Z : Completion.{w} C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : Completion.weakEquivalences C f)
    (hfg : Completion.weakEquivalences C (f ≫ g)) : Completion.weakEquivalences C g := by
  apply (completion_weakEquivalence_iff_homotopyLift g).mpr
  intro A B i hi y z hyz

  obtain ⟨O, hO_nonempty⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hO : IsInitial O := Classical.choice hO_nonempty
  let iO : O ⟶ A := hO.to A
  have hiO : cofibrations C iO := IsCofibrationCategory.initial_cofibration hO A
  letI : Unique (X.obj.obj (op O)) := Classical.choice (X.property.1 hO)
  letI : Unique (Y.obj.obj (op O)) := Classical.choice (Y.property.1 hO)
  let xO : X.obj.obj (op O) := default
  have hcompatO : f.hom.app (op O) xO = Y.obj.map iO.op y := Subsingleton.elim _ _
  obtain ⟨xA, _hxA, hA⟩ :=
    (completion_weakEquivalence_iff_homotopyLift f).mp hf iO hiO xO y hcompatO
  obtain ⟨cylA, H, hA₀, hA₁⟩ := hA
  let e₀ : A ⟶ cylA.I := cylA.j₀ ≫ cylA.c
  let e₁ : A ⟶ cylA.I := cylA.j₁ ≫ cylA.c
  have heA := relativeCylinder_endpoint_properties hiO cylA
  have heA₀p : e₀ ≫ cylA.p = 𝟙 A := by
    simpa [e₀, Category.assoc] using cylA.j₀_c_p
  have heA₁p : e₁ ≫ cylA.p = 𝟙 A := by
    simpa [e₁, Category.assoc] using cylA.j₁_c_p

  letI : HasPushout i e₀ := IsCofibrationCategory.hasPushout (C := C) i e₀ hi
  let S₀ := pushout i e₀
  let s₀B : B ⟶ S₀ := pushout.inl i e₀
  let s₀I : cylA.I ⟶ S₀ := pushout.inr i e₀
  let hS₀ : IsPushout i e₀ s₀B s₀I := IsPushout.of_hasPushout i e₀

  letI : HasPushout e₁ i :=
    IsCofibrationCategory.hasPushout (C := C) e₁ i heA.2.1
  let S₁ := pushout e₁ i
  let s₁I : cylA.I ⟶ S₁ := pushout.inl e₁ i
  let s₁B : B ⟶ S₁ := pushout.inr e₁ i
  let hS₁ : IsPushout e₁ i s₁I s₁B := IsPushout.of_hasPushout e₁ i

  letI : HasPushout i (e₁ ≫ s₀I) :=
    IsCofibrationCategory.hasPushout (C := C) i (e₁ ≫ s₀I) hi
  let T := pushout i (e₁ ≫ s₀I)
  let tB : B ⟶ T := pushout.inl i (e₁ ≫ s₀I)
  let tS₀ : S₀ ⟶ T := pushout.inr i (e₁ ≫ s₀I)
  let hT : IsPushout i (e₁ ≫ s₀I) tB tS₀ :=
    IsPushout.of_hasPushout i (e₁ ≫ s₀I)
  let tB₀ : B ⟶ T := s₀B ≫ tS₀
  let tI : cylA.I ⟶ T := s₀I ≫ tS₀

  have hs₀toB_compat : i ≫ (𝟙 B) = e₀ ≫ (cylA.p ≫ i) := by
    calc
      i ≫ (𝟙 B) = i := by simp
      _ = (e₀ ≫ cylA.p) ≫ i := by rw [heA₀p]; simp
      _ = e₀ ≫ (cylA.p ≫ i) := by simp [Category.assoc]
  let s₀toB : S₀ ⟶ B := hS₀.desc (𝟙 B) (cylA.p ≫ i) hs₀toB_compat
  have hs₀toB_B : s₀B ≫ s₀toB = 𝟙 B := by simp [s₀toB, hS₀]
  have hs₀toB_I : s₀I ≫ s₀toB = cylA.p ≫ i := by simp [s₀toB, hS₀]
  have hTtoB_compat : i ≫ (𝟙 B) = (e₁ ≫ s₀I) ≫ s₀toB := by
    calc
      i ≫ (𝟙 B) = i := by simp
      _ = (e₁ ≫ cylA.p) ≫ i := by rw [heA₁p]; simp
      _ = e₁ ≫ (cylA.p ≫ i) := by simp [Category.assoc]
      _ = e₁ ≫ (s₀I ≫ s₀toB) := by rw [hs₀toB_I]
      _ = (e₁ ≫ s₀I) ≫ s₀toB := by simp [Category.assoc]
  let qT : T ⟶ B := hT.desc (𝟙 B) s₀toB hTtoB_compat
  have hqT_B : tB ≫ qT = 𝟙 B := by simp [qT, hT]
  have hqT_S₀ : tS₀ ≫ qT = s₀toB := by simp [qT, hT]
  have htB₀qT : tB₀ ≫ qT = 𝟙 B := by
    dsimp [tB₀]
    rw [Category.assoc, hqT_S₀, hs₀toB_B]
  have htI_qT : tI ≫ qT = cylA.p ≫ i := by
    dsimp [tI]
    rw [Category.assoc, hqT_S₀, hs₀toB_I]

  obtain ⟨J, cT, pJ, hcofT, hpJ, hfactor⟩ := brown_factorization qT
  let φ₀ : S₀ ⟶ J := tS₀ ≫ cT
  let φ₀B : B ⟶ J := s₀B ≫ φ₀
  let m : cylA.I ⟶ J := s₀I ≫ φ₀
  have hext1_compat : e₁ ≫ tI = i ≫ tB := by
    dsimp [tI, tB]
    simpa [Category.assoc] using hT.w.symm
  let s₁T : S₁ ⟶ T := hS₁.desc tI tB hext1_compat
  have hs₁TI : s₁I ≫ s₁T = tI := by simp [s₁T, hS₁]
  have hs₁TB : s₁B ≫ s₁T = tB := by simp [s₁T, hS₁]
  let φ₁ : S₁ ⟶ J := s₁T ≫ cT
  let φ₁B : B ⟶ J := s₁B ≫ φ₁

  have hS₁T_compat : i ≫ tB₀ = (e₀ ≫ s₁I) ≫ s₁T := by
    calc
      i ≫ tB₀ = (i ≫ s₀B) ≫ tS₀ := by simp [tB₀, Category.assoc]
      _ = (e₀ ≫ s₀I) ≫ tS₀ := by rw [hS₀.w]
      _ = e₀ ≫ tI := by simp [tI, Category.assoc]
      _ = e₀ ≫ (s₁I ≫ s₁T) := by rw [hs₁TI]
      _ = (e₀ ≫ s₁I) ≫ s₁T := by simp [Category.assoc]
  let S₁Tcocone : PushoutCocone i (e₀ ≫ s₁I) :=
    PushoutCocone.mk tB₀ s₁T hS₁T_compat
  have hS₁Tcolimit : IsColimit S₁Tcocone := by
    apply PushoutCocone.isColimitAux' S₁Tcocone
    intro s
    have hS₀compat : i ≫ s.inl = e₀ ≫ (s₁I ≫ s.inr) := by
      simpa [Category.assoc] using s.condition
    let rS₀ : S₀ ⟶ s.pt := hS₀.desc s.inl (s₁I ≫ s.inr) hS₀compat
    have hrS₀B : s₀B ≫ rS₀ = s.inl := by simp [rS₀, hS₀]
    have hrS₀I : s₀I ≫ rS₀ = s₁I ≫ s.inr := by simp [rS₀, hS₀]
    have hTcompat : i ≫ (s₁B ≫ s.inr) = (e₁ ≫ s₀I) ≫ rS₀ := by
      calc
        i ≫ (s₁B ≫ s.inr) = (i ≫ s₁B) ≫ s.inr := by simp [Category.assoc]
        _ = (e₁ ≫ s₁I) ≫ s.inr := by rw [hS₁.w]
        _ = e₁ ≫ (s₁I ≫ s.inr) := by simp [Category.assoc]
        _ = e₁ ≫ (s₀I ≫ rS₀) := by rw [hrS₀I]
        _ = (e₁ ≫ s₀I) ≫ rS₀ := by simp [Category.assoc]
    let rT : T ⟶ s.pt := hT.desc (s₁B ≫ s.inr) rS₀ hTcompat
    have hrTB : tB ≫ rT = s₁B ≫ s.inr := by simp [rT, hT]
    have hrTS₀ : tS₀ ≫ rT = rS₀ := by simp [rT, hT]
    have hrT₀ : tB₀ ≫ rT = s.inl := by
      calc
        tB₀ ≫ rT = (s₀B ≫ tS₀) ≫ rT := rfl
        _ = s₀B ≫ (tS₀ ≫ rT) := by simp [Category.assoc]
        _ = s₀B ≫ rS₀ := congrArg (fun q => s₀B ≫ q) hrTS₀
        _ = s.inl := hrS₀B
    have hrTs₁ : s₁T ≫ rT = s.inr := by
      apply hS₁.hom_ext
      · calc
          s₁I ≫ (s₁T ≫ rT) = (s₁I ≫ s₁T) ≫ rT := by simp [Category.assoc]
          _ = tI ≫ rT := by rw [hs₁TI]
          _ = (s₀I ≫ tS₀) ≫ rT := rfl
          _ = s₀I ≫ (tS₀ ≫ rT) := by simp [Category.assoc]
          _ = s₀I ≫ rS₀ := by rw [hrTS₀]
          _ = s₁I ≫ s.inr := hrS₀I
      · calc
          s₁B ≫ (s₁T ≫ rT) = (s₁B ≫ s₁T) ≫ rT := by simp [Category.assoc]
          _ = tB ≫ rT := by rw [hs₁TB]
          _ = s₁B ≫ s.inr := hrTB
    refine ⟨rT, hrT₀, hrTs₁, ?_⟩
    intro rT' hrT'₀ hrT'₁
    change T ⟶ s.pt at rT'
    change tB₀ ≫ rT' = s.inl at hrT'₀
    change s₁T ≫ rT' = s.inr at hrT'₁
    have hrT'B : tB ≫ rT' = s₁B ≫ s.inr := by
      calc
        tB ≫ rT' = (s₁B ≫ s₁T) ≫ rT' := by rw [hs₁TB]
        _ = s₁B ≫ (s₁T ≫ rT') := by simp [Category.assoc]
        _ = s₁B ≫ s.inr := by rw [hrT'₁]
    have hrT'S₀ : tS₀ ≫ rT' = rS₀ := by
      apply hS₀.hom_ext
      · calc
          s₀B ≫ (tS₀ ≫ rT') = (s₀B ≫ tS₀) ≫ rT' := by simp [Category.assoc]
          _ = tB₀ ≫ rT' := rfl
          _ = s.inl := hrT'₀
          _ = s₀B ≫ rS₀ := hrS₀B.symm
      · calc
          s₀I ≫ (tS₀ ≫ rT') = (s₀I ≫ tS₀) ≫ rT' := by simp [Category.assoc]
          _ = tI ≫ rT' := rfl
          _ = (s₁I ≫ s₁T) ≫ rT' := by rw [hs₁TI]
          _ = s₁I ≫ (s₁T ≫ rT') := by simp [Category.assoc]
          _ = s₁I ≫ s.inr := by rw [hrT'₁]
          _ = s₀I ≫ rS₀ := hrS₀I.symm
    apply hT.hom_ext
    · exact hrT'B.trans hrTB.symm
    · exact hrT'S₀.trans hrTS₀.symm
  let hS₁T : IsPushout i (e₀ ≫ s₁I) tB₀ s₁T :=
    IsPushout.of_isColimit hS₁Tcolimit

  have hs₀Tcof : cofibrations C tS₀ :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hT.flip hi
  have hs₁Tcof : cofibrations C s₁T :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hS₁T.flip hi
  have hφ₀cof : cofibrations C φ₀ :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem tS₀ cT hs₀Tcof hcofT
  have hφ₁cof : cofibrations C φ₁ :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem s₁T cT hs₁Tcof hcofT

  have hφ₀q : φ₀ ≫ pJ = s₀toB := by
    calc
      φ₀ ≫ pJ = (tS₀ ≫ cT) ≫ pJ := rfl
      _ = tS₀ ≫ (cT ≫ pJ) := by simp [Category.assoc]
      _ = tS₀ ≫ qT := by rw [hfactor]
      _ = s₀toB := by simp [qT, hT]
  have hφ₁q : φ₁ ≫ pJ = s₁T ≫ qT := by
    calc
      φ₁ ≫ pJ = (s₁T ≫ cT) ≫ pJ := rfl
      _ = s₁T ≫ (cT ≫ pJ) := by simp [Category.assoc]
      _ = s₁T ≫ qT := by rw [hfactor]
  have hφ₀Bq : φ₀B ≫ pJ = 𝟙 B := by
    calc
      φ₀B ≫ pJ = (s₀B ≫ φ₀) ≫ pJ := rfl
      _ = s₀B ≫ (φ₀ ≫ pJ) := by simp [Category.assoc]
      _ = s₀B ≫ s₀toB := by rw [hφ₀q]
      _ = 𝟙 B := hs₀toB_B
  have hφ₁Bq : φ₁B ≫ pJ = 𝟙 B := by
    calc
      φ₁B ≫ pJ = (s₁B ≫ φ₁) ≫ pJ := rfl
      _ = s₁B ≫ (φ₁ ≫ pJ) := by simp [Category.assoc]
      _ = s₁B ≫ (s₁T ≫ qT) := by rw [hφ₁q]
      _ = (s₁B ≫ s₁T) ≫ qT := by simp [Category.assoc]
      _ = tB ≫ qT := by rw [hs₁TB]
      _ = 𝟙 B := hqT_B

  have hs₀Bweak : weakEquivalences C s₀B :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      e₀ i s₀I s₀B hS₀.flip heA.1.1 heA.1.2
  have hs₁Bweak : weakEquivalences C s₁B :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      e₁ i s₁I s₁B hS₁ heA.2.1 heA.2.2
  have hidB : weakEquivalences C (𝟙 B) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 B)
      (MorphismProperty.isomorphisms.infer_property (𝟙 B))
  have hφ₀p : weakEquivalences C (φ₀ ≫ pJ) := by
    have htotalEq : s₀B ≫ (φ₀ ≫ pJ) = 𝟙 B := by
      calc
        s₀B ≫ (φ₀ ≫ pJ) = (s₀B ≫ φ₀) ≫ pJ := by simp [Category.assoc]
        _ = φ₀B ≫ pJ := rfl
        _ = 𝟙 B := hφ₀Bq
    have htotal : weakEquivalences C (s₀B ≫ (φ₀ ≫ pJ)) := by
      simpa only [htotalEq] using hidB
    have h := IsCylinderCategory.twoOutOfSix (C := C) (𝟙 B) s₀B (φ₀ ≫ pJ)
      (by simpa using hs₀Bweak) (by simpa using htotal)
    exact h.2.2.1
  have hφ₁p : weakEquivalences C (φ₁ ≫ pJ) := by
    have htotalEq : s₁B ≫ (φ₁ ≫ pJ) = 𝟙 B := by
      calc
        s₁B ≫ (φ₁ ≫ pJ) = (s₁B ≫ φ₁) ≫ pJ := by simp [Category.assoc]
        _ = φ₁B ≫ pJ := rfl
        _ = 𝟙 B := hφ₁Bq
    have htotal : weakEquivalences C (s₁B ≫ (φ₁ ≫ pJ)) := by
      simpa only [htotalEq] using hidB
    have h := IsCylinderCategory.twoOutOfSix (C := C) (𝟙 B) s₁B (φ₁ ≫ pJ)
      (by simpa using hs₁Bweak) (by simpa using htotal)
    exact h.2.2.1
  have hφ₀weak : weakEquivalences C φ₀ := by
    have h := IsCylinderCategory.twoOutOfSix (C := C) φ₀ pJ (𝟙 B)
      (by simpa using hφ₀p) (by simpa using hpJ)
    exact h.1
  have hφ₁weak : weakEquivalences C φ₁ := by
    have h := IsCylinderCategory.twoOutOfSix (C := C) φ₁ pJ (𝟙 B)
      (by simpa using hφ₁p) (by simpa using hpJ)
    exact h.1

  have hS₁compat : Z.obj.map e₁.op (g.hom.app (op cylA.I) H) = Z.obj.map i.op z := by
    calc
      Z.obj.map e₁.op (g.hom.app (op cylA.I) H) =
          g.hom.app (op A) (Y.obj.map e₁.op H) := by rw [← NatTrans.naturality_apply]
      _ = g.hom.app (op A) y := by rw [hA₁]
      _ = Z.obj.map i.op z := hyz
  obtain ⟨zS₁, hzS₁I, hzS₁B⟩ := Types.exists_of_isPullback
    (Z.property.2 e₁ i s₁I s₁B hS₁ heA.2.1)
    (g.hom.app (op cylA.I) H) z hS₁compat
  obtain ⟨r₁, hr₁⟩ := IsCylinderCategory.exists_retraction (C := C) φ₁ hφ₁cof hφ₁weak
  have hφ₁r₁ : φ₁ ≫ r₁ = 𝟙 S₁ := hr₁
  let zTilde : Z.obj.obj (op J) := Z.obj.map r₁.op zS₁
  have hmS₁ : m = s₁I ≫ φ₁ := by
    dsimp [m, φ₀, φ₁]
    calc
      s₀I ≫ (tS₀ ≫ cT) = (s₀I ≫ tS₀) ≫ cT := by simp [Category.assoc]
      _ = tI ≫ cT := rfl
      _ = (s₁I ≫ s₁T) ≫ cT := by rw [hs₁TI]
      _ = s₁I ≫ (s₁T ≫ cT) := by simp [Category.assoc]
  have hmR₁ : m ≫ r₁ = s₁I := by
    calc
      m ≫ r₁ = (s₁I ≫ φ₁) ≫ r₁ := by rw [hmS₁]
      _ = s₁I ≫ (φ₁ ≫ r₁) := by simp [Category.assoc]
      _ = s₁I := by rw [hφ₁r₁]; simp
  have hk₁R₁ : φ₁B ≫ r₁ = s₁B := by
    calc
      φ₁B ≫ r₁ = (s₁B ≫ φ₁) ≫ r₁ := rfl
      _ = s₁B ≫ (φ₁ ≫ r₁) := by simp [Category.assoc]
      _ = s₁B := by rw [hφ₁r₁]; simp
  have hzTildeM : Z.obj.map m.op zTilde = g.hom.app (op cylA.I) H := by
    calc
      Z.obj.map m.op zTilde = Z.obj.map (m ≫ r₁).op zS₁ :=
        (presheafMap_comp_apply Z m r₁ zS₁).symm
      _ = Z.obj.map s₁I.op zS₁ := congrArg (fun q => Z.obj.map q.op zS₁) hmR₁
      _ = g.hom.app (op cylA.I) H := hzS₁I
  have hzTildeφ₁B : Z.obj.map φ₁B.op zTilde = z := by
    calc
      Z.obj.map φ₁B.op zTilde = Z.obj.map (φ₁B ≫ r₁).op zS₁ :=
        (presheafMap_comp_apply Z φ₁B r₁ zS₁).symm
      _ = Z.obj.map s₁B.op zS₁ := congrArg (fun q => Z.obj.map q.op zS₁) hk₁R₁
      _ = z := hzS₁B

  let z' : Z.obj.obj (op B) := Z.obj.map φ₀B.op zTilde
  have hiφ₀B : i ≫ φ₀B = e₀ ≫ m := by
    calc
      i ≫ φ₀B = (i ≫ s₀B) ≫ φ₀ := by simp [φ₀B, Category.assoc]
      _ = (e₀ ≫ s₀I) ≫ φ₀ := by rw [hS₀.w]
      _ = e₀ ≫ m := by simp [m, Category.assoc]
  have hz' : Z.obj.map i.op z' = g.hom.app (op A) (f.hom.app (op A) xA) := by
    calc
      Z.obj.map i.op z' = Z.obj.map i.op (Z.obj.map φ₀B.op zTilde) := rfl
      _ = Z.obj.map (i ≫ φ₀B).op zTilde :=
        (presheafMap_comp_apply Z i φ₀B zTilde).symm
      _ = Z.obj.map (e₀ ≫ m).op zTilde :=
        congrArg (fun q => Z.obj.map q.op zTilde) hiφ₀B
      _ = Z.obj.map e₀.op (Z.obj.map m.op zTilde) :=
        presheafMap_comp_apply Z e₀ m zTilde
      _ = Z.obj.map e₀.op (g.hom.app (op cylA.I) H) :=
        congrArg (Z.obj.map e₀.op) hzTildeM
      _ = g.hom.app (op A) (Y.obj.map e₀.op H) := by rw [← NatTrans.naturality_apply]
      _ = g.hom.app (op A) (f.hom.app (op A) xA) := by rw [hA₀]
  have hfgCompat : (f ≫ g).hom.app (op A) xA = Z.obj.map i.op z' := by
    calc
      (f ≫ g).hom.app (op A) xA =
          g.hom.app (op A) (f.hom.app (op A) xA) := rfl
      _ = Z.obj.map i.op z' := hz'.symm
  obtain ⟨l₀, hl₀, hfgHom⟩ :=
    (completion_weakEquivalence_iff_homotopyLift (f ≫ g)).mp hfg i hi xA z' hfgCompat

  have hYcompat : Y.obj.map i.op (f.hom.app (op B) l₀) = Y.obj.map e₀.op H := by
    calc
      Y.obj.map i.op (f.hom.app (op B) l₀) =
          f.hom.app (op A) (X.obj.map i.op l₀) := by rw [← NatTrans.naturality_apply]
      _ = f.hom.app (op A) xA := congrArg (f.hom.app (op A)) hl₀
      _ = Y.obj.map e₀.op H := hA₀.symm
  obtain ⟨yS₀, hyS₀B, hyS₀I⟩ := Types.exists_of_isPullback
    (Y.property.2 i e₀ s₀B s₀I hS₀ hi) (f.hom.app (op B) l₀) H hYcompat
  obtain ⟨r₀, hr₀⟩ := IsCylinderCategory.exists_retraction (C := C) φ₀ hφ₀cof hφ₀weak
  let yTilde : Y.obj.obj (op J) := Y.obj.map r₀.op yS₀
  have hφ₀B_r₀ : φ₀B ≫ r₀ = s₀B := by
    calc
      φ₀B ≫ r₀ = (s₀B ≫ φ₀) ≫ r₀ := rfl
      _ = s₀B ≫ (φ₀ ≫ r₀) := by simp [Category.assoc]
      _ = s₀B := by rw [hr₀]; simp
  have hm_r₀ : m ≫ r₀ = s₀I := by
    calc
      m ≫ r₀ = (s₀I ≫ φ₀) ≫ r₀ := rfl
      _ = s₀I ≫ (φ₀ ≫ r₀) := by simp [Category.assoc]
      _ = s₀I := by rw [hr₀]; simp
  have hyTildeK₀ : Y.obj.map φ₀B.op yTilde = f.hom.app (op B) l₀ := by
    calc
      Y.obj.map φ₀B.op yTilde = Y.obj.map (φ₀B ≫ r₀).op yS₀ :=
        (presheafMap_comp_apply Y φ₀B r₀ yS₀).symm
      _ = Y.obj.map s₀B.op yS₀ :=
        congrArg (fun q => Y.obj.map q.op yS₀) hφ₀B_r₀
      _ = f.hom.app (op B) l₀ := hyS₀B
  have hyTildeM : Y.obj.map m.op yTilde = H := by
    calc
      Y.obj.map m.op yTilde = Y.obj.map (m ≫ r₀).op yS₀ :=
        (presheafMap_comp_apply Y m r₀ yS₀).symm
      _ = Y.obj.map s₀I.op yS₀ := congrArg (fun q => Y.obj.map q.op yS₀) hm_r₀
      _ = H := hyS₀I

  have hiφ₁B : i ≫ φ₁B = e₁ ≫ m := by
    calc
      i ≫ φ₁B = (i ≫ s₁B) ≫ φ₁ := by simp [φ₁B, Category.assoc]
      _ = (e₁ ≫ s₁I) ≫ φ₁ := by rw [hS₁.w]
      _ = e₁ ≫ m := by rw [hmS₁]; simp [Category.assoc]
  let l : Y.obj.obj (op B) := Y.obj.map φ₁B.op yTilde
  have hl : Y.obj.map i.op l = y := by
    calc
      Y.obj.map i.op l = Y.obj.map (i ≫ φ₁B).op yTilde :=
        (presheafMap_comp_apply Y i φ₁B yTilde).symm
      _ = Y.obj.map (e₁ ≫ m).op yTilde :=
        congrArg (fun q => Y.obj.map q.op yTilde) hiφ₁B
      _ = Y.obj.map e₁.op (Y.obj.map m.op yTilde) :=
        presheafMap_comp_apply Y e₁ m yTilde
      _ = Y.obj.map e₁.op H := congrArg (Y.obj.map e₁.op) hyTildeM
      _ = y := hA₁

  let U : Z.obj.obj (op J) := g.hom.app (op J) yTilde
  let V : Z.obj.obj (op J) := zTilde
  have hUM : Z.obj.map m.op U = g.hom.app (op cylA.I) H := by
    calc
      Z.obj.map m.op U = g.hom.app (op cylA.I) (Y.obj.map m.op yTilde) := by
        rw [← NatTrans.naturality_apply]
      _ = g.hom.app (op cylA.I) H := congrArg (g.hom.app (op cylA.I)) hyTildeM
  have hVM : Z.obj.map m.op V = g.hom.app (op cylA.I) H := hzTildeM
  have hboundS₀ : Z.obj.map s₀I.op (Z.obj.map φ₀.op U) =
      Z.obj.map s₀I.op (Z.obj.map φ₀.op V) := by
    calc
      Z.obj.map s₀I.op (Z.obj.map φ₀.op U) = Z.obj.map (s₀I ≫ φ₀).op U :=
        (presheafMap_comp_apply Z s₀I φ₀ U).symm
      _ = Z.obj.map m.op U := rfl
      _ = Z.obj.map m.op V := by rw [hUM, hVM]
      _ = Z.obj.map s₀I.op (Z.obj.map φ₀.op V) :=
        presheafMap_comp_apply Z s₀I φ₀ V
  have hUφ₀B : Z.obj.map φ₀B.op U = (f ≫ g).hom.app (op B) l₀ := by
    calc
      Z.obj.map φ₀B.op U = g.hom.app (op B) (Y.obj.map φ₀B.op yTilde) := by
        rw [← NatTrans.naturality_apply]
      _ = g.hom.app (op B) (f.hom.app (op B) l₀) :=
        congrArg (g.hom.app (op B)) hyTildeK₀
      _ = (f ≫ g).hom.app (op B) l₀ := by rfl
  have hVφ₀B : Z.obj.map φ₀B.op V = z' := rfl
  have hbaseB : PresheafRelHomotopic i Z
      (Z.obj.map φ₀B.op U) (Z.obj.map φ₀B.op V) := by
    rw [hUφ₀B, hVφ₀B]
    exact hfgHom
  have hbaseS₀ : PresheafRelHomotopic i Z
      (Z.obj.map s₀B.op (Z.obj.map φ₀.op U))
      (Z.obj.map s₀B.op (Z.obj.map φ₀.op V)) := by
    simpa only [φ₀B, presheafMap_comp_apply] using hbaseB
  have hs₀Icof : cofibrations C s₀I :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hS₀.flip hi
  have hUVS₀ := presheafRelHomotopic_pushout i e₀ s₀B s₀I hS₀ hi
    hboundS₀ hbaseS₀
  have hUVm := presheafRelHomotopic_trivialCofibration
    (Z := Z) s₀I φ₀ hs₀Icof hφ₀cof hφ₀weak U V hUVS₀
  have hUVk := presheafRelHomotopic_precomp (i := m) (i' := i)
    e₁ φ₁B hiφ₁B hi hUVm
  have hUφ₁B : Z.obj.map φ₁B.op U = g.hom.app (op B) l := by
    calc
      Z.obj.map φ₁B.op U = g.hom.app (op B) (Y.obj.map φ₁B.op yTilde) := by
        rw [← NatTrans.naturality_apply]
      _ = g.hom.app (op B) l := rfl
  have hVφ₁B : Z.obj.map φ₁B.op V = z := hzTildeφ₁B
  have hfinal : PresheafRelHomotopic i Z (g.hom.app (op B) l) z := by
    rw [← hUφ₁B, ← hVφ₁B]
    exact hUVk
  exact ⟨l, hl, hfinal⟩

end HomotopyHypothesis.Category.SemiModelStructure
