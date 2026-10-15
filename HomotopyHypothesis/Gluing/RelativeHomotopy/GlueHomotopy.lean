import Mathlib
/-!
# Gluing homotopies over a pushout of spaces

A homotopy relative to `A` on one leg of a pushout square, together with equality on the other
leg, glues to a homotopy on the pushout relative to the image of the other leg (curry the homotopy
into the compact-open mapping space and use the pushout there; the interval is locally compact).
-/

universe u

open CategoryTheory Limits TopCat

namespace HomotopyHypothesis.Gluing.RelativeHomotopy

/-- A homotopy on one side of a pushout, fixed on the overlap, extends by the constant homotopy
on the other side. -/
theorem homotopicRel_of_isPushout_proof {A D X P Z : TopCat.{u}} {t : A ⟶ D} {l : A ⟶ X}
    {r : D ⟶ P} {b : X ⟶ P} (sq : IsPushout t l r b) {f g : P ⟶ Z}
    (hb : b ≫ f = b ≫ g)
    (hr : (r ≫ f).hom.HomotopicRel (r ≫ g).hom (Set.range t.hom)) :
    f.hom.HomotopicRel g.hom (Set.range b.hom) := by
  classical
  obtain ⟨H⟩ := hr
  let HD : D ⟶ TopCat.of C(unitInterval, Z) :=
    TopCat.ofHom <| ContinuousMap.curry (H.toHomotopy.toContinuousMap.comp ContinuousMap.prodSwap)
  let HX : X ⟶ TopCat.of C(unitInterval, Z) :=
    TopCat.ofHom <| ContinuousMap.curry ((b ≫ f).hom.comp ContinuousMap.fst)
  have hcompat : t ≫ HD = l ≫ HX := by
    apply TopCat.hom_ext
    ext a s
    change H (s, t.hom a) = (b ≫ f).hom (l.hom a)
    rw [H.eq_fst s ⟨a, rfl⟩]
    have hsq : r.hom (t.hom a) = b.hom (l.hom a) :=
      congrArg (fun k : A ⟶ P => k.hom a) sq.w
    calc
      (r ≫ f).hom (t.hom a) = f.hom (r.hom (t.hom a)) := rfl
      _ = f.hom (b.hom (l.hom a)) := congrArg f.hom hsq
      _ = (b ≫ f).hom (l.hom a) := rfl
  let Φ : P ⟶ TopCat.of C(unitInterval, Z) := sq.desc HD HX hcompat
  have hΦD : r ≫ Φ = HD := by
    change r ≫ sq.desc HD HX hcompat = HD
    exact sq.inl_desc HD HX hcompat
  have hΦX : b ≫ Φ = HX := by
    change b ≫ sq.desc HD HX hcompat = HX
    exact sq.inr_desc HD HX hcompat
  let z₀ : C(P, Z) := Φ.hom.uncurry.comp
    (ContinuousMap.prodMk (ContinuousMap.id P) (ContinuousMap.const P (0 : unitInterval)))
  let z₁ : C(P, Z) := Φ.hom.uncurry.comp
    (ContinuousMap.prodMk (ContinuousMap.id P) (ContinuousMap.const P (1 : unitInterval)))
  have hz₀' : TopCat.ofHom z₀ = f := by
    apply sq.hom_ext
    · apply TopCat.ext
      intro d
      change z₀ (r.hom d) = f.hom (r.hom d)
      calc
        z₀ (r.hom d) = (Φ.hom (r.hom d)) 0 := rfl
        _ = (HD.hom d) 0 := by
          have hq := ContinuousMap.congr_fun (congrArg Hom.hom hΦD) d
          simpa [TopCat.hom_comp] using congrArg (fun m : C(unitInterval, Z) => m 0) hq
        _ = (r ≫ f).hom d := by simp [HD, ContinuousMap.curry_apply]
        _ = f.hom (r.hom d) := rfl
    · apply TopCat.ext
      intro x
      change z₀ (b.hom x) = f.hom (b.hom x)
      calc
        z₀ (b.hom x) = (Φ.hom (b.hom x)) 0 := rfl
        _ = (HX.hom x) 0 := by
          have hq := ContinuousMap.congr_fun (congrArg Hom.hom hΦX) x
          simpa [TopCat.hom_comp] using congrArg (fun m : C(unitInterval, Z) => m 0) hq
        _ = (b ≫ f).hom x := by simp [HX, ContinuousMap.curry_apply]
        _ = f.hom (b.hom x) := rfl
  have hz₁' : TopCat.ofHom z₁ = g := by
    apply sq.hom_ext
    · apply TopCat.ext
      intro d
      change z₁ (r.hom d) = g.hom (r.hom d)
      calc
        z₁ (r.hom d) = (Φ.hom (r.hom d)) 1 := rfl
        _ = (HD.hom d) 1 := by
          have hq := ContinuousMap.congr_fun (congrArg Hom.hom hΦD) d
          simpa [TopCat.hom_comp] using congrArg (fun m : C(unitInterval, Z) => m 1) hq
        _ = (r ≫ g).hom d := by simp [HD, ContinuousMap.curry_apply]
        _ = g.hom (r.hom d) := rfl
    · apply TopCat.ext
      intro x
      change z₁ (b.hom x) = g.hom (b.hom x)
      calc
        z₁ (b.hom x) = (Φ.hom (b.hom x)) 1 := rfl
        _ = (HX.hom x) 1 := by
          have hq := ContinuousMap.congr_fun (congrArg Hom.hom hΦX) x
          simpa [TopCat.hom_comp] using congrArg (fun m : C(unitInterval, Z) => m 1) hq
        _ = (b ≫ f).hom x := by simp [HX, ContinuousMap.curry_apply]
        _ = g.hom (b.hom x) := by
          have hb' := ContinuousMap.congr_fun (congrArg Hom.hom hb) x
          simpa [TopCat.hom_comp] using hb'
  have hz₀ : z₀ = f.hom := congrArg Hom.hom hz₀'
  have hz₁ : z₁ = g.hom := congrArg Hom.hom hz₁'
  let K : ContinuousMap.Homotopy f.hom g.hom := {
    toFun := fun p => Φ.hom.uncurry (p.2, p.1)
    continuous_toFun := (Φ.hom.uncurry).continuous.comp ContinuousMap.prodSwap.continuous
    map_zero_left := by
      intro p
      change z₀ p = f.hom p
      exact ContinuousMap.congr_fun hz₀ p
    map_one_left := by
      intro p
      change z₁ p = g.hom p
      exact ContinuousMap.congr_fun hz₁ p
  }
  refine ⟨{ toHomotopy := K, prop' := ?_ }⟩
  intro s p hp
  rcases hp with ⟨x, rfl⟩
  change Φ.hom.uncurry (b.hom x, s) = f.hom (b.hom x)
  calc
    Φ.hom.uncurry (b.hom x, s) = (Φ.hom (b.hom x)) s := rfl
    _ = (HX.hom x) s := by
      have hq := ContinuousMap.congr_fun (congrArg Hom.hom hΦX) x
      simpa [TopCat.hom_comp] using congrArg (fun m : C(unitInterval, Z) => m s) hq
    _ = (b ≫ f).hom x := by simp [HX, ContinuousMap.curry_apply]
    _ = f.hom (b.hom x) := rfl

#print axioms HomotopyHypothesis.Gluing.RelativeHomotopy.homotopicRel_of_isPushout_proof

end HomotopyHypothesis.Gluing.RelativeHomotopy
