import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.Boundary.RealizationGeometry
universe u

open CategoryTheory Limits Opposite Convexity
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Simplicial.CycleRealization

abbrev face {n : ℕ} (i : Fin (n + 2)) :
    HomotopyHypothesis.Henry.SemiSimplexCategory.mk n ⟶ HomotopyHypothesis.Henry.SemiSimplexCategory.mk (n + 1) :=
  ⟨SimplexCategory.δ i, inferInstance⟩

/-- An injective simplex map avoiding a vertex factors through the opposite face. -/
theorem factor_face {m n : ℕ}
    (f : HomotopyHypothesis.Henry.SemiSimplexCategory.mk m ⟶ HomotopyHypothesis.Henry.SemiSimplexCategory.mk (n + 1))
    (i : Fin (n + 2)) (hi : i ∉ Set.range f.hom.toOrderHom) :
    ∃ g : HomotopyHypothesis.Henry.SemiSimplexCategory.mk m ⟶ HomotopyHypothesis.Henry.SemiSimplexCategory.mk n, g ≫ face i = f := by
  let g := SimplexCategory.factor_δ f.hom i
  have hg : g ≫ SimplexCategory.δ i = f.hom :=
    SimplexCategory.factor_δ_spec f.hom i (fun k hk => hi ⟨k, hk⟩)
  have hmono : Mono g := by
    letI : Mono f.hom := f.property
    exact mono_of_mono_fac hg
  exact ⟨⟨g, hmono⟩, by apply WideSubcategory.hom_ext; exact hg⟩

/-- Vanishing at a vertex allows restriction to the opposite face. -/
theorem exists_preimage_face {n : ℕ} (i : Fin (n + 2))
    (t : StdSimplex ℝ (Fin (n + 2))) (ht : t.weights i = 0) :
    ∃ s : StdSimplex ℝ (Fin (n + 1)),
      StdSimplex.map (face i).hom.toOrderHom s = t := by
  apply (StdSimplex.mem_range_map_iff _ _).mpr
  intro j hj
  have hji : j = i := by
    by_contra hne
    apply hj
    change j ∈ Set.range (Fin.succAboveOrderEmb i)
    simpa [Fin.range_succAboveOrderEmb] using hne
  simpa [hji] using ht

/-- A point mapping into a face admits a representative whose simplex map factors through it. -/
theorem restrict_to_face {m n : ℕ}
    (f : HomotopyHypothesis.Henry.SemiSimplexCategory.mk m ⟶ HomotopyHypothesis.Henry.SemiSimplexCategory.mk (n + 1))
    (s : StdSimplex ℝ (Fin (m + 1))) (i : Fin (n + 2))
    (hi : (StdSimplex.map f.hom.toOrderHom s).weights i = 0) :
    ∃ (k : ℕ) (g : HomotopyHypothesis.Henry.SemiSimplexCategory.mk k ⟶ HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)
      (h : HomotopyHypothesis.Henry.SemiSimplexCategory.mk k ⟶ HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
      (r : StdSimplex ℝ (Fin (k + 1))),
      g ≫ f = h ≫ face i ∧ StdSimplex.map g.hom.toOrderHom r = s := by
  classical
  by_cases hmiss : i ∉ Set.range f.hom.toOrderHom
  · obtain ⟨h, hh⟩ := factor_face f i hmiss
    exact ⟨m, 𝟙 _, h, s, by simpa using hh.symm, by simp⟩
  · push Not at hmiss
    obtain ⟨j, hj⟩ := hmiss
    have hinj : Function.Injective f.hom.toOrderHom :=
      SimplexCategory.mono_iff_injective.mp f.property
    have hsj : s.weights j = 0 := by
      rw [← hj] at hi
      simpa only [StdSimplex.weights_map,
        Finsupp.mapDomain_apply_of_injective hinj] using hi
    cases m with
    | zero =>
      have htotal : s.weights j = 1 := by
        fin_cases j
        simpa using s.total_of_fintype
      exact False.elim (by linarith)
    | succ m =>
      obtain ⟨r, hr⟩ := exists_preimage_face j s hsj
      have havoid : i ∉ Set.range ((face j ≫ f).hom.toOrderHom) := by
        rintro ⟨a, ha⟩
        have heq : (face j).hom.toOrderHom a = j := hinj (ha.trans hj.symm)
        exact (Fin.succAbove_ne j a) heq
      obtain ⟨h, hh⟩ := factor_face (face j ≫ f) i havoid
      exact ⟨m, face j, h, r, hh.symm, hr⟩

end HomotopyHypothesis.Simplicial.CycleRealization
