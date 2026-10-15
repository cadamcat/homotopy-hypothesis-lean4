import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Code
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Rank
/-!
# Face maps between derived double cylinders

A face `θ : [n'] ⟶ [n]` and an increasing injection `ι : [m'] ⟶ [m]` with `v ∘ θ = ι ∘ v'` induce
a map `dcylD v' ⟶ dcylD v` (top and middle vertices along `θ`, bottom vertices along `ι`).
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet DV

namespace DV

variable {n m : ℕ}

theorem lt_iff_rank {a b : DV n m} : a < b ↔ rank a < rank b := Iff.rfl

theorem mid_lt_top (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) : (mid S : DV n m) < top i := by
  rw [lt_iff_rank]; simp [rank, Prod.Lex.toLex_lt_toLex]

theorem top_lt_bot (i : Fin (n + 1)) (c : Fin (m + 1)) : (top i : DV n m) < bot c := by
  rw [lt_iff_rank]; simp [rank, Prod.Lex.toLex_lt_toLex]

theorem mid_lt_bot (S : Finset (Fin (n + 1))) (c : Fin (m + 1)) : (mid S : DV n m) < bot c := by
  rw [lt_iff_rank]; simp [rank, Prod.Lex.toLex_lt_toLex]

theorem top_lt_top {i i' : Fin (n + 1)} : (top i : DV n m) < top i' ↔ i < i' := by
  rw [lt_iff_rank]; simp [rank, Prod.Lex.toLex_lt_toLex]

theorem bot_lt_bot {c c' : Fin (m + 1)} : (bot c : DV n m) < bot c' ↔ c < c' := by
  rw [lt_iff_rank]; simp [rank, Prod.Lex.toLex_lt_toLex]

theorem mid_lt_mid_of_card {S S' : Finset (Fin (n + 1))} (h : S'.card < S.card) :
    (mid S : DV n m) < mid S' := by
  have h1 : S.card ≤ n + 1 := by simpa using S.card_le_univ
  rw [lt_iff_rank]
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inl (by omega))⟩)

theorem not_mid_lt_mid_of_card {S S' : Finset (Fin (n + 1))} (h : S'.card < S.card) :
    ¬ (mid S' : DV n m) < mid S := fun h' =>
  lt_asymm (mid_lt_mid_of_card (m := m) h) h'

end DV

/-- The vertex map of a face of derived double cylinders. -/
def DV.mapV {n n' m m' : ℕ} (θ : Fin (n' + 1) ↪ Fin (n + 1)) (ι : Fin (m' + 1) → Fin (m + 1)) :
    DV n' m' → DV n m
  | top i => top (θ i)
  | mid S => mid (S.map θ)
  | bot c => bot (ι c)

/-- The map of derived double cylinders induced by a face `θ` and an increasing injection `ι` with
`v ∘ θ = ι ∘ v'`. -/
def dcylDMapHom {n n' m m' : ℕ} {v : Fin (n + 1) → Fin (m + 1)} {v' : Fin (n' + 1) → Fin (m' + 1)}
    (θ : Fin (n' + 1) ↪ Fin (n + 1)) (hθ : StrictMono θ) (ι : Fin (m' + 1) → Fin (m + 1))
    (hι : StrictMono ι) (h : v ∘ θ = ι ∘ v') :
    (dcylDComplex v').Hom (dcylDComplex v) where
  f := DV.mapV θ ι
  strictMonoOn A hA := by
    intro a ha b hb hab
    cases a with
    | top i =>
      cases b with
      | top i' => exact DV.top_lt_top.2 (hθ (DV.top_lt_top.1 hab))
      | mid S' => exact absurd hab (not_lt.2 (le_of_lt (DV.mid_lt_top _ _)))
      | bot c' => exact DV.top_lt_bot _ _
    | mid S =>
      cases b with
      | top i' => exact DV.mid_lt_top _ _
      | mid S' =>
        have hne : S ≠ S' := by rintro rfl; exact lt_irrefl _ hab
        have hcard : S'.card < S.card := by
          rcases hA.2.1 S S' ha hb with hSS' | hS'S
          · exact absurd hab (DV.not_mid_lt_mid_of_card
              (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hSS', hne⟩)))
          · exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hS'S, hne.symm⟩)
        exact DV.mid_lt_mid_of_card (by simpa using hcard)
      | bot c' => exact DV.mid_lt_bot _ _
    | bot c =>
      cases b with
      | top i' => exact absurd hab (not_lt.2 (le_of_lt (DV.top_lt_bot _ _)))
      | mid S' => exact absurd hab (not_lt.2 (le_of_lt (DV.mid_lt_bot _ _)))
      | bot c' => exact DV.bot_lt_bot.2 (hι (DV.bot_lt_bot.1 hab))
  map_S A hA := by
    have mem_top : ∀ i', top i' ∈ A.image (DV.mapV θ ι) → ∃ i, top i ∈ A ∧ θ i = i' := by
      intro i' hi'
      obtain ⟨a, ha, hfa⟩ := Finset.mem_image.1 hi'
      cases a with
      | top i => exact ⟨i, ha, by simpa [DV.mapV] using hfa⟩
      | mid S => simp [DV.mapV] at hfa
      | bot c => simp [DV.mapV] at hfa
    have mem_mid : ∀ T, mid T ∈ A.image (DV.mapV θ ι) → ∃ S, mid S ∈ A ∧ S.map θ = T := by
      intro T hT
      obtain ⟨a, ha, hfa⟩ := Finset.mem_image.1 hT
      cases a with
      | top i => simp [DV.mapV] at hfa
      | mid S => exact ⟨S, ha, by simpa [DV.mapV] using hfa⟩
      | bot c => simp [DV.mapV] at hfa
    have mem_bot : ∀ c', bot c' ∈ A.image (DV.mapV θ ι) → ∃ c, bot c ∈ A ∧ ι c = c' := by
      intro c' hc'
      obtain ⟨a, ha, hfa⟩ := Finset.mem_image.1 hc'
      cases a with
      | top i => simp [DV.mapV] at hfa
      | mid S => simp [DV.mapV] at hfa
      | bot c => exact ⟨c, ha, by simpa [DV.mapV] using hfa⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro T hT
      obtain ⟨S, hS, rfl⟩ := mem_mid T hT
      exact (hA.1 S hS).map
    · intro T T' hT hT'
      obtain ⟨S, hS, rfl⟩ := mem_mid T hT
      obtain ⟨S', hS', rfl⟩ := mem_mid T' hT'
      rcases hA.2.1 S S' hS hS' with h' | h'
      · exact Or.inl (Finset.map_subset_map.2 h')
      · exact Or.inr (Finset.map_subset_map.2 h')
    · intro i' c' hi' hc'
      obtain ⟨i, hi, rfl⟩ := mem_top i' hi'
      obtain ⟨c, hc, rfl⟩ := mem_bot c' hc'
      exact hA.2.2.1 i c hi hc
    · intro i' T hi' hT
      obtain ⟨i, hi, rfl⟩ := mem_top i' hi'
      obtain ⟨S, hS, rfl⟩ := mem_mid T hT
      exact Finset.mem_map_of_mem θ (hA.2.2.2.1 i S hi hS)
    · intro c' T hc' hT
      obtain ⟨c, hc, rfl⟩ := mem_bot c' hc'
      obtain ⟨S, hS, rfl⟩ := mem_mid T hT
      obtain ⟨k, hk, hvk⟩ := hA.2.2.2.2 c S hc hS
      refine ⟨θ k, Finset.mem_map_of_mem θ hk, ?_⟩
      have := congrFun h k
      simp only [Function.comp_apply] at this
      rw [this, hvk]

end HomotopyHypothesis.Approximation.Topological
