import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Basic
namespace HomotopyHypothesis.Cylinder.PreCylinderCategory

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe v u

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

/-- Weak equivalences respect isomorphisms (from isos ≤ W and composition). -/
instance we_respectsIso [IsCylinderCategory C] : (weakEquivalences C).RespectsIso where
  precomp e he f hf := by
    have he' : weakEquivalences C e :=
      IsCylinderCategory.isomorphisms_le_weakEquivalences _ he
    exact IsCylinderCategory.weakEquivalences_isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ he' hf
  postcomp e he f hf := by
    have he' : weakEquivalences C e :=
      IsCylinderCategory.isomorphisms_le_weakEquivalences _ he
    exact IsCylinderCategory.weakEquivalences_isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ hf he'

/-- Cofibrations respect isomorphisms. -/
instance cof_respectsIso [IsCofibrationCategory C] : (cofibrations C).RespectsIso where
  precomp e he f hf := by
    have he' : cofibrations C e :=
      IsCofibrationCategory.isomorphisms_le _ he
    exact IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem _ _ he' hf
  postcomp e he f hf := by
    have he' : cofibrations C e :=
      IsCofibrationCategory.isomorphisms_le _ he
    exact IsCofibrationCategory.isMultiplicative.toIsStableUnderComposition.comp_mem _ _ hf he'

/-- Horizontal pasting of pushout squares (left then right, sharing the middle vertical edge).
If `h₁ : IsPushout f₁ i₁ i₂ g₁` and `h₂ : IsPushout f₂ i₂ i₃ g₂` then the outer
rectangle `IsPushout (f₁ ≫ f₂) i₁ i₃ (g₁ ≫ g₂)` holds. -/
theorem IsPushout.paste_horiz {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {i₁ : X₁ ⟶ Y₁} {i₂ : X₂ ⟶ Y₂} {i₃ : X₃ ⟶ Y₃}
    {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃}
    (h₁ : IsPushout f₁ i₁ i₂ g₁) (h₂ : IsPushout f₂ i₂ i₃ g₂) :
    IsPushout (f₁ ≫ f₂) i₁ i₃ (g₁ ≫ g₂) := by
  have h₁' : IsPushout i₁ f₁ g₁ i₂ := h₁.flip
  have h₂' : IsPushout i₂ f₂ g₂ i₃ := h₂.flip
  let t₁ : PushoutCocone i₁ f₁ := h₁'.cocone
  let t₂ : PushoutCocone i₂ f₂ := h₂'.cocone
  have hc₁ : IsColimit t₁ := h₁'.isColimit
  have hc₂ : IsColimit t₂ := h₂'.isColimit
  have hi₂ : i₂ = t₁.inr := rfl
  have hcol : IsColimit (t₁.pasteHoriz t₂ hi₂) :=
    pasteHorizIsPushout _ hc₁ hc₂
  -- the pasted cocone is PushoutCocone i₁ (f₁≫f₂) with inl = g₁≫g₂, inr = i₃
  have hout : IsPushout i₁ (f₁ ≫ f₂) (g₁ ≫ g₂) i₃ :=
    IsPushout.of_isColimit hcol
  exact hout.flip

/-- Vertical pasting of pushout squares (top over bottom, sharing the middle horizontal edge).
If `h_top : IsPushout g₂ i₃ i₂ f₂` (top square with top g₂, left i₃) and
`h_bot : IsPushout g₁ i₂ f₁' f₁`... -/
-- General vertical paste: top square h_top : IsPushout g₂ i₃ i₂ f₂, bottom square
-- h_bot : IsPushout g₁ i₂ f₁' f₁ gives outer IsPushout (g₂≫g₁) i₃ f₁' (f₂≫f₁).
theorem IsPushout.paste_vert {Y₃ Y₂ Y₁ X₃ X₂ X₁ : C}
    {g₂ : Y₃ ⟶ Y₂} {g₁ : Y₂ ⟶ Y₁} {i₃ : Y₃ ⟶ X₃} {i₂ : Y₂ ⟶ X₂}
    {f₂ : X₃ ⟶ X₂} {f₁ : X₂ ⟶ X₁} {bot₁ : Y₁ ⟶ X₁}
    (h_top : IsPushout g₂ i₃ i₂ f₂) (h_bot : IsPushout g₁ i₂ bot₁ f₁) :
    IsPushout (g₂ ≫ g₁) i₃ bot₁ (f₂ ≫ f₁) := by
  let t₁ : PushoutCocone g₂ i₃ := h_top.cocone
  let t₂ : PushoutCocone g₁ i₂ := h_bot.cocone
  have hc₁ : IsColimit t₁ := h_top.isColimit
  have hc₂ : IsColimit t₂ := h_bot.isColimit
  have hi₂ : i₂ = t₁.inl := rfl
  have hcol : IsColimit (t₁.pasteVert t₂ hi₂) :=
    pasteVertIsPushout _ hc₁ hc₂
  exact IsPushout.of_isColimit hcol

end HomotopyHypothesis.Cylinder.PreCylinderCategory
