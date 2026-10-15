import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.FiniteCategory.Restriction.Unit
import HomotopyHypothesis.FiniteCategory.UnitPresentation.Flatten
import HomotopyHypothesis.FiniteCategory.UnitPresentation.Unit
/-!
# Single-cell presentations of cellular objects

A countable sequence of coproducts of representable boundary cells admits a refinement
which attaches one cell at a time. The refinement uses a well-order on the set of cells.
-/

noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

local instance : OrderBot Cardinal.aleph0.{u}.ord.ToType :=
  Cardinal.orderBotAleph0OrdToType

namespace HomotopyHypothesis.FiniteCategory.UnitWeakEquivalence

/-- Cellular objects of the completion placeholder single-cell presentations. -/
theorem singleCellPresentation : FiniteCategory.UnitPresentation.SingleCellPresentationStatement.{u} := by
  haveI : HasColimitsOfSize.{u, u} (Completion.{u} FinCell.{u}) :=
    FiniteCategory.Restriction.finCellCompletion_hasColimits
  haveI : NoMaxOrder Cardinal.aleph0.{u}.ord.ToType := Cardinal.noMaxOrder le_rfl
  have hJ : ∀ j : Cardinal.aleph0.{u}.ord.ToType, ¬ Order.IsSuccLimit j := by
    let e : ℕ ≃o Cardinal.aleph0.{u}.ord.ToType :=
      ULift.orderIso.{u}.symm.trans
        (OrderIso.ofRelIsoLT (Nonempty.some (by simp [← Ordinal.type_eq])))
    intro j
    obtain ⟨n, rfl⟩ := e.surjective j
    cases n with
    | zero =>
      have he : e 0 = ⊥ := e.map_bot
      rw [he]
      exact Order.not_isSuccLimit_bot
    | succ n =>
      have he : e (n + 1) = Order.succ (e n) := e.map_succ n
      rw [he]
      exact Order.not_isSuccLimit_succ _
  intro I C hI hc
  obtain ⟨c⟩ := hc
  refine ⟨FiniteCategory.UnitPresentation.Flatten.Idx c, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  exact ⟨FiniteCategory.UnitPresentation.Flatten.transfiniteComposition (c := c) hJ
    FiniteCategory.Restriction.finCellBoundaryGenerators (fun _ i => i.property)⟩

end HomotopyHypothesis.FiniteCategory.UnitWeakEquivalence
