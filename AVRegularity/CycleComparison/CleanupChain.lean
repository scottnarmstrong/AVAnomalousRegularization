-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
public import AVRegularity.CycleComparison.CleanupChain.Main

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Algebraic vanishing of the lift source flux on constant coarse fields. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ}

private theorem dEpsWord_const_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η ε : ℝ) {m : ℕ} (α : DerivativeWord2 m) (c₀ : E)
    (hm : 1 ≤ m) :
    dEpsWord η ε α (fun _ _ => c₀) = 0 := by
  have hne : (List.ofFn α).length ≠ 0 := by
    simp only [List.length_ofFn]
    omega
  have hne' : List.ofFn α ≠ [] := by
    intro hnil
    apply hne
    simp [hnil]
  cases hl : List.ofFn α with
  | nil => exact (hne' hl).elim
  | cons i is =>
      have hconst : dEps η ε i (fun _ _ => c₀) = 0 := by
        funext X z
        simp [dEps, fastPartial, slowPartial]
      have hzero : ∀ l : List (Fin 2),
          l.foldl (fun Ψ' j => dEps η ε j Ψ') (0 : Vec 2 → Vec 2 → E) = 0 := by
        intro l
        induction l with
        | nil => rfl
        | cons j l ih =>
            rw [List.foldl_cons]
            have hmap : dEps η ε j (0 : Vec 2 → Vec 2 → E) = 0 := by
              funext X' z'
              simp [dEps, fastPartial, slowPartial]
            rw [hmap]
            exact ih
      funext X z
      rw [dEpsWord, hl, List.foldl_cons, hconst]
      exact congrFun (congrFun (hzero is) X) z

theorem sourceFlux_const_eq_zero (edge : ConstituentEdges D h) (η ε t : ℝ)
    (c₀ : ∀ i, h i) (k : Fin 2) :
    sourceFlux edge η ε t (fun _ _ => c₀) k = 0 := by
  funext X z v
  change (∑ u : ι, ∑ d : Finset.Icc 2 D,
    ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
      (γ.coeff α t X z k) • γ.map (dEpsWord η ε α (fun _ _ => c₀) X z u)).sum) = 0
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro d hd
  have hd' : 2 ≤ d.1 := (Finset.mem_Icc.mp d.2).1
  have hword : ∀ α : DerivativeWord2 (d.1 - 1),
      dEpsWord η ε α (fun _ _ => c₀) X z u = 0 := by
    intro α
    have hm : 1 ≤ d.1 - 1 := by omega
    have hzero := dEpsWord_const_eq_zero (E := ∀ i, h i) η ε α c₀ hm
    have hpoint : dEpsWord η ε α (fun _ _ => c₀) X z = 0 :=
      congrFun (congrFun hzero X) z
    exact congrFun hpoint u
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hy
  apply Finset.sum_eq_zero
  intro α _
  have hpoint := hword α
  simp [hpoint]

theorem sourceFluxCoeff_const_eq_zero (edge : ConstituentEdges D h) (η : ℝ)
    (j : ℕ) (t : ℝ) (c₀ : ∀ i, h i) (k : Fin 2) :
    sourceFluxCoeff edge η j t (fun _ _ _ => c₀) k = 0 := by
  funext X z v
  simp [sourceFluxCoeff, sourceFlux_const_eq_zero]

end AVRegularity
end
end

section
/-! Facade: existence of the cleanup chain `V₀ = F₀ + 𝒜_z f₀`, `V_j = 𝒜_z(-div_X V_{j-1})`
(`AVRegularity.CleanupChain.exists_isCleanupChain`), built from the Fourier solver with a slow
parameter on `ℓ²(ℤ²; ℂ)`-valued coefficient maps. -/
end
