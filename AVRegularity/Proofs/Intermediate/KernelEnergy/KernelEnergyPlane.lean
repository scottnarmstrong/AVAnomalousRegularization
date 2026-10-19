-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.KernelEnergyPlane.PlaneKernelComponentSup
public import AVRegularity.Statements.Intermediate.CoupledEnergy.DriftCoefficient
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
public import AVRegularity.Statements.Intermediate.KernelEnergy.KernelSchurMatrix
public import AVRegularity.Statements.Intermediate.KernelEnergy.KernelWeakSolutionPlane
public import AVRegularity.Statements.Intermediate.KernelEnergy.SchurBound
public import AVRegularity.Statements.Intermediate.KernelEnergy.SpatialRegularizer

/-! The plane kernel-energy statement. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergyPlane AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Providers

theorem kernel_energy_plane (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (ρ : ℝ) (hρ : 0 < ρ)
    (ν : ℝ) (hν : 0 < ν) (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ‖v t x‖ ≤ C)
    (hv_meas : Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => v p.1 p.2)
    (hv_smooth : ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hv_div : ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ∑ m : Fin 2, fderiv ℝ (v t) x (basisVec m) m = 0)
    (a B₀ lam : ℝ) (ha : 0 ≤ a) (hB₀ : 1 ≤ B₀) (hlam : 0 < lam) (k : ℕ)
    (hjets : ∀ l : ℕ, 1 ≤ l → l ≤ k → ∀ t ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hB : B₀ * ρ / lam ≤ 1 / 2) (hab : a * B₀ * ρ ^ 2 ≤ ν / 8)
    (D : ℕ) (hD : 2 ≤ D)
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hB_meas : ∀ i j α d, Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => B i j α d p.1 p.2)
    (hB_smooth : ∀ i j α d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (k : ℕ) (B i j α d t))
    (hB_fin : ∀ i j α d, coefficientSeminorm ρ k t₀ t₁ (B i j α d) ≠ ⊤)
    (C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α)
    (S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict (Set.univ : Set (Vec 2)))) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict (Set.univ : Set (Vec 2)))))
    (c : ℕ → ℝ) (r : ∀ i j, Γ i j → ℝ) (hr : ∀ i j α, 0 < r i j α)
    (hS : ∀ i j α, IsSpatialRegularizer ρ k D t₀ t₁ c (r i j α) (S i j α))
    (θ : ℝ) (hθ : θ ≤ 1 / 8)
    (hschur : SchurBound θ (kernelSchurMatrix ν ρ π k D t₀ t₁ c r C B))
    (f : ∀ i, PlaneHk Set.univ k (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc t₀ t₁)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc t₀ t₁))) :
    (∃ (u : ∀ i, ℝ → PlaneHk Set.univ k (h i)) (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
      (y : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k + D - 1) (G i j α)),
      IsKernelWeakSolutionPlane ν t₀ t₁ v k D B C S f F g u w y) ∧
    (∀ (u u' : ∀ i, ℝ → PlaneHk Set.univ k (h i))
      (w w' : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
      (y y' : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k + D - 1) (G i j α)),
      IsKernelWeakSolutionPlane ν t₀ t₁ v k D B C S f F g u w y →
      IsKernelWeakSolutionPlane ν t₀ t₁ v k D B C S f F g u' w' y' →
      ∀ i, ∀ t ∈ Set.Icc t₀ t₁, u i t = u' i t) ∧
    (∀ (u : ∀ i, ℝ → PlaneHk Set.univ k (h i)) (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
      (y : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k + D - 1) (G i j α)),
      IsKernelWeakSolutionPlane ν t₀ t₁ v k D B C S f F g u w y →
      ∀ s ∈ Set.Icc t₀ t₁,
        IsKernelWeakSolutionPlane ν s t₁ v k D B C S (fun i => u i s) F g u w y) ∧
    (∀ (u : ∀ i, ℝ → PlaneHk Set.univ k (h i)) (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
      (y : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k + D - 1) (G i j α)),
      IsKernelWeakSolutionPlane ν t₀ t₁ v k D B C S f F g u w y →
      ∀ t ∈ Set.Icc t₀ t₁,
        massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (u i t).val) +
          ν / 2 * ∫ s in Set.Icc t₀ t₁,
            massGradNormSq (E := h) (K := fun _ => k) ρ π (fun i => (w i s).val)
        ≤ 2 * massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (f i).val)
          + 8 / ν * (∫ s in Set.Icc t₀ t₁,
              massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => k) ρ π
                (fun i => (F i s).val))
          + 10 * (∫ s in Set.Icc t₀ t₁,
              Real.sqrt (massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (g i s).val))) ^ 2) ∧
    ((∀ i s, F i s = 0) → (∀ i s, g i s = 0) →
      ∀ (u : ∀ i, ℝ → PlaneHk Set.univ k (h i)) (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
        (y : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k + D - 1) (G i j α)),
        IsKernelWeakSolutionPlane ν t₀ t₁ v k D B C S f F g u w y →
        (∀ s ∈ Set.Icc t₀ t₁, ∀ t ∈ Set.Icc t₀ t₁, s ≤ t →
          massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (u i t).val) +
            5 * ν / 4 * ∫ τ in Set.Ioc s t,
              massGradNormSq (E := h) (K := fun _ => k) ρ π (fun i => (w i τ).val)
          ≤ massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (u i s).val)) ∧
        (∑ i, ENNReal.ofReal (π i)⁻¹ *
            ⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSq ρ (u i t).val)
          ≤ ENNReal.ofReal
            (massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (f i).val)
              + 2 * ν * θ * ∫ s in Set.Icc t₀ t₁,
                massGradNormSq (E := h) (K := fun _ => k) ρ π (fun i => (w i s).val))) ∧
        (∑ i, ENNReal.ofReal (π i)⁻¹ *
            ((⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSq ρ (u i t).val)) +
              ENNReal.ofReal (ν * ∫ s in Set.Icc t₀ t₁, gradFactorialNormSq ρ (w i s).val))
          ≤ ENNReal.ofReal
            (2 * massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (f i).val)))) :=
by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he =>
    let _ := he
    refine ⟨?_, ?_⟩
    · refine ⟨(fun i => isEmptyElim i), (fun i => isEmptyElim i), (fun i => isEmptyElim i), ?_⟩
      simp [IsKernelWeakSolutionPlane]
    · simp [IsKernelWeakSolutionPlane, massNormSq, massGradNormSq]
  | inr he =>
    let _ := he
    obtain ⟨V0, hv0⟩ := hv_bdd
    let V := max V0 0
    have hV : 0 ≤ V := le_max_right _ _
    have hvV : ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ‖v t x‖ ≤ V :=
      fun t ht x => (hv0 t ht x).trans (le_max_left _ _)
    let P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) t₀ t₁ ρ ν k D := {
      htime := ht, radius_pos := hρ, diffusivity_pos := hν, order_ge_two := hD
      π := π, hπ := hπ, B := B, hB_meas := hB_meas, hB_smooth := hB_smooth
      hB_fin := hB_fin, C := C, S := S, c := c, r := r, hr := hr, hS := hS
      θ := θ, hθ := hθ, hschur := hschur }
    let Q : PlaneKernelDriftData P := {
      v := v, smooth := hv_smooth, measurable := hv_meas, V := V, V_nonneg := hV
      bounded := hvV, divergence_zero := hv_div, strain := a, B := B₀, lam := lam
      strain_nonneg := ha, B_ge_one := hB₀, lam_pos := hlam, scale_small := hB
      strain_small := hab, jets := fun t ht l hl hk x => hjets l hl hk t ht x }
    let T : PlaneKernelFeedbackData Q := { f := f, F := F, hF := hF, g := g, hg := hg }
    refine ⟨T.exists_kernelWeakSolution_of_nonempty, ?_, ?_, ?_, ?_⟩
    · intro u u' w w' y y' hu hu'
      let A : PlaneKernelSolutionData Q := {
        f := f, F := F, hF := hF, g := g, hg := hg, u := u, w := w, y := y, solution := hu }
      let A' : PlaneKernelSolutionData Q := {
        f := f, F := F, hF := hF, g := g, hg := hg, u := u', w := w', y := y', solution := hu' }
      exact A.sameData_unique A' rfl rfl rfl
    · intro u w y hu s hs
      exact P.kernelWeakSolution_restart v f F g u w y hu s hs
    · intro u w y hu t ht
      let A : PlaneKernelSolutionData Q := {
        f := f, F := F, hF := hF, g := g, hg := hg, u := u, w := w, y := y, solution := hu }
      exact A.energy ⟨t, ht⟩
    · intro hF0 hg0 u w y hu
      let A : PlaneKernelSolutionData Q := {
        f := f, F := F, hF := hF, g := g, hg := hg, u := u, w := w, y := y, solution := hu }
      have hf0 : A.F = 0 := funext (fun i => funext (hF0 i))
      have hg0' : A.g = 0 := funext (fun i => funext (hg0 i))
      refine ⟨?_, (A.homogeneous_component_sups hf0 hg0').1,
        (A.homogeneous_component_sups hf0 hg0').2⟩
      intro s hs t ht hst
      exact A.homogeneous_interval hf0 hg0' ⟨s, hs⟩ ⟨t, ht⟩ hst

end AVRegularity.Providers
