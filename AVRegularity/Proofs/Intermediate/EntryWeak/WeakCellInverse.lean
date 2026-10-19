-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeak.IndependentExplicitNaturalCoefficientCalibration
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCellFieldInverse

@[expose] public noncomputable section

open MeasureTheory Homogenization
open AVRegularity.EntryWeakProofs

namespace AVRegularity.Providers

/-- **The two-dimensional cell inverse at small Péclet number** (Lemma 14.2 of the paper). -/
theorem weak_cell_inverse (l sZ : ℕ) (hl : sZ + 2 ≤ l) (hl₃ : 3 ≤ l) (CG Cv ω : ℝ) (_hω₀ : 0 < ω)
    (hω : ω < 3 * Real.pi ^ 2 / 2) :
    ∃ Pe₀ C : ℝ, 0 < Pe₀ ∧ 0 < C ∧
    ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (Pe t₀ t₁ : ℝ),
      t₀ ≤ t₁ → 0 ≤ Pe → Pe ≤ Pe₀ →
      (∀ i j, Measurable fun t' => G t' i j) →
      (∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤ ∑ i, ∑ j, G t i j * k i * k j) →
      (∀ t i j, |G t i j| ≤ CG) →
      Measurable (fun p : ℝ × Vec 2 => v p.1 p.2) →
      (∀ t, ContDiff ℝ ((l + 1 : ℕ) : ℕ∞) (v t)) →
      (∀ t, AVenhance.IsZ2Periodic (v t)) →
      (∀ t (j : ℕ), j ≤ l + 1 → ∀ z, ‖iteratedFDeriv ℝ j (v t) z‖ ≤ Cv) →
      (∀ t z, ∑ i : Fin 2, fderiv ℝ (fun z' => v t z' i) z (Pi.single i 1) = 0) →
    ∀ (c₀ : Vec 2 → ℝ) (g : ℝ → Vec 2 → ℝ) (Ng : ℝ),
      ContDiff ℝ (l : ℕ∞) c₀ → AVenhance.IsZ2Periodic c₀ → (∫ z in AVenhance.unitCube, c₀ z = 0) →
      Measurable (fun p : ℝ × Vec 2 => g p.1 p.2) →
      (∀ t, ContDiff ℝ (l : ℕ∞) (g t)) → (∀ t, AVenhance.IsZ2Periodic (g t)) →
      (∀ t (j : ℕ), j ≤ l → ∀ z, ‖iteratedFDeriv ℝ j (g t) z‖ ≤ Ng) →
      (∀ t, ∫ z in AVenhance.unitCube, g t z = 0) →
      (∃ c : ℝ → Vec 2 → ℝ, IsCellFieldInverse G (fun t z => Pe • v t z) sZ t₀ t₁ c₀ g c) ∧
      (∀ c c' : ℝ → Vec 2 → ℝ,
        IsCellFieldInverse G (fun t z => Pe • v t z) sZ t₀ t₁ c₀ g c →
        IsCellFieldInverse G (fun t z => Pe • v t z) sZ t₀ t₁ c₀ g c' →
        ∀ t ∈ Set.Icc t₀ t₁, c t =ᵐ[volume.restrict AVenhance.unitCube] c' t) ∧
      ∀ c : ℝ → Vec 2 → ℝ,
        IsCellFieldInverse G (fun t z => Pe • v t z) sZ t₀ t₁ c₀ (fun _ _ => 0) c →
        ∀ t ∈ Set.Icc t₀ t₁,
          ∫ z in AVenhance.unitCube, c t z ^ 2 ≤
            C ^ 2 * Real.exp (-(2 * ω * (t - t₀))) * ∫ z in AVenhance.unitCube, c₀ z ^ 2 :=
  by
    refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro G v Pe a b hab hPe hPe1 hGm hGc hGb hvm hvc hvp hvb hvd c₀ g Ng hc₀ hp₀ hm₀ hgm hgc hgp hgb hg₀
    let P : MolecularData := ⟨G, (fun t z => Pe • v t z), CG, 2 * Pe * Cv,
      hGm, hGb, hGc, hvm.const_smul Pe, scaled_drift_square_bound l v Cv Pe hvb⟩
    have hvD := scaled_drift_isCellDrift l v Cv Pe hvm hvc hvp hvb hvd
    have hvC : ∀ t, ContDiff ℝ (l : ℕ∞) (P.v t) :=
      fun t => ((hvc t).of_le (by simp)).const_smul Pe
    have hvP : ∀ t, AVenhance.IsZ2Periodic (P.v t) := by
      intro t n z
      exact congrArg (fun w : Vec 2 => Pe • w) (hvp t n z)
    have hCv : 0 ≤ |Pe| * Cv :=
      mul_nonneg (abs_nonneg Pe) (drift_budget_nonneg l v Cv hvb)
    have hg := complexFiniteJet_memLp l a b g hgc hgm Ng hgb
      (AVRegularity.Sobolev.valueIndex2 l)
    refine ⟨dataRegular_scalar_inverse hab P hvD l sZ hl hl₃ (|Pe| * Cv) hCv
      hvC hvP (scaled_drift_component_bound l v Cv Pe hvc hvb)
      c₀ g Ng hc₀ hp₀ hm₀ hgm hgc hgp hgb hg₀, ?_, ?_⟩
    · exact dataScalarInverse_unique hab P sZ c₀ g hg
    · intro c hc t ht
      simpa only [one_pow, one_mul] using
        dataScalarInverse_decay hab P hvD sZ ω hω c₀ c hc t ht

end AVRegularity.Providers
