-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Matrix.Basic

/-! The covariance `H_cov(t) = ∫_{t₀}^t (𝖩(s) - B I) ds` of an abstract spatially constant symmetric
time-dependent matrix `𝖩`. The reference-flux instance is `ocCovariance`; here `𝖩` is the abstract
diagonal flux of the coarse family. -/

@[expose] public noncomputable section

open MeasureTheory

namespace AVRegularity

/-- `H_cov(t)_{ij} = ∫_{t₀}^t (𝖩(s)_{ij} - B δ_{ij}) ds`. -/
def covarianceMatrix (J : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B t₀ t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => ∫ s in t₀..t, (J s i j - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)

end AVRegularity
