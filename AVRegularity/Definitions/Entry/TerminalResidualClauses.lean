-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.CycleWords.CoreScalarPackage
public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVRegularity.Definitions.Construction.ResidualOps

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity

/-! The scales of the terminal passage `M → M-1`.

`ν = κ_M` (the molecular diffusivity, `κ ∈ 𝒦_M`), `B = κ_{M-1}`, `x = ε_M`, `E = ε_{M-1}`,
`Y = ε_{M-2}`, `h = τ_M''`, `ℓ² = x²/ν`, `d_* = x√(B/ν)`, `ρ = c_r√(Bh)`, `Pe_M = x^β/ν`
(`β = 1+α`), `ζ = qγ + 3δ`; the kernel radii `r_w = x^{1+σ_w}` (weak paired kernel),
`r_new = ρE^{t_T}` (fresh terminal kernels) and the capped molecular radius `r_* = c_K x`. -/

section
namespace OCData

variable (D : OCData)

/-- `ν = κ_M`. -/
def termNu (M : ℕ) : ℝ := D.κ M

/-- `B = κ_{M-1}`. -/
def termB (M : ℕ) : ℝ := D.κ (M - 1)

/-- `h = τ_M''`. -/
def termH (M : ℕ) : ℝ := ocTauPP D.α D.q D.Λ M

/-- `ℓ² = x²/ν`. -/
def termEllSq (M : ℕ) : ℝ := D.eps M ^ 2 / D.termNu M

/-- `d_* = x√(B/ν)`. -/
def termDstar (M : ℕ) : ℝ := D.eps M * Real.sqrt (D.termB M / D.termNu M)

/-- `ρ = c_r√(Bh)`. -/
def termRho (cr : ℝ) (M : ℕ) : ℝ := cr * Real.sqrt (D.termB M * D.termH M)

/-- `Pe_M = x^β/ν`, `β = 1+α`. -/
def termPe (M : ℕ) : ℝ := D.eps M ^ (1 + D.α) / D.termNu M

/-- `ζ = qγ + 3δ`. -/
def termZeta : ℝ := D.q * ocGamma D.α D.q + 3 * ocDelta D.α D.q

/-- The weak paired-kernel radius `r_w = x^{1+σ_w}`. -/
def termRW (σw : ℝ) (M : ℕ) : ℝ := D.eps M ^ (1 + σw)

/-- The fresh terminal radius `r_new = ρE^{t_T}`. -/
def termRNew (cr tT : ℝ) (M : ℕ) : ℝ := D.termRho cr M * D.eps (M - 1) ^ tT

/-- The capped molecular radius `r_* = c_K x`. -/
def termRStar (cK : ℝ) (M : ℕ) : ℝ := cK * D.eps M

/-- The cell ratio `ε_T = d_*/ρ`. -/
def termEpsCell (cr : ℝ) (M : ℕ) : ℝ := D.termDstar M / D.termRho cr M

end OCData
end

/-! The isotropic paired kernel
`S_{r/√2,I} S_{r/√2,I}`.
The `KernelSpec` stores the **source radius** `r`
with both reference matrices `I/√2`: its two displacements are `(r/√2)z`, so it is exactly the
source operator, and every identity carrying it records the width `r` (`rb = r`), as the cascade
convention `kernel width = record width` requires. The spanning inverse has the fixed
norm `√2`, absorbed in the admissibility bound. It is the weak kernel `S_w` at `r = r_w` and the fresh
terminal kernel `S_α` at `r = r_new`; all kernels use the cascade's mass-one template `φ₀`,
with orders `n` (moments of orders `1, …, 2n-1` vanish) chosen before the families. -/

/-- The isotropic paired kernel of radius `r` and order `n`. -/
def isoPairedKernel (r : ℝ) (n : ℕ+) : KernelSpec where
  width := r
  order := n
  H₁ := fun _ => (Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)
  H₂ := fun _ => (Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The **finite-order scalar package** `ScalarPackageUpTo J_req`: the fields of
`FibreScalarData`, `CoreScalarPackage` and `ScalarPackage`, with every
order-indexed clause (graph, row, decay and smoothing jets, the high-band smoothing, the replacement
graphs/rows, the Taylor rows and the phase jets) restricted to orders `≤ J_req`. The terminal
proof asserts this record for each finite requested order, with its threshold after that order;
the all-order record is not supplied by the terminal argument.
Decay entrances are periodic at every order; fast/adjoint decay and smoothing
outputs are periodic, so they can serve as later entrances. -/

structure FibreScalarDataUpTo (Jreq : ℕ) (K : ScalarConstants) (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (t₀ S : ℝ) where
  /-- Taylor coefficients of the graph `r(ξ) = ∑ ξ^α r_α`. -/
  r : ℕ × ℕ → ℝ → RawJet2 1 ℂ
  /-- Taylor coefficients of the symbol `λ(ξ) = ∑ ξ^α λ_α`. -/
  lam : ℕ × ℕ → ℝ → ℂ
  /-- Taylor coefficients of the row `ℓ(ξ) = ∑ ξ^α ℓ_α`. -/
  ell : ℕ × ℕ → ℝ → Vec 2 → ℂ
  graph : IsFibreGraph η G v K.ξ0 K.Cg r lam
  row_summable : ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < K.ξ0 →
    ∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ * ⨆ s, cellL2Norm (ell p s) < ⊤
  row_mean : ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < K.ξ0 → ∀ s : ℝ,
    Integrable (fun x => fibreSeriesFun ell ξ s x * (1 + cellValue (fibreSeriesJet r ξ) s x))
        (volume.restrict AVenhance.unitCube) ∧
      (∫ x in AVenhance.unitCube,
        fibreSeriesFun ell ξ s x * (1 + cellValue (fibreSeriesJet r ξ) s x)) = 1 ∧
      cellL2Norm (fun x => fibreSeriesFun ell ξ s x - 1) ≤ ENNReal.ofReal (K.Cg * fibreNorm ξ)
  row_taylor : ∀ (n : ℕ) (ξ : Fin 2 → ℂ) (s : ℝ), n ≤ Jreq →
    cellL2Norm (fibreHomogeneous ell ξ n s) ≤
      ENNReal.ofReal (K.Cg * (2 / K.ξ0) ^ n * fibreNorm ξ ^ n)
  real_ratio : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 → ∀ s t : ℝ, s ≤ t →
    ENNReal.ofReal ‖Complex.exp (∫ τ in s..t, fibreSeriesC lam ξ τ)‖ *
        cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) t x) ≤
      cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) s x) ∧
    cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) s x) ≤
      ENNReal.ofReal K.Cg * cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) t x)
  graph_jets : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), j ≤ Jreq → (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 → ∀ t : ℝ,
    ContDiff ℝ j (cellValue (fibreSeriesJet r ξ) t) ∧
      cellSobolevNorm j (cellValue (fibreSeriesJet r ξ) t) ≤
        ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ)
  row_jets : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), j ≤ Jreq → (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 → ∀ t : ℝ,
    ContDiff ℝ j (fun x => fibreSeriesFun ell ξ t x - 1) ∧
      cellSobolevNorm j (fun x => fibreSeriesFun ell ξ t x - 1) ≤
        ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ)
  fast_decay : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), j ≤ Jreq → (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 →
    ∀ s t : ℝ, t₀ ≤ s → s ≤ t → t ≤ t₀ + S → ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc s t) (fibreCoefficients η G v ξ (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) D →
      ∀ g₀ : Vec 2 → ℂ, ContDiff ℝ j g₀ → AVenhance.IsZ2Periodic g₀ → cellValue D s =ᵐ[volume.restrict AVenhance.unitCube] g₀ →
      ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
        fibreFastPart r lam ell ξ D s t =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
        cellSobolevNorm j g₁ ≤
          ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * Real.exp (-(K.cj j) * (t - s))) *
            cellSobolevNorm j g₀
  fast_smoothing : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), j ≤ Jreq → (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 →
    ∀ s t : ℝ, t₀ ≤ s → s < t → t ≤ t₀ + S → ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc s t) (fibreCoefficients η G v ξ (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) D →
      ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
        fibreFastPart r lam ell ξ D s t =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
        cellSobolevNorm j g₁ ≤
          ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j *
              (1 + (t - s) ^ (-(j : ℝ) / 2)) * Real.exp (-(K.cj j) * (t - s))) *
            cellL2Norm (cellValue D s)
  adjoint_decay : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), j ≤ Jreq → (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 →
    ∀ s t : ℝ, t₀ ≤ s → s ≤ t → t ≤ t₀ + S → ∀ Ψ : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc (-t) (-s))
        (fibreCoefficients η (fun τ => G (-τ)) (fun τ z => -(v (-τ) z)) (fun k => -(ξ k))
          (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) Ψ →
      ∀ g₀ : Vec 2 → ℂ, ContDiff ℝ j g₀ → AVenhance.IsZ2Periodic g₀ →
        cellValue Ψ (-t) =ᵐ[volume.restrict AVenhance.unitCube] g₀ →
      ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
        fibreAdjointFastPart r lam ell ξ Ψ s t =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
        cellSobolevNorm j g₁ ≤
          ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * Real.exp (-(K.cj j) * (t - s))) *
            cellSobolevNorm j g₀
  adjoint_smoothing : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), j ≤ Jreq → (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 →
    ∀ s t : ℝ, t₀ ≤ s → s < t → t ≤ t₀ + S → ∀ Ψ : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc (-t) (-s))
        (fibreCoefficients η (fun τ => G (-τ)) (fun τ z => -(v (-τ) z)) (fun k => -(ξ k))
          (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) Ψ →
      ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
        fibreAdjointFastPart r lam ell ξ Ψ s t =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
        cellSobolevNorm j g₁ ≤
          ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j *
              (1 + (t - s) ^ (-(j : ℝ) / 2)) * Real.exp (-(K.cj j) * (t - s))) *
            cellL2Norm (cellValue Ψ (-t))


structure CoreScalarPackageUpTo (Jreq : ℕ) (K : ScalarConstants) (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (t₀ S ϖ : ℝ)
    (reg : BlockRegions) where
  consts_pos : 0 < K.ξ0 ∧ 0 < K.ξlo ∧ 2 * K.ξlo < K.ξ0 ∧ 0 < K.Cg ∧ 0 < K.cGauss ∧
    0 < K.θs ∧ 0 < K.cadm ∧ (∀ j, 0 < K.Cj j ∧ 0 < K.cj j) ∧ (∀ m, 0 < K.Cwt m) ∧
    (2 + K.Cw * K.Cg) * (2 * K.ξlo) ^ 2 ≤ Real.pi ^ 2 / 16
  /-- Graph, row, decay and smoothing for the actual drift. -/
  actual : FibreScalarDataUpTo Jreq K η G v t₀ S
  contraction : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → ∀ s t : ℝ, t₀ ≤ s → s ≤ t →
    t ≤ t₀ + S → ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc s t) (fibreCoefficients η G v ξ (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) D →
      cellL2Norm (cellValue D t) ≤ cellL2Norm (cellValue D s)
  high_smoothing : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), j ≤ Jreq →
    (∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt η) →
    ∀ s t : ℝ, t₀ ≤ s → s < t → t ≤ t₀ + S →
      (∀ D : ℝ → RawJet2 1 ℂ,
        IsCellSolution (Set.Icc s t) (fibreCoefficients η G v ξ (fun _ => 0))
          (fun _ _ => 0) (fun _ _ => 0) D →
        ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧
          cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
          cellSobolevNorm j g₁ ≤
            ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * (1 + (t - s)) ^ K.Qj j *
              (1 + (t - s) ^ (-(j : ℝ) / 2))) * cellL2Norm (cellValue D s)) ∧
      (∀ Ψ : ℝ → RawJet2 1 ℂ,
        IsCellSolution (Set.Icc (-t) (-s))
          (fibreCoefficients η (fun τ => G (-τ)) (fun τ z => -(v (-τ) z)) (fun k => -(ξ k))
            (fun _ => 0))
          (fun _ _ => 0) (fun _ _ => 0) Ψ →
        ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧
          cellValue Ψ (-s) =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
          cellSobolevNorm j g₁ ≤
            ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * (1 + (t - s)) ^ K.Qj j *
              (1 + (t - s) ^ (-(j : ℝ) / 2))) * cellL2Norm (cellValue Ψ (-t)))
  quiet_zero : ∀ t ∈ reg.quiet ∩ Set.Icc t₀ (t₀ + S), ∀ z, v t z = 0
  quiet_mean : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → ∀ a b : ℝ, a ≤ b →
    Set.Icc a b ⊆ reg.quiet → Set.Icc a b ⊆ Set.Icc t₀ (t₀ + S) → ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc a b) (fibreCoefficients η G v ξ (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) D →
      cellMean (cellValue D b) =
        Complex.exp (-(η : ℂ) * ∫ τ in a..b, fibreQuad (G τ) ξ) * cellMean (cellValue D a)
  quiet_gap : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt η) →
    ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ reg.quiet → Set.Icc a b ⊆ Set.Icc t₀ (t₀ + S) →
      ∀ D : ℝ → RawJet2 1 ℂ,
        IsCellSolution (Set.Icc a b) (fibreCoefficients η G v ξ (fun _ => 0))
          (fun _ _ => 0) (fun _ _ => 0) D →
        cellL2Norm (cellQ0 (cellValue D b)) ≤
          ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2) * (b - a))) *
            cellL2Norm (cellQ0 (cellValue D a))
  cover : ∀ t ∈ Set.Icc t₀ (t₀ + S), t ∈ reg.quiet ∨ ∃ p, t ∈ Set.Icc (reg.lo p) (reg.hi p)
  buffer_nonneg : 0 ≤ reg.buffer
  buffer_le : reg.buffer ≤ S
  joins_ge : 2 * reg.P ≤ reg.joins
  buffer_inside : ∀ p, Set.Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer) ⊆
    Set.Icc t₀ (t₀ + S)
  buffer_quiet : ∀ p, Set.Ico (reg.lo p - reg.buffer) (reg.lo p) ⊆ reg.quiet ∧
    Set.Ioc (reg.hi p) (reg.hi p + reg.buffer) ⊆ reg.quiet
  /-- The single-orientation extension of the drift on the `p`th region. -/
  ext : Fin reg.P → ℝ → Vec 2 → Vec 2
  ext_local : ∀ p, FibreScalarDataUpTo Jreq K η G (ext p) t₀ S
  ext_shear : ∀ p, ∃ V : ℝ → ℝ → ℝ,
    ∀ t z, ext p t z = V t (z (reg.orient p).rev) • basisVec (reg.orient p)
  ext_drift : ∀ p, IsCellDrift (ext p) ∧ (∀ t (k : Fin 2), cellMean (fun x => (ext p t x k : ℂ)) = 0) ∧
    ∀ t x, Real.sqrt η * Real.sqrt (∑ i, ext p t x i ^ 2) ≤ K.Cw
  ext_agree : ∀ p, ∀ t ∈ Set.Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer), ∀ z,
    ext p t z = v t z
  replace_graph : ∀ (j : ℕ) (p : Fin reg.P) (ξ : Fin 2 → ℂ), j ≤ Jreq → (∀ i, (ξ i).im = 0) →
    fibreNorm ξ < K.ξ0 → ∀ t ∈ Set.Icc (reg.lo p) (reg.hi p + reg.buffer),
      cellSobolevNorm j (fun x => cellValue (fibreSeriesJet actual.r ξ) t x -
          cellValue (fibreSeriesJet (ext_local p).r ξ) t x) ≤
        ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ *
          Real.exp (-(K.cj j) * reg.buffer))
  replace_row : ∀ (j : ℕ) (p : Fin reg.P) (ξ : Fin 2 → ℂ), j ≤ Jreq → (∀ i, (ξ i).im = 0) →
    fibreNorm ξ < K.ξ0 → ∀ s ∈ Set.Icc (reg.lo p - reg.buffer) (reg.hi p),
      cellSobolevNorm j (fun x => fibreSeriesFun actual.ell ξ s x -
          fibreSeriesFun (ext_local p).ell ξ s x) ≤
        ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ *
          Real.exp (-(K.cj j) * reg.buffer))
  replace_symbol : ∀ (p : Fin reg.P) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) →
    fibreNorm ξ < K.ξ0 → ∀ t ∈ Set.Icc (reg.lo p) (reg.hi p + reg.buffer),
      ‖fibreSeriesC actual.lam ξ t - fibreSeriesC (ext_local p).lam ξ t‖ ≤
        K.Cj 0 * peFactor η ^ K.Qj 0 * fibreNorm ξ ^ 2 * Real.exp (-(K.cj 0) * reg.buffer)
  /-- The chart, weight and duration bounds, for every requested moment reserve `M ≤ J_req`. -/
  weights : ∀ M : ℕ, M ≤ Jreq → ChartWeights (fun t _ => G t) v t₀ S ϖ 0 M K.Cwt
  neg_adjoint : ∀ (k p : ℕ) (s t : ℝ), k ≤ Jreq → p ≤ Jreq → t₀ ≤ s → s ≤ t → t ≤ t₀ + S →
    ∀ (f : ∀ _ : Unit, PlaneHk Set.univ k ℝ)
      (u : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ k ℝ)
      (w : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (k + 1) ℝ),
      IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => k) (-t) (-s)
        (fun τ z => -(v (-τ) z)) f (fun _ _ _ => 0) u w →
      weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
          (fun x a w' => planeJetOrder (u 0 x (-s)) a w') ≤
        ENNReal.ofReal (K.Cneg k p * peFactor η ^ K.Qneg k * (1 + (t - s)) ^ K.Qneg k) *
          weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
            (fun x a w' => planeJetOrder (f x) a w')


structure ScalarPackageUpTo (Jreq : ℕ) (K : ScalarConstants) (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t₀ S ϖ : ℝ) (reg : BlockRegions)
    extends CoreScalarPackageUpTo Jreq K η G v t₀ S ϖ reg where
  gauss : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → fibreNorm ξ ≤ 2 * K.ξlo →
    (∫ τ in t₀..(t₀ + S), fibreSeriesC actual.lam ξ τ).re ≤ -K.cGauss * S * fibreNorm ξ ^ 2 ∧
    ∀ N : ℕ, 2 ≤ N → N ≤ Jreq →
      (∫ τ in t₀..(t₀ + S), ∑ n ∈ Finset.range (N + 1), fibreHomogeneous actual.lam ξ n τ).re ≤
        -K.cGauss * S * fibreNorm ξ ^ 2
  phase_jets : ∀ (n : ℕ) (j : Fin n → Fin 2) (ξ : Fin 2 → ℂ), 1 ≤ n → n ≤ Jreq → fibreNorm ξ < K.ξ0 →
    ∀ s t : ℝ, t₀ ≤ s → s ≤ t → t ≤ t₀ + S →
      ‖iteratedFDeriv ℂ n (fun ξ' : Fin 2 → ℂ => ∫ τ in s..t, fibreSeriesC actual.lam ξ' τ) ξ
          (fun i => Pi.single (j i) (1 : ℂ))‖ ≤
        K.Cj n * Real.sqrt S ^ n * (if n = 1 then Real.sqrt S * fibreNorm ξ else 1)
  marks_in : ∀ j, ∀ m ∈ reg.marks j, t₀ ≤ m ∧ m + K.θs ≤ t₀ + S
  marks_sep : ∀ j, ∀ m ∈ reg.marks j, ∀ m' ∈ reg.marks j, m ≠ m' →
    m + K.θs ≤ m' ∨ m' + K.θs ≤ m
  marks_count : ∀ j, K.cadm * S / K.θs ≤ ((reg.marks j).card : ℝ)
  high_marks : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt η) →
    K.ξlo ≤ fibreNorm ξ → ∃ j : Fin 2, ∀ m ∈ reg.marks j, ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc m (m + K.θs)) (fibreCoefficients η G v ξ (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) D →
      cellL2Norm (cellValue D (m + K.θs)) ≤ ENNReal.ofReal (1 / 2) * cellL2Norm (cellValue D m)

end AVRegularity
end

section
namespace AVRegularity

/-! The sufficient schedule of the terminal orders.

With `δ, γ, c` of the construction, `ζ = qγ + 3δ`, `D_read = q^{J_w+1}(1+s)`, the excess
`s_T = max_{l ∈ A} letterOrder(l) - 2` of the fresh letters, `η_b = η₀/2` and
`b_T = δ - η₀ - η_b/2 - t_Ts_T`:
* `k₀ ≥ L_w + 5` (the weak readout bound reads its input in `L²` at the order `L_w + 5`, two
  orders above the sup-norm order `L_w + 3` of the lift estimate);
  `Q_T/2 > P_T + D_read + 2`;
* `ζA_T > 3`, `ζN_T > Q_T + 2`, `δ(R_T+1)/2 > Q_T + 2`, `δp_T > Q_T + 2`;
* `0 < η₀ ≤ δ/8`; `0 < t_T < δ/(8(s_T+1))`;
* moment orders: `b_T + t_TL_c > Q_T + 2`, `qχ_w + (ζ + qσ_w)L_o > Q_T + 2`,
  `q(χ_w + σ_wL_f) > Q_T + 2`, `q(χ_w + σ_wL) > 2Q_T + 4` (ordered preparation telescope);
* kernel orders before solving: the weak kernel `S_w` (order `n_w`) has moments through
  `max{L, L_o, L_f}` and the cascade's `max{L_pr, L_c, L_f}`; the fresh kernels (order `n_T`)
  through `L_c` and the cascade's `max{L_pr, L_c, L_f}` (`2n - 1 ≥ L`).
The order names `L_pr` (the ordered preparation telescope; here `L`) and `L_c`, `L_o`, `L_f` are
read as terminal orders, distinct from the preservation orders. The internal geometry orders of
the capped preparation (`K_g, J_g`) belong to its proof. -/

/-- The actual terminal alphabet (display (14.2) of the paper): the first source `𝖣`,
the new higher interaction means `𝖬_{n,h}` of degree `3 ≤ n ≤ N_T + D` along paths of
`1 ≤ h ≤ d_w` edges, and the covariance dressings `𝖵_{n,h,a,a'}` with `2 ≤ n ≤ N_T + D`,
`a, a' ≤ p_T`, `a + a' ≥ 1`; no padding letters. `D` is the largest incoming tested order `D_w`
and `d_w` the depth of the weak graph. -/
def termAlphabet (NT pT DW dW : ℕ) : Finset WordLetter := succAlphabet (NT + DW) dW pT 0

/-- The largest excess order of the fresh letters. -/
def termExcess (NT pT : ℕ) (A : Finset WordLetter) : ℕ := A.sup (letterOrder NT pT) - 2

/-- The terminal schedule. -/
def IsTerminalSchedule (α q s PT QT σw χw η₀ tT : ℝ) (Jw Lw k₀ NT pT RT AT LcT LoT LfT LpT : ℕ)
    (A : Finset WordLetter) : Prop :=
  let δ := ocDelta α q
  let ζ := q * ocGamma α q + 3 * δ
  let sT := termExcess NT pT A
  let bT := δ - η₀ - η₀ / 4 - tT * sT
  Lw + 5 ≤ k₀ ∧ QT / 2 > PT + q ^ (Jw + 1) * (1 + s) + 2 ∧
    ζ * AT > 3 ∧ ζ * NT > QT + 2 ∧ δ * (RT + 1) / 2 > QT + 2 ∧ δ * pT > QT + 2 ∧
    0 < η₀ ∧ η₀ ≤ δ / 8 ∧ 0 < tT ∧ tT < δ / (8 * (sT + 1)) ∧
    bT + tT * LcT > QT + 2 ∧ q * χw + (ζ + q * σw) * LoT > QT + 2 ∧
    q * (χw + σw * LfT) > QT + 2 ∧ q * (χw + σw * LpT) > 2 * QT + 4

/-- The fresh terminal kernel order, a finite request after the preservation menus and before the
threshold (moments through `L_c^T` and the cascade's `max{L_pr, L_c, L_f}`). -/
def IsFreshKernelOrder (nT : ℕ+) (LcT Lpr Lc Lf : ℕ) : Prop :=
  LcT + 1 ≤ 2 * (nT : ℕ) ∧ max Lpr (max Lc Lf) + 1 ≤ 2 * (nT : ℕ)

/-- The weak kernel order, chosen before the weak families are solved. -/
def IsTerminalKernelOrders (nW : ℕ+) (LoT LfT LpT Lpr Lc Lf : ℕ) : Prop :=
  max LpT (max LoT LfT) + 1 ≤ 2 * (nW : ℕ) ∧ max Lpr (max Lc Lf) + 1 ≤ 2 * (nW : ℕ)

/-- The a priori seed order bound `D̄₀ = max{2, D_w, max_{α ∈ A_T} d_max(α)}`:
direct copies keep order `≤ D_w`, quadratic conversions have order two,
fresh letters have the orders of `letterOrder`, and Piola transfer only lowers orders. It depends
only on the weak and terminal physical menus, not on the later preservation menus or reserves. -/
def termD0bar (NT pT DW dW : ℕ) : ℕ :=
  max 2 (max DW ((termAlphabet NT pT DW dW).sup (letterOrder NT pT)))

/-- The a priori seed depth bound `r̄₀ = max{2, (R_T+2)(d_w+1) - 1}`: at most `R_T+1`
fresh edges separate at most `R_T+2` old runs of depth `≤ d_w`. -/
def termR0bar (RT dW : ℕ) : ℕ := max 2 ((RT + 2) * (dW + 1) - 1)

/-- The seed exponents chosen after the terminal menus and before the preservation menus:
`0 < τ_e < min{qχ_w, b_T}` with `b_T = δ - η₀ - η_b/2 - t_Ts_T`, `η_b = η₀/2`, and the
coarse width exponent `3δ < λ_entry < min{λ_w, λ_new}`,
`λ_w = q²(1+σ_w) - 1 - c`, `λ_new = q(1+c+t_T) - 1 - c`; the fine width exponent is `σ_entry = δ`. -/
def IsEntrySeedExponents (α q σw χw η₀ tT τe lamE : ℝ) (NT pT DW dW : ℕ) : Prop :=
  let δ := ocDelta α q
  let c := ocC α q
  let bT := δ - η₀ - η₀ / 4 - tT * (termExcess NT pT (termAlphabet NT pT DW dW) : ℝ)
  0 < τe ∧ τe < q * χw ∧ τe < bT ∧
    3 * δ < lamE ∧ lamE < q ^ 2 * (1 + σw) - 1 - c ∧ lamE < q * (1 + c + tT) - 1 - c

/-! The whole-window bill `𝔅_T` of the terminal passage:

`𝔅_T = ε_T^{N_T}(1 + Z_cl) + [√(B/ν) + ε_T²(1 + Z_cl)]·[E^{δ(R_T+1)/2} + E^{δp_T}
       + E^{b_T + t_TL_c} + x^{χ_w}(r_w/ρ)^{L_o}] + x^{χ_w + σ_wL_f}
       + C_gE^{-C_g} ℓ √(B_p/d_gap) exp(-c d_gap/ℓ²)`,

with `ε_T = d_*/ρ`, `I = [t_p, a+T₀]`, `Z_cl = √|I| ℓ^{-1}(x/ρ)^{A_T}`, `B_p = 1 + |I|/τ_M`,
`d_gap = c τ_M`; the terms are the centered cell reconstruction, the response frontier at `R_T+1`,
the covariance truncation, the fresh and old coarse filter tails, the complete fine filter tail,
and gluing with all histories. Only `B_p ≤ C(1+|I|/τ_M)` and `d_gap ≥ cτ_M` are used; the bill
takes these values. -/

/-- The terminal bill. -/
def termBill (D : OCData) (M NT pT RT AT LcT LoT LfT : ℕ) (A : Finset WordLetter)
    (cr σw χw η₀ tT cgap Cg tp tf : ℝ) : ℝ :=
  let δ := ocDelta D.α D.q
  let E := D.eps (M - 1)
  let x := D.eps M
  let ρ := D.termRho cr M
  let εT := D.termEpsCell cr M
  let ℓ := Real.sqrt (D.termEllSq M)
  let Zcl := Real.sqrt (tf - tp) / ℓ * (x / ρ) ^ AT
  let Bp := 1 + (tf - tp) / ocTau D.α D.q D.Λ M
  let dgap := cgap * ocTau D.α D.q D.Λ M
  let bT := δ - η₀ - η₀ / 4 - tT * (termExcess NT pT A : ℝ)
  εT ^ NT * (1 + Zcl) +
    (Real.sqrt (D.termB M / D.termNu M) + εT ^ 2 * (1 + Zcl)) *
      (E ^ (δ * (RT + 1) / 2) + E ^ (δ * pT) + E ^ (bT + tT * LcT) +
        x ^ χw * (D.termRW σw M / ρ) ^ LoT) +
    x ^ (χw + σw * LfT) +
    Cg * E ^ (-Cg) * ℓ * Real.sqrt (Bp / dgap) * Real.exp (-(dgap / ℓ ^ 2))

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! The **output package of the weak reduction** consumed by terminal entry.

The weak construction itself (the weak passages with the two-dimensional small-Péclet inverse) is
defined separately.
The output is recorded as a predicate on explicit objects, all at hr = `ScalarH` (every
component of entry is a real scalar field). The package carries the
certificates the seed needs, not only numerical envelopes:
* `IsWeakStage`: the datum-independent start `a ≤ a_M ≤ a + 6J_wτ''_{M+1}`, the re-rooted stage at level `M` (every component a root,
  every identity a seed identity whose tag stores its weak birth tuple), finite depth `d_w` and
  order `D_w`, record widths `r_w` equal to the stored widths of `S_w`, original lengths
  `≤ C_L ε_{M+1}`, masses `∑π ≤ 2/3`, `∑ω²π ≤ 2/3`, and the stage invariant at the weak constants
  `kW` (context certificates at the allocated reserves, record-majorant envelopes, ledger and price,
  kernels, quiet atlas, transversality, fast independence) at the capped radius `c_Kx`;
* `IsWeakPaired`: the raw family `U` (identity kernel, mass-one template) and the paired family
  `V` from the same trace, at the reserve `K_w`, with the energies of `U`
  and `V` and the paired difference `x^{χ_w + σ_wL}`;
* `IsWeakReadout`: the finest scalar solution `θ` (`ℒ_{M+J_w}θ = 0`, `θ(a) = f`), the weak lift
  `𝒲_w` (linear at each time on fields of class `C^{L_w+3}`) with the sharp readout
  bound
  `‖𝒲_w z‖_{C^s} ≤ Cε_{M+J_w}^{-1-s}|z|_{c_Kx,L_w+3;π}` (it is `CE^{-D_read}`,
  `D_read = q^{J_w+1}(1+s)`), on classical representatives
  of order `L_w + 3` (which exist when `K_w ≥ L_w + 5`), and the identity `θ = 𝒲_wV + e_w`,
  `sup_{[a+τ,a+T₀]}‖e_w‖_{C^s} ≤ Cx^{P_w}‖f‖₂`.
The conditional statement `entry_terminal_of_weak` takes this package as its hypothesis; the
terminal entry is its composition with the weak construction. -/

section
/-- Every component of entry is a real scalar field. -/
abbrev ScalarH : ℕ → Type := fun _ => ℝ

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The registry of `G` is certified at or above the level `n`: every export is
scheduled, every denotation of it is slotwise parallel invariant on `J_𝗉`, its
denotation is unique on `J_𝗉` and the admissible chains, and its root lies at or
above `n`. This is the export clause of `IsGeneratedSeed` for an arbitrary stage. -/
def GenStage.HasCertifiedExports (G : GenStage D ScalarH Dm b j₀) (n : ℕ) : Prop :=
  (∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), G.exports e →
      Gen.IsScheduled D e ∧ (∀ f : GenSort.Sem .ctx, Gen.Denotes D b j₀ e f →
        IsSlotParInvCtx D b j₀ i p f) ∧
      ∀ f f' : GenSort.Sem .ctx, Gen.Denotes D b j₀ e f → Gen.Denotes D b j₀ e f' →
        ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ ch : RealChain, IsAdmissibleChain D b j₀ i p ch →
          ∀ ζ : Vec 2, f t ch ζ = f' t ch ζ) ∧
    SeedExports.Above (fun {_ _} e => G.exports e) n

/-- The weak stage at level `M`, re-rooted, with its datum-independent start `a_M`, its masses,
its finite depth and order, its tags (record widths `r_w` equal to the stored widths of `S_w`,
original lengths `≤ C_L ε_{M+1}`, identity maps of norm `≤ 1`), and the **stage invariant at the weak constants `kW`** on
`[a_M, a+T₀]`: generated membership with quantitative context certificates at the graded producer
reserves, both envelopes (ordinary and marked) with the record majorant on the reserved inner
domains, the marked ledger and kernel price `≤ C_χ x^{χ_w}`, the kernels `S_w` (admissible, stored
width = record width), the quiet atlas, transversality and fast independence.
The pieces are natural at the finest history level
`M_nat = M + J_w`. The molecular radius of the invariant is
`rhoStar D c_K M = c_K min{x, √(κ_M/a_M)}`, which is the capped radius `c_Kx` once `Pe_M ≤ 1`. -/
def IsWeakStage (law : BirthLaw) (P : ProvParams) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (M Mnat Jw dW DW : ℕ) (nW : ℕ+) (kW : InvConsts) (a T₀ σw CL Cχ χw : ℝ)
    (Gw : GenStage D ScalarH Dm b j₀) (aM : ℝ) : Prop :=
  a ≤ aM ∧ aM ≤ a + 6 * Jw * ocTauPP D.α D.q D.Λ (M + 1) ∧
    Gw.level = M ∧ Gw.fam.HasDepthAtMost dW ∧ (∀ v : CompIn Gw.comps, v.1.births = []) ∧
    ((∀ v u (γ : Gw.fam.Γ v u), ∃ k tag, Gw.prov v u γ = .seed k tag) ∧
      Gw.HasCertifiedExports M ∧ IsSeedPointwiseMolecular law kW Gw aM (a + T₀)) ∧
    (∀ v u (γ : Gw.fam.Γ v u), (Gw.fam.identity v u γ).maxOrder ≤ DW ∧
      (Gw.fam.identity v u γ).record.width = D.termRW σw M ∧
      (Gw.fam.identity v u γ).record.length ≤ CL * D.eps (M + 1) ∧
      ‖(Gw.fam.identity v u γ).map‖ ≤ 1) ∧
    ∑ v, Gw.mass law v ≤ 2 / 3 ∧ ∑ v, Gw.readoutWeight law v ^ 2 * Gw.mass law v ≤ 2 / 3 ∧
    IsStageInvariant law P (fun _ => isoPairedKernel (D.termRW σw M) nW)
      (fun _ => isoPairedKernel (D.termRW σw M) nW) φ₀ hφ₀ Mnat kW aM (a + T₀)
      (Cχ * D.eps M ^ χw) (Cχ * D.eps M ^ χw) Gw

/-- The raw family `U` (identity kernel: width `0`, which is the identity operator for the
mass-one template) and the paired family `V` (`S_w` at `r_w`), both from the complete
trace `U₀` at `a_M`, at the reserve `K_w`, with the energy bounds
`𝓔^κ_{c_Kx,K_w}(U) + 𝓔^κ_{c_Kx,K_w}(V) ≤ C_K‖f‖₂` and the paired difference
`𝓔^κ_{c_Kx,K_w}(U - V) ≤ C_K x^{χ_w + σ_wL}‖f‖₂` (Lemma 14.8 of the paper gives the first bound,
and its bound on `U_M - Ũ_M` gives the second). -/
def IsWeakPaired (P : ProvParams) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (law : BirthLaw)
    (M Kw L : ℕ) (nW : ℕ+) (a T₀ σw χw cK CK : ℝ) (f : Vec 2 → ℝ)
    (Gw : GenStage D ScalarH Dm b j₀) (aM : ℝ)
    (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
    (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
    (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
    (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root)) : Prop :=
  ∫ z, φ₀ z = 1 ∧
    Gw.IsRegSolution P (fun _ => isoPairedKernel 0 nW) (fun _ => isoPairedKernel 0 nW) φ₀ hφ₀
      (D.κ M) (streamVel (D.Φ M)) Kw aM (a + T₀) U₀ (fun _ _ => 0) (fun _ _ => 0) U Uw Uk ∧
    Gw.IsRegSolution P (fun _ => isoPairedKernel (D.termRW σw M) nW)
      (fun _ => isoPairedKernel (D.termRW σw M) nW) φ₀ hφ₀
      (D.κ M) (streamVel (D.Φ M)) Kw aM (a + T₀) U₀ (fun _ _ => 0) (fun _ _ => 0) V Vw Vk ∧
    strongEnergy (D.termRStar cK M) (D.κ M) (Gw.mass law) aM (a + T₀) U Uw +
        strongEnergy (D.termRStar cK M) (D.κ M) (Gw.mass law) aM (a + T₀) V Vw ≤
      ENNReal.ofReal (CK * Real.sqrt (l2NormSq f)) ∧
    strongEnergy (D.termRStar cK M) (D.κ M) (Gw.mass law) aM (a + T₀)
        (fun v t => U v t - V v t) (fun v t => Uw v t - Vw v t) ≤
      ENNReal.ofReal (CK * D.eps M ^ (χw + σw * L) * Real.sqrt (l2NormSq f))

/-- The finest scalar solution, the weak lift `𝒲_w` (linear on fields of class `C^{L_w+3}`, with
the scaled Sobolev readout bound on classical representatives of the order `L_w + 3`, measured by
the weighted norm at the order `L_w + 5`) and the weak identity on `[a+τ, a+T₀]`.
Linearity is asserted only on `C^{L_w+3}` fields. The composed readout differentiates
its input (`orderedDerivative`, an iterated `fderiv`), so it is not additive on arbitrary fields;
it is applied only to classical representatives of order `L_w + 3`.
The readout bound takes `z` at the order `L_w + 5`. The lift estimate of the tree
(`weak_lift_rep`) reads sup norms of the derivatives of order at most `L_w + 3`, which cost two
more `L²` orders in two dimensions. -/
def IsWeakReadout (law : BirthLaw) (M Jw Lw Kw : ℕ) (κ a τ T₀ s Pw cK Cread Cid : ℝ)
    (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ) (Gw : GenStage D ScalarH Dm b j₀)
    (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ)
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root)) : Prop :=
  IsWeakSolutionOn (streamVel (D.Φ (M + Jw))) κ a (a + T₀) f θ ∧
    (∀ t (z₁ z₂ : CompIn Gw.comps → Vec 2 → ℝ) (c : ℝ),
      (∀ v, ContDiff ℝ ((Lw + 3 : ℕ) : ℕ∞) (z₁ v)) →
      (∀ v, ContDiff ℝ ((Lw + 3 : ℕ) : ℕ∞) (z₂ v)) →
      Ww t (fun v => z₁ v + c • z₂ v) = Ww t z₁ + c • Ww t z₂) ∧
    (∀ t (z : ∀ v : CompIn Gw.comps, TorusHk (Lw + 5) (ScalarH v.1.root)) (az : CompIn Gw.comps → Vec 2 → ℝ),
      (∀ v, IsClassicalRep (z v) (az v) (Lw + 3)) →
      CsNormLe s (Ww t az)
        (Cread * D.eps (M + Jw) ^ (-(1 + s)) *
          weightedNorm (D.termRStar cK M) (Gw.mass law) (fun _ => 1) z)) ∧
    ∀ t ∈ Set.Icc (a + τ) (a + T₀), ∀ aV : CompIn Gw.comps → Vec 2 → ℝ,
      (∀ v, IsClassicalRep (V v t) (aV v) (Lw + 3)) →
      ∃ Θt : Vec 2 → ℝ, IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
        CsNormLe s (fun x => Θt x - Ww t aV x) (Cid * D.eps M ^ Pw * Real.sqrt (l2NormSq f))

/-- The weak reserve constants `k_W` meet the seed's allocation: reserves at least the seed's
(`K_s, K_an, L_an, J_m, L_*`), a producer offset at least one grade below the seed's (the reserve
gap `g_T = 1` in grades of the producer grid) and the same top grade, a nonnegative envelope reserve
below the smallest graded reserve, moments through the requested order `L`. -/
def IsWeakAllocation (kW kS : InvConsts) (L : ℕ) : Prop :=
  kS.Ks ≤ kW.Ks ∧ kS.Kan ≤ kW.Kan ∧ kS.Lan ≤ kW.Lan ∧ kS.Jm ≤ kW.Jm ∧ kS.Lstar ≤ kW.Lstar ∧
    kW.G0 + 1 ≤ kS.G0 ∧ kW.Hprod = kS.Hprod ∧ 0 ≤ kW.mEnv ∧ kW.mEnv < 1 / ((kW.Hprod : ℝ) + 1) ∧
    L ≤ kW.Lker
end

/-! The **actual terminal construction**.

* `termCovPrimitive`: the new covariance primitive `H_M(t) = ∫_{t_p}^t (J_M - BI)`, anchored at the
  quiet endpoint `t_p` (its original anchor; no earlier covariance primitive exists at entry).
* `termProvParams`: the tag parameters of the terminal passage: fresh birth length `ρ` and recorded
  width `r_new = ρE^{t_T}`, equal to the stored width of its kernel
  `isoPairedKernel r_new`.
* `termMenu`: the menus of the terminal passage, read as one passage of the actual successor
  construction at level `M` (`IsActualSuccessor`) with the grade cutoff `1` (no grade frontier: one
  passage creates at most one birth per component), the word length `R_T`, the cell cutoff `N_T`,
  the covariance degree `p_T` and the covariance anchor `t_p`. The old block `OS_w` is copied into
  every word (the copies of `IsActualSuccessor`), prefix sources are the letters with
  `λ = E^{-η₀}`, empty words start at `g`, new words at zero.
* `IsTerminalPrepMap`, `IsTerminalPrepBounds`: the asserted properties of the capped preparation
  `(t_p, 𝐏_term)` (Proposition 14.10(a) of the paper): `t_p` quiet with `ch ≤ t_p - a_M ≤ Ch`,
  `𝐏_term` linear and fixing constant component vectors, `|g|_{ρ,K_out;π} ≤ C‖f‖`,
  `‖V(t_p) - g‖_π ≤ CE^{Q_T}‖f‖` and `|V(t_p) - g|_{r_*,k₀;π} ≤ CE^{Q_T/2}‖f‖`.
* `IsTerminalTrace`: `Z_{(v,∅)}(t_p) = g_v`, zero on new words.
* `IsTerminalLiftedField`: `T_MP𝖱_TZ`: the lift coefficients of the weak stage's fiber at the native
  chart of every pulse from the original start (`IsLiftSequence`) at the terminal slow length
  `ρ = c_r√(κ_{M-1}τ_M'')` (the source convention, used throughout), `P = P_{p_T}(𝒞)` with the
  covariance anchored at `t_p`, the readout `𝖱_T` (`succReadout`, weights `E^{η₀|σ|}`), a classical
  representative, and the glued lift (`gluedLift`). -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- `H_M(t) = ∫_{t_p}^t (J_M - BI)`. -/
def termCovPrimitive (D : OCData) (M : ℕ) (tp t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ocCovariance D.α D.q D.Λ D.ζ M (D.κ M) (D.κ (M - 1)) tp t

/-- The tag parameters of the terminal passage. -/
def termProvParams (D : OCData) (Cw cr tT η₀ : ℝ) (N p M : ℕ) : ProvParams where
  C := Cw
  w := fun _ => 1
  eps := D.eps
  δ := ocDelta D.α D.q
  η0 := η₀
  N := N
  p := p
  Rb := fun _ => D.termRho cr M
  rb := fun _ => D.termRNew cr tT M

/-- The menus of the terminal passage (grade cutoff `1`, words of length at most `R_T`). -/
def termMenu (Mnat : ℕ) (A : Finset WordLetter) (RT NT pT sX sZ : ℕ) (η₀ tp cr : ℝ) : SuccMenu where
  M := Mnat
  A := A
  H := 1
  J := RT
  N := NT
  p := pT
  sX := sX
  sZ := sZ
  η0 := η₀
  anchor := tp
  lenFactor := cr

/-- The f-independent properties of the capped preparation: the quiet endpoint, the
normalization, and the slow quiet margin of half-width `τ'_M` around the endpoint
(Proposition 14.10(a) of the paper; the endpoint is the midpoint of an actual slow quiet margin of
level `M`, which the initial discrepancy uses). -/
def IsTerminalPrepMap (M Kw Kout : ℕ) (c C : ℝ) (Gw : GenStage D ScalarH Dm b j₀) (aM tp : ℝ)
    (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk Kout (ScalarH v.1.root))) : Prop :=
  tp ∈ ocQuietTimes D.α D.q D.Λ D.ζ M ∧ aM + c * D.termH M ≤ tp ∧ tp ≤ aM + C * D.termH M ∧
    (∀ (cv : CompIn Gw.comps → ℝ) (X : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)),
      (∀ v, (X v).toFunction.jet (valueIndex2 Kw) =ᵐ[volume.restrict AVenhance.unitCube]
        fun _ => cv v) →
      ∀ v, (Pterm X v).toFunction.jet (valueIndex2 Kout) =ᵐ[volume.restrict AVenhance.unitCube]
        fun _ => cv v) ∧
    Set.Icc (tp - ocTauP D.α D.q D.Λ M) (tp + ocTauP D.α D.q D.Λ M) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ M

/-- The model bounds of the capped preparation for one datum (Proposition 14.10(a) of the paper). -/
def IsTerminalPrepBounds (law : BirthLaw) (M Kw Kout k₀ : ℕ) (hk₀w : k₀ ≤ Kw) (hk₀o : k₀ ≤ Kout)
    (cr cK C QT : ℝ) (f : Vec 2 → ℝ) (Gw : GenStage D ScalarH Dm b j₀) (aM tp : ℝ)
    (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk Kout (ScalarH v.1.root)))
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root)) : Prop :=
  weightedNorm (D.termRho cr M) (Gw.mass law) (fun _ => 1) (Pterm fun v => V v aM) ≤
      C * Real.sqrt (l2NormSq f) ∧
    weightedNorm 1 (Gw.mass law) (fun _ => 1)
        (fun v => truncateTorusHk (Nat.zero_le Kw) (V v tp) -
          truncateTorusHk (Nat.zero_le Kout) (Pterm (fun v => V v aM) v)) ≤
      C * D.eps (M - 1) ^ QT * Real.sqrt (l2NormSq f) ∧
    weightedNorm (D.termRStar cK M) (Gw.mass law) (fun _ => 1)
        (fun v => truncateTorusHk hk₀w (V v tp) - truncateTorusHk hk₀o (Pterm (fun v => V v aM) v)) ≤
      C * D.eps (M - 1) ^ (QT / 2) * Real.sqrt (l2NormSq f)

/-- The trace of the first coarse family: `g` on the empty words, zero on new words. -/
def IsTerminalTrace (Gw Gt : GenStage D ScalarH Dm b j₀) {K : ℕ}
    (g : ∀ v : CompIn Gw.comps, TorusHk K (ScalarH v.1.root))
    (Z₀ : ∀ v' : CompIn Gt.comps, TorusHk K (ScalarH v'.1.root)) : Prop :=
  (∀ v' (hv : v'.1 ∈ Gw.comps), Z₀ v' = g ⟨v'.1, hv⟩) ∧ ∀ v', v'.1 ∉ Gw.comps → Z₀ v' = 0

/-- `T g` for a classical field `g` on the weak components: the glued Eulerian lift at the terminal
slow length `ρ = c_r√(κ_{M-1}τ_M'')`. -/
def termLiftedRep (Gw : GenStage D ScalarH Dm b j₀) (M N depth : ℕ) (cr : ℝ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (g : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root) :
    ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root :=
  fun t x => gluedLift (ocObsPulses D.α D.q D.Λ M t t) (fun k => ocCutoff D.α D.q D.Λ M k)
    (D.cellScaleSq M) (cr * liftLength D M) (D.eps M)
    (ocDStar D.q D.Λ M (D.κ M) (D.κ (M - 1)) / (cr * liftLength D M)) N depth CcT
    (fun k s' y => D.flowOf (M - 1) s' y (D.slotAnchor M k))
    (fun k s' y => D.flowOf (M - 1) (D.slotAnchor M k) y s') g t x

/-- The lifted field `T_MP𝖱_TZ` of the terminal passage (covariance anchored at `t_p`, slow length
`ρ = c_r√(Bh)`). -/
def IsTerminalLiftedField (Gw Gt : GenStage D ScalarH Dm b j₀) (M p Kout N depth sX sZ : ℕ)
    (η₀ tp tf cr : ℝ) (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Kout (ScalarH v.1.root)) {K : ℕ}
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kout - 2 * p) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
    (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk K (ScalarH v.1.root)) : Prop :=
  (∀ (k : ℤ) (hk : Odd k),
    IsLiftSequence (familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
        (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩)))
      sX sZ (D.slotStart M k / D.cellScaleSq M)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) N depth (CcT k)) ∧
  (∀ v, ∀ t ∈ Set.Icc tp tf,
    IsCovImage (covPolyP (termCovPrimitive D M tp t) p)
      (succReadout M (D.eps (M - 1)) η₀ Kout (fun v' => Z v' t) v) (PZ v t) ∧
    IsClassicalRep (PZ v t) (fun x => aRep t x v) (Kout - 2 * p)) ∧
  ∀ v, ∀ t ∈ Set.Icc tp tf,
    (û v t).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => termLiftedRep Gw M N depth cr CcT aRep t x v
end

/-! The **terminal seed** as the cascade's seed.

The retained terminal family `Gt` (level `n = M-1`) carries births of the terminal passage (its
words). The cascade's seed has components of grade zero and marker `I`: the strong birth sets are
empty, and earlier birth tuples remain stored despite strong grade zero. `IsSeedEncoding` is the
re-rooting: a bijection `ι` of the components of `Gt` onto root components of the seed
(`births = []`), carrying the masses and readout weights of `Gt` (terminal birth law) into root
masses/readouts `rootM`, `rootR` (any cascade law with these roots); every identity becomes a seed
identity whose tag is the complete provenance tag of the terminal identity (original birth list,
length, width, excess, witness, order), whose seed kernel is the identity's actual kernel (`S_w` at
`r_w` for the old block, `S_α` at `r_new` for fresh letters), and whose maps, records, pieces,
weights, actual contexts and chart coefficients are those of `Gt` (restriction keeps coefficient
records and original inverse starts).

`TerminalSeedClauses` collects the seed clauses consumed by `seed_invariant_discharge` and
`preservation_successor`, for the datum `f_n = Z(s_n)`:
* `n = M-1`, `s_n = t_p + h`, the datum is `Z(s_n)` transported by `ι`, with
  `‖f_n‖_π ≤ C_entry‖f‖₂`, and the cascade window `[s_n, s_n + 4τ_n''] ⊂ [a_M, a+T₀]`;
* `IsGeneratedSeed` for every tag parameter `P` and every fresh
  kernel family of the cascade (the seed has only seed identities, so neither enters): generated
  membership with solved weak inverse leaves, both envelopes, the ledger `S_n^♯ ≤ C_eε_n^{τ_e}`,
  kernels, widths, lengths `≤ ε_n`, the stage invariant with the quiet certificate at `kS`;
* the width exponents `σ_f^S = δ` and `λ_c^S > 3δ`;
* the seed allocation (`IsSeedAllocation`: moments through `max{L_pr, L_c, L_f}`, reserves,
  producer offset `G₀`, `H_prod = G₀ + H + 1`);
* `∑π_+ < 5/6`, `∑ω_+²π_+ < 5/6`, and the cascade law `IsSuccessorLaw`. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The seed tag recording complete provenance tags. -/
def seedTagOf (t : ProvTags) : SeedTag where
  size := t.witness
  birthLevel := t.birthLevel
  birthExcess := t.birthExcess
  length := t.length
  width := t.width
  births := t.births
  maxOrder := t.order

/-- The re-rooting of the terminal family `Gt` (order index `Dt`) as the seed (order index `Ds`;
the cascade's index `succSchedD D̄₀ N p (H+1)`): a relabeling of the entire actual terminal family,
identity data compared field by field. -/
def IsSeedEncoding {Dt Ds : ℕ} (Pt : ProvParams) (lawT : BirthLaw) (rootM rootR : ℕ → ℝ)
    (seedKt freshKt seedKc : ℕ → KernelSpec)
    (Gt : GenStage D ScalarH Dt b j₀) (seed : GenStage D ScalarH Ds b j₀)
    (ι : CompIn Gt.comps ≃ CompIn seed.comps) : Prop :=
  seed.level = Gt.level ∧ (∀ v, (ι v).1.births = []) ∧
    (∀ v, rootM (ι v).1.root = Gt.mass lawT v ∧ rootR (ι v).1.root = Gt.readoutWeight lawT v) ∧
    (∀ p, (seed.actual p).1 = (Gt.actual p).1) ∧ (∀ p, seed.fam.piece p = Gt.fam.piece p) ∧
    (∀ p t, seed.fam.weight p t = Gt.fam.weight p t) ∧
    ∃ (e : ∀ v u, Gt.fam.Γ v u ≃ seed.fam.Γ (ι v) (ι u)) (idx : ∀ v u, Gt.fam.Γ v u → ℕ),
      (∀ v u (γ : Gt.fam.Γ v u) v' u' (γ' : Gt.fam.Γ v' u'),
        idx v u γ = idx v' u' γ' → v = v' ∧ u = u' ∧ HEq γ γ') ∧
      ∀ v u (γ : Gt.fam.Γ v u),
        seed.prov (ι v) (ι u) (e v u γ) = .seed (idx v u γ) (seedTagOf ((Gt.prov v u γ).tags Pt)) ∧
        seedKc (idx v u γ) = Gt.kernelOf Pt seedKt freshKt v u γ ∧
        (seed.fam.identity (ι v) (ι u) (e v u γ)).map = (Gt.fam.identity v u γ).map ∧
        (seed.fam.identity (ι v) (ι u) (e v u γ)).record = (Gt.fam.identity v u γ).record ∧
        (seed.fam.identity (ι v) (ι u) (e v u γ)).maxOrder = (Gt.fam.identity v u γ).maxOrder ∧
        ∀ (p : OddSlot) (c : StageCtx D b j₀ seed.level p) (c' : StageCtx D b j₀ Gt.level p),
          c.1 = c'.1 → ∀ (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2),
          seed.fam.flux p c (ι v) (ι u) (e v u γ) d I t X z = Gt.fam.flux p c' v u γ d I t X z
end

/-! The clauses of the conclusion of
`entry_terminal_of_weak` as named predicates (the inline statement would be large).

* `IsTerminalLaw`: the birth law of the terminal passage: the weak root masses
  and readouts, one mass `p_T = c_H E^{η_b}/#Σ_T` per nonempty word (`wordCount = #Σ_T`,
  `etaB = η₀/2`), readout `E^{η₀|σ|}`, no marker.
* `TerminalSeedClauses`: the seed clauses for every cascade law with the seed's root masses and
  readouts, at the a priori depth/order bounds `r̄₀, D̄₀`. The seed allocation and the
  exponents `σ_f^S = δ`, `λ_c^S = λ_entry` are properties of the constants `kS`, stated with them.
* `TerminalFamilyClauses`: the first coarse family `Z` from the trace `g = 𝐏_term V(a_M)`, its
  energy, and the outgoing datum `f_n = Z(s_n)`.
* `EntryIdentityClauses`: the terminal identity: for the lifted field
  `T_MP𝖱_TZ`, `e_T = 𝒲_w(V - T_MP𝖱_TZ)` has `sup ‖e_T‖_{C^s} ≤ CE^{P_T}‖f‖₂` on `[t_p, a+T₀]`, and
  the total scalar error `θ - 𝒲_wT_MP𝖱_TZ` is at most `C(x^{P_w} + E^{P_T})‖f‖₂` in `C^s` on
  `[max(t_p, a+τ), a+T₀]`. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The birth law of the terminal passage. -/
def IsTerminalLaw (lawW lawT : BirthLaw) (cH η₀ : ℝ) (nWords : ℕ) : Prop :=
  lawT.rootMass = lawW.rootMass ∧ lawT.rootReadout = lawW.rootReadout ∧ lawT.cH = cH ∧
    lawT.iota = 0 ∧
    lawT.wordCount = max 1 nWords ∧ lawT.etaB = η₀ / 2 ∧ lawT.eta0 = η₀

/-- The seed clauses of the terminal seed, for every cascade law with the seed's
roots, every tag parameter and every fresh kernel family of the cascade. -/
def TerminalSeedClauses (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (Mnat n : ℕ) (kS : InvConsts) (Ce τe : ℝ)
    (r₀ D₀ : ℕ) (seed : GenStage D ScalarH Dm b j₀) (sn tf : ℝ) : Prop :=
  (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r) ∧
    ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
      (∀ (P : ProvParams) (freshK : ℕ → KernelSpec),
        IsGeneratedSeed law P seedKc freshK φ₀ hφ₀ Mnat kS seed n sn tf Ce τe r₀ D₀) ∧
      IsSeedPointwiseMolecular law kS seed sn tf ∧
      ∑ v, seed.mass law v < 5 / 6 ∧ ∑ v, seed.readoutWeight law v ^ 2 * seed.mass law v < 5 / 6

/-- The first coarse family from the trace `g`, its energy, and the outgoing datum
`f_n = Z(s_n)` transported to the seed. -/
def TerminalFamilyClauses (Pt : ProvParams) (seedKt freshKt : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (lawW lawT : BirthLaw) (rootM : ℕ → ℝ) (M Kout : ℕ) (cr C Centry tp sn tf : ℝ)
    (f : Vec 2 → ℝ) (Gw Gt : GenStage D ScalarH Dm b j₀) {Ds : ℕ} (seed : GenStage D ScalarH Ds b j₀)
    (ι : CompIn Gt.comps ≃ CompIn seed.comps)
    (g : ∀ v : CompIn Gw.comps, TorusHk Kout (ScalarH v.1.root))
    (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Kout (ScalarH v.1.root)) : Prop :=
  ∃ (Z₀ : ∀ v : CompIn Gt.comps, TorusHk Kout (ScalarH v.1.root))
    (Zw : ∀ v : CompIn Gt.comps, ℝ → TorusHk (Kout + 1) (ScalarH v.1.root))
    (Zk : ∀ v u (_ : Gt.fam.Γ v u), ℝ → TorusHk (Kout + Dm - 1) (ScalarH u.1.root)),
    IsTerminalTrace Gw Gt g Z₀ ∧
    Gt.IsRegSolution Pt seedKt freshKt φ₀ hφ₀ (D.termB M) (streamVel (D.Φ (M - 1))) Kout tp tf Z₀
      (fun _ _ => 0) (fun _ _ => 0) Z Zw Zk ∧
    ENNReal.ofReal (weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g) +
        strongEnergy (D.termRho cr M) (D.termB M) (Gt.mass lawT) tp tf Z Zw ≤
      ENNReal.ofReal (C * Real.sqrt (l2NormSq f)) ∧
    ∃ fn : ∀ v : CompIn seed.comps, TorusHk 0 (ScalarH v.1.root),
      (∀ v, fn (ι v) = truncateTorusHk (Nat.zero_le Kout) (Z v sn)) ∧
      weightedNorm 1 (fun v => rootM v.1.root) (fun _ => 1) fn ≤ Centry * Real.sqrt (l2NormSq f)

/-- The terminal identity and the total scalar error. -/
def EntryIdentityClauses (Gw Gt : GenStage D ScalarH Dm b j₀) (M pT Kout Kw Lw NT depth sX sZ : ℕ)
    (η₀ tp a τ T₀ s Pw PT C cr : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ)
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
    (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Kout (ScalarH v.1.root)) : Prop :=
  (∃ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kout - 2 * pT) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
      (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
    IsTerminalLiftedField Gw Gt M pT Kout NT depth sX sZ η₀ tp (a + T₀) cr Z CcT PZ aRep û) ∧
  ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kout - 2 * pT) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
    (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
    IsTerminalLiftedField Gw Gt M pT Kout NT depth sX sZ η₀ tp (a + T₀) cr Z CcT PZ aRep û →
    ∀ t ∈ Set.Icc tp (a + T₀), ∀ aV : CompIn Gw.comps → Vec 2 → ℝ,
      (∀ v, IsClassicalRep (V v t) (aV v) (Lw + 3)) →
      CsNormLe s (Ww t fun v x => aV v x - termLiftedRep Gw M NT depth cr CcT aRep t x v)
          (C * D.eps (M - 1) ^ PT * Real.sqrt (l2NormSq f)) ∧
        (a + τ ≤ t →
          ∃ Θt : Vec 2 → ℝ, IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
          CsNormLe s (fun x => Θt x - Ww t (fun v x' => termLiftedRep Gw M NT depth cr CcT aRep t x' v) x)
            (C * (D.eps M ^ Pw + D.eps (M - 1) ^ PT) * Real.sqrt (l2NormSq f)))
end

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The certificates of the retained terminal family that make its
regularized system solvable at every order up to `K` on `[t_p, t_f]`, at the terminal diffusivity
`B = κ_{M-1}` and the enhanced radius `ρ = c_r√(Bh)`. It is the terminal analogue of the second
conjunct of `NextFamilyClauses`, with the coefficient premises of the kernel energy estimate
`kernel_energy_torus` (`hB_meas`, `hB_smooth`, `hB_per`, `hB_fin`) and its regularizer premise
`hS`. The terminal seed clauses produce it; the first coarse family, the residual and the error
energy consume it.

`TerminalSeedCertificate` bundles the three products of the seed side of the route that the
residual and the error energy consume (the seed side of the terminal route): a re-rooting of the retained family onto
a seed (`IsSeedEncoding`), the seed clauses (`TerminalSeedClauses`) and the certificates above.
As a premise, `(∃ seed …, A ∧ B ∧ C) → goal` is `∀ seed …, A → B → C → goal` when the goal does not
mention the seed; the bundle keeps the two consuming statements within the default elaboration
budget.

The degenerate cases are included: an empty retained family (every clause is vacuous over the
empty index, and the Schur bound of the empty matrix holds); orders below two (`Finset.Icc 2 Dm`
is empty, so the coefficient clauses are vacuous and the Schur matrix vanishes); `K = 0` (the
Schur bound and the regularizer clause are asked at order `0` only). -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The certificates of the retained terminal family `Gt` at every order `kk ≤ K`: the
kernel-priced Schur bound `1/8` at radius `ρ = c_r√(Bh)` and diffusivity `B = κ_{M-1}`, the
regularizer property of every kernel at every radius, and the coefficient premises of
`kernel_energy_torus`. -/
def TerminalRetainedClauses (lawT : BirthLaw) (Pt : ProvParams) (seedKt freshKt : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (cker : ℕ → ℝ) (M K : ℕ) (cr tp tf : ℝ)
    (Gt : GenStage D ScalarH Dm b j₀) : Prop :=
  (∀ kk ≤ K, SchurBound (1 / 8) (kernelSchurMatrix (ι := CompIn Gt.comps)
      (h := fun v => ScalarH v.1.root) (Γ := Gt.fam.Γ) (G := fun _ u _ => ScalarH u.1.root)
      (D.κ (M - 1)) (D.termRho cr M) (fun v => Gt.mass lawT v) kk Dm tp tf cker
      (fun v u γ => (Gt.kernelOf Pt seedKt freshKt v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
      (fun v u γ d => Gt.physCoeff v u γ d.1))) ∧
  (∀ v u (γ : Gt.fam.Γ v u), ∀ ϱ : ℝ, 0 < ϱ → ∀ kk ≤ K,
    IsSpatialRegularizerTorus ϱ kk Dm tp tf cker
      (Gt.kernelOf Pt seedKt freshKt v u γ).width
      (Gt.sysS Pt seedKt freshKt φ₀ hφ₀ v u γ)) ∧
  ∀ v u (γ : Gt.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)),
    (Measurable fun p : Set.Icc tp tf × Vec 2 => Gt.physCoeff v u γ d.1 p.1 p.2) ∧
    (∀ t ∈ Set.Icc tp tf, ContDiff ℝ (K : ℕ) (Gt.physCoeff v u γ d.1 t)) ∧
    (∀ t ∈ Set.Icc tp tf, AVenhance.IsZ2Periodic (Gt.physCoeff v u γ d.1 t)) ∧
    coefficientSeminorm (D.termRho cr M) K tp tf (Gt.physCoeff v u γ d.1) ≠ ⊤

/-- The seed side of the terminal route for the retained family `Gt`: a re-rooting onto a seed at
the order index `Ds`, its seed clauses, and the certificates of `Gt`. -/
def TerminalSeedCertificate (Pt : ProvParams) (lawT : BirthLaw) (seedKt freshKt : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (cker : ℕ → ℝ) (Mnat n M K : ℕ) (kS : InvConsts)
    (Ce τe : ℝ) (r₀ D₀ Ds : ℕ) (cr tp sn tf : ℝ) (Gt : GenStage D ScalarH Dm b j₀) : Prop :=
  ∃ (seed : GenStage D ScalarH Ds b j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn Gt.comps ≃ CompIn seed.comps),
    IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι ∧
    TerminalSeedClauses rootM rootR seedKc φ₀ hφ₀ Mnat n kS Ce τe r₀ D₀ seed sn tf ∧
    TerminalRetainedClauses lawT Pt seedKt freshKt φ₀ hφ₀ cker M K cr tp tf Gt

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! The conclusion of `entry_terminal_residual` as a named predicate (a `def`, so that elaborating
the statement does not unfold it inline). `TerminalResidualClauses`: the error `e = V - û` of order
`k₀` solves the paired weak equation (kernel `S_w`) on `[t_p, t_f]` with a residual presentation
`div R + q`, and for every word of order `j ≤ k₀` the differentiated residual norm at `r_*` is at
most `C·bill·‖f‖₂`. The presentation `(R, q)` is a.e. strongly measurable on the window
(every forced energy estimate needs measurable forcing). -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The residual presentation of the terminal error and its differentiated bill. -/
def TerminalResidualClauses (PW : ProvParams) (seedK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (lawW : BirthLaw) (M Kw k₀ : ℕ) (hk : k₀ ≤ Kw) (cK C bill tp tf : ℝ)
    (f : Vec 2 → ℝ) (Gw : GenStage D ScalarH Dm b j₀)
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
    (Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
    (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk k₀ (ScalarH v.1.root))
    (ŵ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (k₀ + 1) (ScalarH v.1.root)) : Prop :=
  ∃ (Rres : ∀ v : CompIn Gw.comps, ℝ → TorusHk k₀ (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (qres : ∀ v : CompIn Gw.comps, ℝ → TorusHk k₀ (ScalarH v.1.root))
    (ek : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (k₀ + Dm - 1) (ScalarH u.1.root)),
    Gw.IsRegSolution PW seedK seedK φ₀ hφ₀ (D.κ M) (streamVel (D.Φ M)) k₀ tp tf
      (fun v => truncateTorusHk hk (V v tp) - û v tp) Rres qres
      (fun v t => truncateTorusHk hk (V v t) - û v t)
      (fun v t => truncateTorusHk (Nat.succ_le_succ hk) (Vw v t) - ŵ v t) ek ∧
    (∀ (j : ℕ), j ≤ k₀ → ∀ β : DerivativeWord2 j,
      residualNorm (D.κ M) (Gw.mass lawW) (Set.Icc tp tf)
          (fun t x k v => D.termRStar cK M ^ j • (torusJetOrder (Rres v t) j β x) k)
          (fun t x v => D.termRStar cK M ^ j • torusJetOrder (qres v t) j β x) ≤
        ENNReal.ofReal (C * bill * Real.sqrt (l2NormSq f))) ∧
    (∀ v, AEStronglyMeasurable (Rres v) (volume.restrict (Set.Icc tp tf))) ∧
    (∀ v, AEStronglyMeasurable (qres v) (volume.restrict (Set.Icc tp tf)))

end AVRegularity
end
