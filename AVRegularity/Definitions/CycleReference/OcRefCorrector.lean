-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.IsWindowTestFunction
public import AVRegularity.Sobolev.Basic
public import AVRegularity.Statements.Construction.OcGamma
public import AVRegularity.Statements.Intermediate.CycleReference.OcShearVel
public import AVRegularity.Statements.Intermediate.CycleReference.OcRefFlux
public import AVenhance.Statements.Roots.IsPeriodicH1With

@[expose] public section

section
open MeasureTheory Filter Topology Homogenization AVenhance
namespace AVRegularity

/-! Energy solutions on the torus `𝕋² = ℝ²/ℤ²` of the linear
parabolic equation `∂ₜθ + b·∇θ - div(A∇θ) = div q + f` with continuous `L²` trace, the torus
analogue of `IsPlaneEnergySolution` (periodic fields, tests periodic in space, integrals over the
unit cell). Covers both
`∂ₜθ + 𝐛ₘ·∇θ - νΔθ = div q + f` (`A = νI`) and the pulled-back material equation
(`b = 0`, `A = νG + ψσ`, non-symmetric). -/

/-- `θ ∈ C([t₀,t₁];L²(𝕋²)) ∩ L²(t₀,t₁;H¹(𝕋²))` with gradient `Dθ`, trace `θ(t₀) = θ₀` on the unit
cell, solving `∂ₜθ + b·∇θ - div(A∇θ) = div q + f` on `(t₀,t₁) × 𝕋²` in the weak sense against every
smooth, `ℤ²`-periodic space-time test function vanishing for `t ≥ t₁`
(`IsWindowTestFunction t₁`):
`∬ [-θ ∂ₜφ + (b·Dθ) φ + (A Dθ)·∇φ + q·∇φ - f φ] = ∫ θ₀ φ(t₀)`, the integrals over
`(t₀,t₁) × (0,1)²` and `(0,1)²`. Each `θ(t)` is `ℤ²`-periodic; the tested integrand is required
integrable, so no integral takes the Bochner junk value. -/
def IsTorusEnergySolution (b : ℝ → Vec 2 → Vec 2)
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (t₀ t₁ : ℝ) (q : ℝ → Vec 2 → Vec 2)
    (f : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ) : Prop :=
  ∃ Dθ : ℝ → Vec 2 → Vec 2,
    (∀ t ∈ Set.Icc t₀ t₁, IsZ2Periodic (θ t) ∧ MemL2On unitCube (θ t)) ∧
    (∀ t ∈ Set.Icc t₀ t₁,
      Tendsto (fun s => eLpNorm (fun x => θ s x - θ t x) 2 (volume.restrict unitCube))
        (𝓝[Set.Icc t₀ t₁] t) (𝓝 0)) ∧
    θ t₀ =ᵐ[volume.restrict unitCube] θ₀ ∧
    (∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) 2
      (volume.restrict (Set.Ioo t₀ t₁ ×ˢ unitCube))) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ioo t₀ t₁)), IsPeriodicH1With (θ t) (Dθ t)) ∧
    ∀ φ : ℝ → Vec 2 → ℝ, IsWindowTestFunction t₁ φ →
      Integrable
        (fun p : ℝ × Vec 2 =>
          -(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
            + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
            + vecDot ((A p.1 p.2).mulVec (Dθ p.1 p.2)) (spaceGrad (φ p.1) p.2)
            + vecDot (q p.1 p.2) (spaceGrad (φ p.1) p.2) - f p.1 p.2 * φ p.1 p.2)
        (volume.restrict (Set.Ioo t₀ t₁ ×ˢ unitCube)) ∧
      ∫ p in Set.Ioo t₀ t₁ ×ˢ unitCube,
          (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
            + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
            + vecDot ((A p.1 p.2).mulVec (Dθ p.1 p.2)) (spaceGrad (φ p.1) p.2)
            + vecDot (q p.1 p.2) (spaceGrad (φ p.1) p.2) - f p.1 p.2 * φ p.1 p.2)
        = ∫ x in unitCube, θ₀ x * φ t₀ x

end AVRegularity
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Ordered coordinate derivatives of a planar vector map.
-/

/-- Ordered coordinate differentiation of a planar vector map, applying directions in the order
of the word (the vector-valued analogue of `orderedCoefficientDerivative`). -/
noncomputable def orderedPartial (f : Vec 2 → Vec 2) :
    (j : ℕ) → DerivativeWord2 j → Vec 2 → Vec 2
  | 0, _ => f
  | j + 1, w => fun x =>
      fderiv ℝ (orderedPartial f j (Fin.init w)) x (basisVec (w (Fin.last j)))

/-! The Euclidean tensor norm of the order-`j` derivative array
of a planar vector map. -/

/-- `|D^j f(x)| = (∑_{words w of length j} ∑_{k} |∂_w f_k(x)|²)^{1/2}`. -/
noncomputable def derivArrayNorm (f : Vec 2 → Vec 2) (j : ℕ) (x : Vec 2) : ℝ :=
  Real.sqrt (∑ w : DerivativeWord2 j, vecNormSq (orderedPartial f j w x))

end AVRegularity
end

section
namespace AVRegularity

/-! The exponent `c = γ/2 + δ`. -/

/-- `c = γ/2 + δ`. -/
noncomputable def ocC (α q : ℝ) : ℝ := ocGamma α q / 2 + ocDelta α q

/-! The parent radius `ρ_par = E^{1+γ/2}`.
-/

/-- `ρ_par = E^{1+γ/2}`, `E = ε_{m-1}`. -/
noncomputable def ocRhoPar (α q : ℝ) (Λ m : ℕ) : ℝ :=
  ocEpsilon q Λ (m - 1) ^ (1 + ocGamma α q / 2)

/-! The renewal diffusion length `R_h = √(Bh)`.
-/

/-- `R_h = √(B h)`, `h = τ_m''`. -/
noncomputable def ocRh (α q : ℝ) (Λ m : ℕ) (B : ℝ) : ℝ := Real.sqrt (B * ocTauPP α q Λ m)

/-! The glueing cutoffs `ϖ_k`. -/

/-- `ϖ_k(t) = 𝖧(5/2 - 2|t - kτ|/τ)`, `τ = τ_m`, `𝖧 = Real.smoothTransition`. -/
noncomputable def ocCutoff (α q : ℝ) (Λ m : ℕ) (k : ℤ) (t : ℝ) : ℝ :=
  Real.smoothTransition
    (5 / 2 - 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m)

/-! Complete cores of a renewal block. -/

/-- The odd slot `k` has a complete core in the block labelled `l`: its label is `l`, and the
slow cutoff `ζ̂_{m,l}` is identically one on the core `[(k-1/3)τ, (k+1/3)τ]`, `τ = τ_m`. -/
def IsOCCompleteCore (α q : ℝ) (Λ m : ℕ) (l k : ℤ) : Prop :=
  Odd k ∧ ocLabel α q Λ m k = l ∧
    ∀ t ∈ Set.Icc (((k : ℝ) - 1 / 3) * ocTau α q Λ m) (((k : ℝ) + 1 / 3) * ocTau α q Λ m),
      slowEnvelope α q Λ m l t = 1

end AVRegularity
end

section
open Homogenization
namespace AVRegularity

/-! The single-pulse corrector `χ_k`.
-/

/-- `χ_k(t,y) = -M_k(t) 𝐮_k(y)` (`χ_{m,k}^ν`). -/
noncomputable def ocPulseCorrector (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν : ℝ) (k : ℤ)
    (t : ℝ) (y : Vec 2) : Vec 2 :=
  -(ocPulseMemory α q Λ ζ m ν k t) • ocShearVel α q Λ m k y

end AVRegularity
end

section
open MeasureTheory
namespace AVRegularity

/-! The covariance `C_s(t)`. -/

/-- `C_s(t) = ∫_s^t (J - B I)`, entrywise. -/
noncomputable def ocCovariance (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν B s t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j =>
    ∫ r in s..t, (ocRefFlux α q Λ ζ m ν r i j - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)

end AVRegularity
end

section
open Homogenization
namespace AVRegularity

/-! The glued reference corrector `χ_ref`.
-/

/-- `χ_ref = ∑_{k odd} ϖ_k χ_k` (`χ_m^ν`). At each `t` only the finitely many slots with
`|t - kτ| < 5τ/4` contribute. -/
noncomputable def ocRefCorrector (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν : ℝ) (t : ℝ)
    (y : Vec 2) : Vec 2 :=
  ∑' k : {k : ℤ // Odd k},
    ocCutoff α q Λ m k.1 t • ocPulseCorrector α q Λ ζ m ν k.1 t y

end AVRegularity
end
