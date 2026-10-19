-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleEvolution.CellL2Norm
public import AVRegularity.Statements.Intermediate.CycleWords.OcCellMetric
public import AVRegularity.Statements.Intermediate.CycleWords.OcCellCentre
public import AVRegularity.Statements.Intermediate.CoupledEnergy.DriftCoefficient
public import AVRegularity.Statements.Intermediate.CycleEvolution.OcCellDrift

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The sine part of the Bloch fibre of a plane function (see
`blochCos`): `∑_{n∈ℤ²} sin(θ·(z+n)) • g(z+n)`. -/

/-- `∑_{n∈ℤ²} sin(θ·(z+n)) • g(z+n)`. -/
def blochSin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (θ : Vec 2) (g : Vec 2 → E)
    (z : Vec 2) : E :=
  ∑' k : Fin 2 → ℤ, Real.sin (vecDot θ (z + fun i => (k i : ℝ))) • g (z + fun i => (k i : ℝ))

end AVRegularity
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity

/-! The common physical weights and fluxes of the weighted energy method: weights
`W_m = (1+|q|²)^m` and fluxes `Φ_m` with `(∂ₜ + 𝐛_m·∇ + νΔ)W_m ≤ λ_m W_m + div Φ_m` and
`ν|∇ log W_m|² + |Φ_m|²/(νW_m²) ≤ λ_m = C_m/T`, with `q` differing by a bounded amount from the
normalized label, so `W_m ≍ ⟨(Y-X₀)/R⟩^{2m}` (the moment weights of Step 3 of the proof of
Proposition 11.7 of the paper).
In the cell variables of the plane (`ν = 1`, cell time, `S = T/ℓ²`) with the actual metric `G` and
drift `v`, the weights are required for `m ≤ M` and the time window `[t₀, t₀+S]`. This is the
chart, weight and duration bounds input of the scalar package; the geometry estimates
(`cycle_geometry_energy`, `cycle_geometry_error`) take it as a premise. -/

/-- Weights `W m`, fluxes `Phi m` and rates `lam m` with: `W` of class `C²` and `Phi` of class `C¹`
in space-time, positive, comparable to `(1 + ϖ²|z - zc|²)^m` with constant `Cw m`, with the
defect inequality `∂ₜW + v·∇W + div(G∇W) ≤ λ W + div Φ` and the bound
`|∇W|²/W² + |Φ|²/W² ≤ λ`, `0 ≤ λ ≤ Cw m / S`. -/
structure ChartWeights (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (M : ℕ) (Cw : ℕ → ℝ) where
  /-- The weight `W_m(t,z)`. -/
  W : ℕ → ℝ → Vec 2 → ℝ
  /-- The weight flux `Φ_m(t,z)`. -/
  Phi : ℕ → ℝ → Vec 2 → Vec 2
  /-- The rate `λ_m`. -/
  lam : ℕ → ℝ
  smooth : ∀ m, m ≤ M →
    ContDiff ℝ 2 (fun p : ℝ × Vec 2 => W m p.1 p.2) ∧
      ContDiff ℝ 1 (fun p : ℝ × Vec 2 => Phi m p.1 p.2)
  pos : ∀ m, m ≤ M → ∀ t z, 0 < W m t z
  comparable : ∀ m, m ≤ M → ∀ t ∈ Set.Icc t₀ (t₀ + S), ∀ z : Vec 2,
    (Cw m)⁻¹ * (1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ m ≤ W m t z ∧
      W m t z ≤ Cw m * (1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ m
  defect : ∀ m, m ≤ M → ∀ t ∈ Set.Icc t₀ (t₀ + S), ∀ z : Vec 2,
    deriv (fun s => W m s z) t
        + ∑ k : Fin 2, v t z k * fderiv ℝ (W m t) z (basisVec k)
        + ∑ k : Fin 2, fderiv ℝ (fun z' => ∑ j : Fin 2, G t z' k j *
            fderiv ℝ (W m t) z' (basisVec j)) z (basisVec k)
      ≤ lam m * W m t z + ∑ k : Fin 2, fderiv ℝ (fun z' => Phi m t z' k) z (basisVec k)
  bound : ∀ m, m ≤ M → ∀ t ∈ Set.Icc t₀ (t₀ + S), ∀ z : Vec 2,
    (∑ k : Fin 2, fderiv ℝ (W m t) z (basisVec k) ^ 2) / W m t z ^ 2
        + (∑ k : Fin 2, Phi m t z k ^ 2) / W m t z ^ 2 ≤ lam m
  lam_bound : ∀ m, m ≤ M → 0 ≤ lam m ∧ lam m ≤ Cw m / S

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity

/-! The convolution kernel of a real even Fourier multiplier
`m(θ)` on the plane (as for the cutoff `Π_- = χ_-(d_*D)` with a fixed real even `χ_-`).
For the smooth compactly supported multipliers of the statement,
`k(x) = (2π)⁻² ∫ m(θ) cos(θ·x) dθ`. -/

/-- `k(x) = (2π)⁻² ∫ m(θ) cos(θ·x) dθ`. -/
def cutoffKernel (m : Vec 2 → ℝ) (x : Vec 2) : ℝ :=
  (2 * Real.pi)⁻¹ ^ 2 * ∫ θ, m θ * Real.cos (vecDot θ x)

end AVRegularity
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity

/-! A centered exact volume-preserving chart transition with its
inverse jets, with the bounds of the renewal transitions: `‖A - I‖ ≤ Cg`,
`‖D^jΥ‖ ≤ Cg(j-1)!(C/E)^{j-1}`, the same for the inverse. The
first-order bound holds at every point, not only at the centre (`Υ` is a short-time flow map,
`‖DX - I‖_∞ ≤ Cg`). In the cell variable `z = y/e` the length
scale `E` becomes `1/δ` with `δ = e/E`. The jets are through the finite reserve `q`. -/

/-- `Υ` and `Υinv` are inverse `C^q` diffeomorphisms of the plane, `Υ 0 = 0`, `det DΥ = 1`,
`‖DΥ(z) - I‖, ‖DΥinv(z) - I‖ ≤ Cg` at every `z`, `‖D^jΥ‖, ‖D^jΥinv‖ ≤ Cg(j-1)!(Cδ)^{j-1}`
for `2 ≤ j ≤ q`. -/
structure IsCenteredTransition (Υ Υinv : Vec 2 → Vec 2) (g δ C : ℝ) (q : ℕ) : Prop where
  centered : Υ 0 = 0
  left_inv : ∀ z, Υinv (Υ z) = z
  right_inv : ∀ z, Υ (Υinv z) = z
  smooth : ContDiff ℝ q Υ ∧ ContDiff ℝ q Υinv
  volume : ∀ z, (fderiv ℝ Υ z).det = 1
  dev : (∀ z, ‖fderiv ℝ Υ z - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ C * g) ∧
    ∀ z, ‖fderiv ℝ Υinv z - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ C * g
  jets : ∀ j, 2 ≤ j → j ≤ q → ∀ z,
    ‖iteratedFDeriv ℝ j Υ z‖ ≤ C * g * ((j - 1).factorial : ℝ) * (C * δ) ^ (j - 1) ∧
    ‖iteratedFDeriv ℝ j Υinv z‖ ≤ C * g * ((j - 1).factorial : ℝ) * (C * δ) ^ (j - 1)

end AVRegularity
end
end

section
@[expose] public section
open MeasureTheory Homogenization
namespace AVRegularity

/-! `(A, B)` is the retained amplitude of the band-limited function
`g` with frequencies in the ball of radius `r` (whose ordinary
Fourier reconstruction is `𝒫f = (2πd_*)⁻¹∫ e^{iξ·(y-y₀)/d_*} a[f](ξ) dξ`). The reconstruction is
written without complex exponentials (the Hilbert components are real): the complex amplitude is
`Ã(θ) = A(θ) - iB(θ)` in the cell frequency `θ = √η ξ` and `g(z) = ∫_{|θ|≤r} cos(θ·z)A + sin(θ·z)B dθ`.
The amplitude vanishes outside the ball. Numerical normalization constants (`2π e√η` between `a[f]`
and `Ã`) are fixed by the statements that use it; they are scale free. -/

/-- `A, B` vanish outside `{|θ| ≤ r}`, are integrable there, and `g` is their cos/sin transform. -/
def IsRetainedAmplitude {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Vec 2 → E)
    (r : ℝ) (A B : Vec 2 → E) : Prop :=
  (∀ θ : Vec 2, r ^ 2 < vecDot θ θ → A θ = 0 ∧ B θ = 0) ∧
    IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} ∧
    IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} ∧
    ∀ z, g z = ∫ θ in {θ : Vec 2 | vecDot θ θ ≤ r ^ 2},
      (Real.cos (vecDot θ z) • A θ + Real.sin (vecDot θ z) • B θ)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The slow Taylor polynomial of a scalar function at a point,
truncated between a lowest and a highest degree (the Taylor expansion at `X₀`; for the spatial
Taylor polynomial `G^{[K]}` through degree `K`, the positive-degree part `P_K = G^{[K]} - G₀` is
`lo = 1`). -/

/-- `∑_{r=lo}^{K} (1/r!) D^r f(X₀)[Δ,…,Δ]`: the degree-`lo..K` terms of the Taylor polynomial of
`f` at `X₀`, evaluated at `X₀ + Δ`. For `f` of class `C^K` this is `∑_{lo ≤ |γ| ≤ K} ∂^γ f(X₀)Δ^γ/γ!`. -/
def taylorSlow (lo K : ℕ) (f : Vec 2 → ℝ) (X₀ Δ : Vec 2) : ℝ :=
  ∑ r ∈ Finset.Icc lo K, ((r.factorial : ℝ))⁻¹ * iteratedFDeriv ℝ r f X₀ (fun _ => Δ)

/-! The mixed partial derivative `∂_{θ₁}^a ∂_{θ₂}^b F(θ)` of a function
of the cell frequency, through the iterated Fréchet derivative (for the frequency derivatives
`δ_ξ^α = (η/S)^{|α|/2}∂_θ^α`). It is the true derivative where `F` is
`C^{a+b}`; every statement that uses it assumes this. -/

/-- `D^{a+b}F(θ)[e₀,…,e₀,e₁,…,e₁]` with `a` copies of `e₀` and `b` copies of `e₁`. -/
def thetaPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : ℕ)
    (F : Vec 2 → E) (θ : Vec 2) : E :=
  iteratedFDeriv ℝ (a + b) F θ
    (Fin.append (fun _ : Fin a => basisVec (0 : Fin 2)) (fun _ : Fin b => basisVec (1 : Fin 2)))

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity

/-! The Fourier cutoff operator `Π_- = m(D)` of a real even multiplier `m` on a vector-valued
plane function (`Π_- = χ_-(d_*D)`), as the convolution with the kernel `cutoffKernel m`. -/

/-- `(m(D) g)(y) = ∫ k(x) g(y - x) dx`, `k = cutoffKernel m`. -/
def fourierCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : Vec 2 → ℝ)
    (g : Vec 2 → E) : Vec 2 → E :=
  fun y => ∫ x, cutoffKernel m x • g (y - x)

end AVRegularity
end
end

section
@[expose] public section
open MeasureTheory Homogenization
namespace AVRegularity

/-! A real vector-valued function has Fourier support in the closed
ball of radius `r` (the ordinary Fourier reconstruction
`𝒫f = (2πd_*)⁻¹∫ e^{iξ·(y-y₀)/d_*} a[f](ξ) dξ` has Fourier support `|ξ_F| ≤ 2ξ_*/d_*`).
The reconstruction is written without complex exponentials (the Hilbert components are real
spaces): with integrable amplitudes `A, B` on the ball,
`g(z) = ∫_{|θ|≤r} cos(θ·z) A(θ) + sin(θ·z) B(θ) dθ`. In the cell variable `z = (y-y₀)/e` the
physical frequency `ξ_F` corresponds to `θ = e ξ_F = √η ξ` (as `e/d_* = √η`), so the radius for
`|ξ| ≤ 2ξ_*` is `r = 2ξ_*√η`. -/

/-- `g` is the cos/sin transform of an amplitude pair supported in the ball (`IsRetainedAmplitude`). -/
def HasFourierSupportIn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Vec 2 → E)
    (r : ℝ) : Prop :=
  ∃ A B : Vec 2 → E, IsRetainedAmplitude g r A B

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The flux operator of a matrix coefficient `M` acting on the
gradient (word array of length one) of a component, `g ↦ (k ↦ ∑_j M_{kj} g_j)`. It is the
order-two coupling of the coupled energy estimate that carries a metric deviation:
`div(G∇u) = Δu + div((G - I)∇u)` (as in `L = L_0 - D_P - D_H`, `D_P = ν div(P_K ∇)`). The two
component indices `a = b` and the word length `m = 1` are propositional equalities so that the
operator can be inserted into the dependently typed coefficient array of the coupled energy
estimate; it is `M ⊗ id` when both hold. -/

/-- The operator `g ↦ (k ↦ ∑_j M k j • g (fun _ => j))` from `PiLp 2 (DerivativeWord2 m → h b)` to
`PiLp 2 (Fin 2 → h a)` (for `a = b`, `m = 1`). -/
def metricFlux {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (M : Matrix (Fin 2) (Fin 2) ℝ) {a b : ι} (m : ℕ) (hab : a = b)
    (hm : m = 1) :
    (PiLp 2 (fun _ : DerivativeWord2 m => h b)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h a)) := by
  subst hab hm
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => h a)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k : Fin 2 =>
      ∑ j : Fin 2, (M k j) •
        PiLp.proj 2 (fun _ : DerivativeWord2 1 => h a) (fun _ => j))

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The spatial Taylor polynomial of a matrix-valued metric about
a center, truncated between degrees `lo` and `K` (with `G₀(t) = G(t,y_l)`, `G^{[K]}` the spatial
Taylor polynomial there through degree `K`, and `P_K = G^{[K]} - G₀`): `lo = 0` is `G^{[K]}` and
`lo = 1` is `P_K`. Cell variable `z`, entrywise. -/

/-- `(i,k) ↦ ∑_{lo≤r≤K} (1/r!) D^r (G_{ik}(t,·))(zc)[(z-zc)^r]`. -/
def metricTaylor (lo K : ℕ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (zc z : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i k => taylorSlow lo K (fun z' => G t z' i k) zc (z - zc)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The weighted jet norm `‖v‖_{r,j;p} = ∑_{a≤j} r^a ‖ω_p D^a v‖₂/a!`,
`ω_p = ⟨y/R⟩^p`, of `cycle_seam`, on a family of components
with the inverse-mass sum `|x|²_π = ∑_v π_v⁻¹‖x_v‖²`. Cell variable `z = y/e`: `⟨y/R⟩ = ⟨s z⟩` with
`s = e/R`, and `r D_y = (r/e) D_z`; the scale argument is `r/e`. Jets are given as raw jets
`J v a w` (carrier weak jets or classical derivatives). `p` is a real exponent. -/

/-- `∑_{a≤j} ((r/e)^a/a!) (∑_v π_v⁻¹ ‖⟨s z⟩^p |J_v^{(a)}|‖₂²)^{1/2}` in `[0,∞]`
(`r` here is the ratio `r/e`; `⟨x⟩ = (1+|x|²)^{1/2}`). -/
def weightedJetNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ)
    (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v) : ℝ≥0∞ :=
  ∑ a ∈ Finset.range (j + 1),
    ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
      (∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
          Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z‖ ^ 2)) 2 volume ^ 2) ^ (1 / 2 : ℝ)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The raw representative of the weak derivative of a given order
and ordered word of a plane Sobolev field on all of `ℝ²`, as a total function (the plane analogue
of `torusJetOrder`). The carrier stores jets of order `≤ K`; the accessor returns the jet of order
`m` when `m ≤ K` and `0` otherwise. Every use in the cycle word statements has `m ≤ K`
structurally (the slot of the field is at least the order that is read). -/

/-- The raw jet of order `m` and word `w` of `W : PlaneHk univ K E` (`0` if `m > K`). -/
def planeJetOrder {K : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (W : PlaneHk Set.univ K E) (m : ℕ)
    (w : DerivativeWord2 m) : Vec 2 → E :=
  fun x => if hm : m ≤ K then W.toFunction.jet ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ x else 0

/-! The value representative of a plane Sobolev field (the jet of
order zero), as a total function. -/

/-- The representative `W(z)` of the value of `W : PlaneHk univ K E` (the order-zero jet). -/
def planeValue {K : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (W : PlaneHk Set.univ K E) :
    Vec 2 → E :=
  planeJetOrder W 0 (fun i => i.elim0)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The weighted factorial norm of the geometry estimates, with `W_n = ⟨(Y-X₀)/R⟩^{2n}` and
`|f|²_{W_n,ρ,k} = ∑_{r≤k} ρ^{2r} ∫ W_n |∇^r f|²/(r!)²`. Cell variable `z = Y/e`:
`(Y-X₀)/R = ϖ(z - zc)` with `ϖ = e/R`, and `ρ∇_Y = r∇_z` with `r = ρ/e`. In `[0,∞]`. -/

/-- `∑_{j≤K} (r^{2j}/(j!)²) ∫ (1 + ϖ²|z - zc|²)^n ‖∇^j U(z)‖² dz`, from the order-`K'` jets of `U`. -/
def weightedFactorialNormSq {K' : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (r : ℝ)
    (K : ℕ) (U : PlaneHk Set.univ K' E) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (K + 1),
    ENNReal.ofReal (r ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n *
        ∑ w : DerivativeWord2 j, ‖planeJetOrder U j w z‖ ^ 2)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The Sobolev norm of order `j` of a smooth cell function,
`∑_{b≤j} ‖∇^b g‖_{L²(𝕋²)}` (the `H^j` norms of the graph, the row
and the fast propagators, for every reserved norm), through the classical iterated derivatives
(Euclidean-operator norm of the multilinear map). It is used only for functions of class `C^j`
(every statement that uses it asserts `ContDiff ℝ j`); the value is in `[0,∞]`. -/

/-- `∑_{b ≤ j} ‖ x ↦ ‖D^b g(x)‖ ‖_{L²(𝕋²)}`. -/
def cellSobolevNorm (j : ℕ) (g : Vec 2 → ℂ) : ℝ≥0∞ :=
  ∑ b ∈ Finset.range (j + 1), cellL2Norm (fun x => ‖iteratedFDeriv ℝ b g x‖)

end AVRegularity
end
end

section
@[expose] public section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity

/-! The premises of the geometry estimates that concern the construction:
the preparation cover `I = [ta, ta+T]` of duration comparable to
`h = τ''_m` (`CT`), covered by the renewal blocks of the charts `l₀, …, l₀+P-1` (including every
chart anchor path; the block of chart `l` is `[(l-½)h, (l+½)h]`); the scales `R = √(BT) ≤ E`,
`ℓ² ≤ T`, `ρ_* ≤ min{e,R}` (`E = ε_{m-1}`, `e = ε_m`, `ℓ = e/√ν`); the short-flow bounds of the
background velocity `𝐛_bg = 𝐛_{m-1} = streamVel (Φ (m-1))`, `T‖D𝐛_bg‖ ≤ g` and
`T‖D²𝐛_bg‖ ≤ Cb·g/E` on the hull of `I` and the core chart anchors `l₀h, …, (l₀+P-1)h` (so that
every anchor path is covered); the duration condition `√T ℓ τ⁻¹ exp(-π²τ/(3ℓ²)) ≤ 1`; and, in
the cell variables of every chart (centres `ocCellCentre`), on the cell-time window `[ta/ℓ², (ta+T)/ℓ²]`
only, `‖G-I‖ ≤ g ≤ g₀`, `‖D_X^jG‖ ≤ C_j g E^{-j}` through
the reserve `qJ` (`D_X = ∇_y`, i.e. `‖∇_z^jG‖ ≤ C_j g (e/E)^j`) and the finite molecular drift
absorption conditions of the label-frame drift `ocCellDrift` at the radius `ρ_*/e`. The orders
`K, J, n, H` and the family are premises of the statements. -/

/-- The construction-side premises of the geometry lemma on a cover of `P` charts from `l₀`. -/
structure IsGeometryCover (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (ν B T ta ρs g g0 a B₀ lam Cb CT : ℝ)
    (qJ Kmax : ℕ) (CG : ℕ → ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2) : Prop where
  pos : 0 < ν ∧ 0 < B ∧ 0 < T ∧ 0 < ρs
  P_pos : 1 ≤ P
  RE : Real.sqrt (B * T) ≤ ocEpsilon q Λ (m - 1)
  ellT : ocEll q Λ m ν ^ 2 ≤ T
  rho_e : ρs ≤ ocEpsilon q Λ m
  rho_R : ρs ≤ Real.sqrt (B * T)
  dur : Real.sqrt T * ocEll q Λ m ν / ocTau α q Λ m *
    Real.exp (-(Real.pi ^ 2 * ocTau α q Λ m) / (3 * ocEll q Λ m ν ^ 2)) ≤ 1
  short1 : ∀ t ∈ Set.Icc (min ta ((l₀ : ℝ) * ocTauPP α q Λ m))
      (max (ta + T) (((l₀ : ℝ) + P - 1) * ocTauPP α q Λ m)), ∀ y : Vec 2,
    T * ‖fderiv ℝ (streamVel (Φ (m - 1)) t) y‖ ≤ g
  short2 : ∀ t ∈ Set.Icc (min ta ((l₀ : ℝ) * ocTauPP α q Λ m))
      (max (ta + T) (((l₀ : ℝ) + P - 1) * ocTauPP α q Λ m)), ∀ y : Vec 2,
    T * ‖fderiv ℝ (fderiv ℝ (streamVel (Φ (m - 1)) t)) y‖ ≤ Cb * g / ocEpsilon q Λ (m - 1)
  comparable : T ≤ CT * ocTauPP α q Λ m ∧ ocTauPP α q Λ m ≤ CT * T
  window : ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ta ∧ ta < ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m ∧
    ((l₀ : ℝ) + P - 3 / 2) * ocTauPP α q Λ m < ta + T ∧
    ta + T ≤ ((l₀ : ℝ) + P - 1 / 2) * ocTauPP α q Λ m
  g_range : 0 ≤ g ∧ g ≤ g0
  metric_near : ∀ i : Fin P, ∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2),
    ∀ z (ξ : Vec 2),
    |∑ a', ∑ k, ξ a' * (ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t z -
          (1 : Matrix (Fin 2) (Fin 2) ℝ)) a' k * ξ k| ≤ g * ∑ a', ξ a' ^ 2
  metric_smooth : ∀ i : Fin P, ∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2),
    ∀ a' k : Fin 2, ContDiff ℝ qJ (fun z => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
      (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t z a' k)
  metric_jets : ∀ i : Fin P, ∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2),
    ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ qJ → ∀ a' k : Fin 2,
      ‖iteratedFDeriv ℝ j (fun z' => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t z' a' k) z‖ ≤
        CG j * g * (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) ^ j
  drift_pos : 0 ≤ a ∧ 1 ≤ B₀ ∧ 0 < lam
  drift_jets : ∀ i : Fin P, ∀ l : ℕ, 1 ≤ l → l ≤ Kmax →
    ∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2), ∀ z : Vec 2,
      ‖coefficientDerivativeArray (driftCoefficient (ocCellDrift α q Λ ζ m ν
          (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t)) l z‖ ≤
        a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)
  drift_scale : B₀ * (ρs / ocEpsilon q Λ m) / lam ≤ 1 / 2
  drift_small : a * B₀ * (ρs / ocEpsilon q Λ m) ^ 2 ≤ 1 / 8

end AVRegularity
end
end
