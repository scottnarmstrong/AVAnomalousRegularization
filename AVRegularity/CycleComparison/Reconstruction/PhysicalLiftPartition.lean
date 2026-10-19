-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.ReconForceBill
import AVRegularity.CycleComparison.Reconstruction.ReconForcePieces
import AVRegularity.CycleComparison.Reconstruction.Tested
public import AVRegularity.Statements.Intermediate.CycleOutput.CompReserveK
public import AVRegularity.CycleComparison.Reconstruction.ReconLiftSlices
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.CycleComparison.Reconstruction.ReconForceCarrier
import AVRegularity.CycleComparison.Reconstruction.ReconForceLimit
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.ChartTransport AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The physical reconstruction on a window**. On a reconstruction window
(`ReconWindow`) at the orders `ReconOrders`, the clamped glued lift `û` of the classical
representative solves the actual coupled equation with the residual presentation `(R, q)`
obtained as limits of the residuals of the Galerkin approximants (`ReconWindowAt.flux_limit`,
`ReconWindowAt.force_limit`, `ReconWindowAt.physical_weak_solution`), starts at the joint model
(`ReconWindowAt.physicalLift_start`), and its residual is bounded by `C 𝔅 M` whenever the coarse
energies are bounded by `M` and the bill `𝔅` dominates the five scale terms
(`ReconWindowAt.physical_lift`). The constant `C` (`reconBillConst`) depends only on the orders,
the lift constants, the grading constant and the coarse constants. -/

section
/-- **The orders of the physical reconstruction on a window**: `A_cl` cleanup orders, `K_max`
physical derivatives, the density order `m'`, the residual reserve `k_res`, the chart order `N_χ`
and the classical order `r₀` of the representative, below the lift orders `(K_lift, L_lift)` and
the coarse orders `(k_c, J_c, p_c)`. -/
structure ReconOrders (D Nc H Klift Llift kc Jc pc r₀ Kmax Acl m' kres Nχ : ℕ) : Prop where
  hD2 : 2 ≤ D
  hAcl : 1 ≤ Acl
  hK : Acl + 2 + Kmax ≤ Klift
  hrL : Kmax ≤ Llift
  hJL : Kmax + 2 ≤ Llift
  hDL : D ≤ Llift + 2
  hK2 : 2 * Acl + 2 + Kmax ≤ Klift + D + 2
  hord : Acl + 2 + Kmax + (2 * Nc + D) ≤ m' + 1
  hk : Acl + 2 + Kmax + Nc + 1 ≤ kres
  hNχ : m' + 1 ≤ Nχ
  hNχ' : kres + 1 ≤ Nχ
  hkres : kres ≤ kc
  hmr : m' + 1 ≤ r₀
  hrW : Nc + Kmax + 2 ≤ kc + 1 + (Nc + D)
  hNco : Nc + Kmax + 3 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)
  hordd : Nc + Kmax + (Nc + D) + 3 ≤ r₀
  hrK : r₀ + 2 ≤ kc + 1 + (Nc + D)

/-- **The orders of the physical reconstruction at the reserves of `cycle_comparison`**:
`A_cl = A_c`, the density order `m' = A_c + 1 + K_max + 2N_c + D`, the residual reserve
`k_res = A_c + 3 + K_max + N_c`, the chart order `N_χ = m' + 1`, the coarse order
`k_c = compReserveK` and the classical order `r₀ = k_c + (N_c + D) - 1`. -/
theorem reconOrders_of_reserves {D H Kmax Ac Nc Jc pc Mout Klift Llift : ℕ} (hD : 2 ≤ D)
    (hAc : 1 ≤ Ac) (hNc : 1 ≤ Nc)
    (hN : compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) ≤ Mout)
    (hK1 : max (Mout + Ac + Kmax + 2) (Ac + 2 + Kmax + D * (H + 1) * Nc) ≤ Klift)
    (hL1 : Kmax + D * (H + 1) * Nc + 1 ≤ Llift) :
    ReconOrders D Nc H Klift Llift (compReserveK Ac Nc D H Kmax) Jc pc
      (compReserveK Ac Nc D H Kmax + (Nc + D) - 1) Kmax Ac (Ac + 1 + Kmax + 2 * Nc + D)
      (Ac + 3 + Kmax + Nc) (Ac + 2 + Kmax + 2 * Nc + D) := by
  have hkc : compReserveK Ac Nc D H Kmax = 4 * (Nc + D) + 2 * Ac + 16 + Kmax + H * (D - 2) :=
    rfl
  have hX1 : 1 ≤ D * (H + 1) * Nc := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ D by omega) (show 1 ≤ H + 1 by omega)) hNc
    simpa using this
  have hXD : D ≤ D * (H + 1) * Nc := by
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_right D (Nat.mul_pos (by omega) (by omega))
  have hK1a := (le_max_left _ _).trans hK1
  have hK1b := (le_max_right _ _).trans hK1
  exact
    { hD2 := hD, hAcl := hAc, hK := (by omega), hrL := (by omega), hJL := (by omega),
      hDL := (by omega), hK2 := (by omega), hord := (by omega), hk := (by omega),
      hNχ := (by omega), hNχ' := (by omega), hkres := (by omega), hmr := (by omega),
      hrW := (by omega), hNco := (by omega), hordd := (by omega), hrK := (by omega) }

/-- **The constant of the residual bill** of the physical reconstruction: the flux part
(`r_bill_le`), the force part (`q_bill_le`) and the partition part `C_p`. -/
def reconBillConst (H Nc D Acl Kmax m' kres Nχ Klift Llift : ℕ) (CGl Cw : ℕ → ℝ)
    (Ca Sb Cg Cs Cy Cp : ℝ) : ℝ :=
  Real.sqrt (2 ^ (Kmax + 1) * 3 * (tailPhysConst H Nc D Acl Kmax m' (pulseChartD Nχ) *
      reconTailS Klift Llift D H Nc CGl Cw Ca Sb ^ 2 * Cs ^ 2 +
    ((Kmax.factorial : ℝ) ^ 2 + liftPhysConst H Nc Acl Kmax kres Nχ (pulseChartD Nχ) *
      reconLiftTheta Acl Kmax H Cg Sb ^ 2) * Cy ^ 2)) +
  Real.sqrt (2 * 2 ^ (Kmax + 1)) *
    (Real.sqrt (tailForceConst H Nc D Acl Kmax m' (pulseChartD Nχ)) *
        reconTailS Klift Llift D H Nc CGl Cw Ca Sb * Cs +
      Real.sqrt (liftForceConst H Nc Acl Kmax kres Nχ (pulseChartD Nχ)) *
        reconLiftTheta Acl Kmax H Cg Sb * Cy) + Cp

section Support

/-- The truncated gradient factorial norm is continuous on the jet space. -/
theorem continuous_gradFactorialNormSqUpTo {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] {μ : Measure (Vec 2)} {K : ℕ} (ρ : ℝ) (m : ℕ) :
    Continuous fun X : JetL2 μ K E => gradFactorialNormSqUpTo ρ m X := by
  unfold gradFactorialNormSqUpTo derivativeNormSq
  refine continuous_finsetSum _ fun j _ => ?_
  refine continuous_if_const _ (fun _ => continuous_const.mul ?_) fun _ => continuous_const
  exact continuous_finsetSum _ fun w _ => ((PiLp.continuous_apply 2 _ _).norm).pow 2

/-- A nonnegative a.e. strongly measurable function below an integrable one on a set is
integrable there. -/
theorem integrableOn_of_le_of_nonneg {I : Set ℝ} {f g : ℝ → ℝ} (hI : MeasurableSet I)
    (hg : IntegrableOn g I) (hf : AEStronglyMeasurable f (volume.restrict I))
    (h0 : ∀ s, 0 ≤ f s) (hle : ∀ s ∈ I, f s ≤ g s) : IntegrableOn f I :=
  Integrable.mono' hg hf ((ae_restrict_iff' hI).2 (Filter.Eventually.of_forall fun s hs => by
    rw [Real.norm_of_nonneg (h0 s)]
    exact hle s hs))

/-- A nonnegative a.e. strongly measurable function whose lower integral on a set is finite is
integrable there. -/
theorem integrableOn_of_lintegral_ofReal_lt_top {I : Set ℝ} {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict I)) (h0 : ∀ s, 0 ≤ f s)
    (hfin : ∫⁻ s in I, ENNReal.ofReal (f s) < ⊤) : IntegrableOn f I :=
  ⟨hf, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h0)).2 hfin⟩

/-- From the coarse-flux bound `B^{-1/2} (∫⁻_I M)^{1/2} ≤ Y`, the lower integral of `M` is
finite. -/
theorem lintegral_lt_top_of_coarse_bound {I : Set ℝ} {f : ℝ → ℝ} {B Y : ℝ} (hB : 0 < B)
    (h : ENNReal.ofReal (Real.sqrt B)⁻¹ * (∫⁻ s in I, ENNReal.ofReal (f s)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal Y) :
    ∫⁻ s in I, ENNReal.ofReal (f s) < ⊤ := by
  have hc : ENNReal.ofReal (Real.sqrt B)⁻¹ ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (inv_pos.2 (Real.sqrt_pos.2 hB))
  have h1 : (∫⁻ s in I, ENNReal.ofReal (f s)) ^ (1 / 2 : ℝ) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hc] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
  have h2 := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1
    (lt_top_iff_ne_top.2 h1)
  exact h2

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, CompleteSpace (E i)]

/-- **The Sobolev norm of a component is controlled by the mass-weighted norm** at a positive
radius: `‖U_v‖ ≤ 1 + (∑ π)(∑ w_min⁻¹) ‖U‖²_{ρ,K;π}`. -/
theorem norm_le_one_add_massNormSq (K : ι → ℕ) {ρ : ℝ} (hρ : 0 < ρ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (U : ∀ i, TorusHk (K i) (E i)) (v : ι) :
    ‖U v‖ ≤ 1 + (∑ i, π i) * (∑ i, (factorialWeightMin ρ (K i))⁻¹) *
      massNormSq ρ π (fun i => (U i).val) := by
  have hw : ∀ i, 0 < factorialWeightMin ρ (K i) := fun i => factorialWeightMin_pos ρ hρ
  have hmass : massNormSq ρ π (fun i => (U i).val) =
      ∑ i, (π i)⁻¹ * factorialNormSq ρ (U i).val := rfl
  have hterm : ∀ i, 0 ≤ (π i)⁻¹ * factorialNormSq ρ (U i).val := fun i =>
    mul_nonneg (inv_nonneg.2 (hπ i).le) (factorialNormSq_nonneg ρ (U i).val)
  have hM0 : 0 ≤ massNormSq ρ π (fun i => (U i).val) := by
    rw [hmass]
    exact Finset.sum_nonneg fun i _ => hterm i
  have h1 : factorialWeightMin ρ (K v) * ‖(U v).val‖ ^ 2 ≤ factorialNormSq ρ (U v).val :=
    factorialNormSq_lower ρ (U v).val
  have h2 : (π v)⁻¹ * factorialNormSq ρ (U v).val ≤ massNormSq ρ π (fun i => (U i).val) := by
    rw [hmass]
    exact Finset.single_le_sum (f := fun i => (π i)⁻¹ * factorialNormSq ρ (U i).val)
      (fun i _ => hterm i) (Finset.mem_univ v)
  have hnorm : ‖U v‖ = ‖(U v).val‖ := rfl
  have h3 : ‖(U v).val‖ ^ 2 ≤ (factorialWeightMin ρ (K v))⁻¹ * π v *
      massNormSq ρ π (fun i => (U i).val) := by
    have e1 : ‖(U v).val‖ ^ 2 = (factorialWeightMin ρ (K v))⁻¹ *
        (factorialWeightMin ρ (K v) * ‖(U v).val‖ ^ 2) := by
      rw [← mul_assoc, inv_mul_cancel₀ (hw v).ne', one_mul]
    have e2 : factorialNormSq ρ (U v).val = π v * ((π v)⁻¹ * factorialNormSq ρ (U v).val) := by
      rw [← mul_assoc, mul_inv_cancel₀ (hπ v).ne', one_mul]
    rw [e1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (hw v).le)
    calc factorialWeightMin ρ (K v) * ‖(U v).val‖ ^ 2 ≤ factorialNormSq ρ (U v).val := h1
      _ = π v * ((π v)⁻¹ * factorialNormSq ρ (U v).val) := e2
      _ ≤ π v * massNormSq ρ π (fun i => (U i).val) :=
          mul_le_mul_of_nonneg_left h2 (hπ v).le
  have hsw : (factorialWeightMin ρ (K v))⁻¹ ≤ ∑ i, (factorialWeightMin ρ (K i))⁻¹ :=
    Finset.single_le_sum (f := fun i => (factorialWeightMin ρ (K i))⁻¹)
      (fun i _ => inv_nonneg.2 (hw i).le) (Finset.mem_univ v)
  have hsπ : π v ≤ ∑ i, π i :=
    Finset.single_le_sum (f := π) (fun i _ => (hπ i).le) (Finset.mem_univ v)
  have h4 : ‖(U v).val‖ ^ 2 ≤ (∑ i, π i) * (∑ i, (factorialWeightMin ρ (K i))⁻¹) *
      massNormSq ρ π (fun i => (U i).val) := by
    refine h3.trans (mul_le_mul_of_nonneg_right ?_ hM0)
    rw [mul_comm (∑ i, π i)]
    exact mul_le_mul hsw hsπ (hπ v).le
      (Finset.sum_nonneg fun i _ => inv_nonneg.2 (hw i).le)
  have h5 : ‖(U v).val‖ ≤ 1 + ‖(U v).val‖ ^ 2 := by
    nlinarith [sq_nonneg (‖(U v).val‖ - 1), norm_nonneg (U v).val]
  rw [hnorm]
  linarith

end Support

/-- Integrability of a two-density bound. -/
theorem integrableOn_two_density {I : Set ℝ} {G Fm : ℝ → ℝ} (hG : IntegrableOn G I)
    (hF : IntegrableOn Fm I) (c k a b : ℝ) :
    IntegrableOn (fun s => c * (k * (a * G s + b * Fm s))) I :=
  (((hG.const_mul a).add (hF.const_mul b)).const_mul k).const_mul c

/-- Integrability of a merged density bound with two constants. -/
theorem integrableOn_sum_density_const {I : Set ℝ} (hI : volume I < ⊤) {G Fm : ℝ → ℝ}
    (hG : IntegrableOn G I) (hF : IntegrableOn Fm I) (c e₁ e₂ : ℝ) :
    IntegrableOn (fun s => 3 * (c * (G s + Fm s) + e₁ + e₂)) I :=
  ((((hG.add hF).const_mul c).add (integrableOn_const hI.ne)).add
    (integrableOn_const hI.ne)).const_mul 3

/-- Nonnegativity of a two-density bound. -/
theorem two_density_nonneg {G Fm : ℝ → ℝ} {c k a b : ℝ} (hc : 0 ≤ c) (hk : 0 ≤ k) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hG0 : ∀ s, 0 ≤ G s) (hF0 : ∀ s, 0 ≤ Fm s) :
    ∀ s, 0 ≤ c * (k * (a * G s + b * Fm s)) := fun s =>
  mul_nonneg hc (mul_nonneg hk (add_nonneg (mul_nonneg ha (hG0 s)) (mul_nonneg hb (hF0 s))))

section Window

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
  {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
  {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
  {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
  {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
  {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
  {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))}
  {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
  {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
  {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
  {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
  {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}

/-- **The physical reconstruction on a window.** The clamped glued lift `û` of the classical
representative solves the actual coupled equation with a residual presentation `(R, q)`, starts at
the joint model `X₀`, and its residual is at most `C 𝔅 M` (`C = reconBillConst`) in the residual
norm, in `ν⁻¹ ∫ ‖R‖²_{r_s}` (squared) and in `∫ ‖q‖_{r_s}`, provided: the strong energy of `W` at
order `m'` is at most `X ≤ C_s M`, the coarse flux `B^{-1/2}‖F_c‖_{L²}` at most `Y ≤ C_y M 𝔱`, the
partition terms of the approximants are bounded by `X_p` times their strong energy at order
`ord`, with `X_p E_b ≤ C_p 𝔅 M`, and the bill `𝔅` dominates `ε_c^{N_c}`, `√(B/ν) 𝔱`, `ε_c² 𝔱`,
`ε_c^{N_c} Z` and `ε_c² Z 𝔱`. -/
theorem ReconWindowAt.physical_lift
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Kmax Acl m' kres Nχ : ℕ}
    (o : ReconOrders D Nc H Klift Llift kc Jc pc r₀ Kmax Acl m' kres Nχ)
    (hKmax : ∀ v, K v ≤ Kmax) (hSb : 0 ≤ Sb) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ Nc →
      ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ Acl + 2 + Kmax →
        schurEnergyJet π (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp /
            ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2))
          Llift j (Cc k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ρ / ocEpsilon q Λ (m - 1)) ^ (n - m'' + j)))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m)
    (hrsρ : rs ≤ ρ)
    (hWc : ∀ v, ContinuousOn (W v) (Set.Icc tp (tp + Tobs)))
    (hFm : ∀ n r', Measurable fun s =>
      coarseModeCoeff n (fun v => Fc v (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s)) r')
    (hFcm : ∀ v, AEStronglyMeasurable (Fc v) (volume.restrict (Set.Icc tp (tp + Tobs))))
    {Vb : ℝ}
    (hbm : ∀ s ∈ Set.Ioc tp (tp + Tobs), ∀ k,
      AEStronglyMeasurable (fun x => streamVel (Φ m) s x k) (volume.restrict AVenhance.unitCube))
    (hVb : ∀ s ∈ Set.Ioc tp (tp + Tobs), ∀ x k, |streamVel (Φ m) s x k| ≤ Vb)
    {CA : ℝ} (hCA : 0 ≤ CA)
    (hAb : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v u d x, ‖(edgeCoefficient F ν (ocEpsilon q Λ m)
        (ocEpsilon q Λ (m - 1)) actual K) v u d s x‖ ≤ CA)
    (hAm : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v u d,
      AEStronglyMeasurable ((edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual
        K) v u d s) (volume.restrict AVenhance.unitCube))
    {X Y M tt bill Cs Cy Cpx : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hM : 0 ≤ M) (htt : 0 ≤ tt)
    (hCs : 0 ≤ Cs) (hCy : 0 ≤ Cy) (hCpx : 0 ≤ Cpx)
    {ord : ℕ} (hordE : ord + 1 ≤ kc + 1 + (Nc + D)) {Xp : ℝ} (hXp : 0 ≤ Xp)
    (hPB : ∀ n, ∫⁻ t in Set.Icc tp (tp + Tobs), (∑ j ∈ Finset.range (Kmax + 1),
        ∑ w' : DerivativeWord2 j, scalInt π (fun x => rs ^ j • orderedDerivative w' (fun x' =>
          ∑ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), deriv (F.weight (pp k)) t •
            pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ
              (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H
              (Cc k) (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (coarseTraj n W) t x') x)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal Xp * classicalStrongEnergy ρ B π
        (Set.Icc tp (tp + Tobs)) ord (coarseTraj n W))
    (hEn : strongEnergyUpTo ρ B π tp (tp + Tobs) ord W ≤
      ENNReal.ofReal X)
    (hX : strongEnergyUpTo ρ B π tp (tp + Tobs) m' W ≤
      ENNReal.ofReal X)
    (hY : ENNReal.ofReal (Real.sqrt B)⁻¹ * (∫⁻ s in Set.Icc tp (tp + Tobs), ENNReal.ofReal
        (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
          ρ π (fun v => (Fc v s).val))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal Y)
    (hXM : X ≤ Cs * M) (hYM : Y ≤ Cy * M * tt) (hPM : Xp ≤ Cpx * bill)
    (hb1 : (ocDStar q Λ m ν B / ρ) ^ Nc ≤ bill)
    (hb2 : Real.sqrt (B / ν) * tt ≤ bill)
    (hb3 : (ocDStar q Λ m ν B / ρ) ^ 2 * tt ≤ bill)
    (hb4 : (ocDStar q Λ m ν B / ρ) ^ Nc *
      (Real.sqrt Tobs / ocEll q Λ m ν *
        (ocEpsilon q Λ m / ρ) ^ Acl) ≤ bill)
    (hb5 : (ocDStar q Λ m ν B / ρ) ^ 2 *
      (Real.sqrt Tobs / ocEll q Λ m ν *
        (ocEpsilon q Λ m / ρ) ^ Acl) * tt ≤ bill)
    (Mv : ι → ℕ) (X0 : ∀ v, TorusHk (Mv v) (h v))
    (hNM : ∀ v, kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) ≤ Mv v) (hKM : ∀ v, K v ≤ Mv v)
    (hXst : ∀ v, truncateTorusHk (hNM v) (X0 v) = f0 v) :
    ∃ (û : ∀ v, ℝ → TorusHk (K v) (h v)) (ŵ : ∀ v, ℝ → TorusHk (K v + 1) (h v))
      (Rres : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
      (qres : ∀ v, ℝ → TorusHk (K v) (h v)),
      (∀ t ∈ Set.Icc tp (tp + Tobs), ∀ v,
        (û v t).toFunction.jet (valueIndex2 (K v)) =ᵐ[volume.restrict AVenhance.unitCube]
          fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
            (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m)
            (ocDStar q Λ m ν B / ρ) Nc H Cc
            (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
            (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
            aRep t x v) ∧
      IsCoupledWeakSolutionTorus ν tp (tp + Tobs) (streamVel (Φ m)) D K
        (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
        (fun v => û v tp) Rres qres û ŵ ∧
      residualNorm ν π (Set.Icc tp (tp + Tobs))
          (fun t x k v => ((Rres v t).toFunction.jet (valueIndex2 (K v)) x) k)
          (fun t x v => (qres v t).toFunction.jet (valueIndex2 (K v)) x) ≤
        ENNReal.ofReal (reconBillConst H Nc D Acl Kmax m' kres Nχ Klift Llift CGl Cw Ca Sb Cg
          Cs Cy (Cpx * Cs) * bill * M) ∧
      (∀ v, û v tp = truncateTorusHk (hKM v) (X0 v)) ∧
      (∀ v, MemLp (Rres v) 2 (volume.restrict (Set.Icc tp (tp + Tobs)))) ∧
      (∀ v, Integrable (qres v) (volume.restrict (Set.Icc tp (tp + Tobs)))) ∧
      ν⁻¹ * ∫ s in Set.Icc tp (tp + Tobs),
          massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) rs π
            (fun v => (Rres v s).val) ≤
        (reconBillConst H Nc D Acl Kmax m' kres Nχ Klift Llift CGl Cw Ca Sb Cg Cs Cy
          (Cpx * Cs) * bill * M) ^ 2 ∧
      ∫ s in Set.Icc tp (tp + Tobs),
          Real.sqrt (massNormSq (E := h) (K := K) rs π (fun v => (qres v s).val)) ≤
        reconBillConst H Nc D Acl Kmax m' kres Nχ Klift Llift CGl Cw Ca Sb Cg Cs Cy
          (Cpx * Cs) * bill * M := by
  have htAZ : tp ≤ tp + Tobs := by linarith [w.hTobs]
  have hI : MeasurableSet (Set.Icc tp (tp + Tobs)) := measurableSet_Icc
  have hIfin : volume (Set.Icc tp (tp + Tobs)) < ⊤ := measure_Icc_lt_top
  have hπ : ∀ v, 0 < π v := w.hcs.mass_pos
  have hB : 0 < B := w.hB
  have hν : 0 < ν := w.hν
  have hD1 : 1 ≤ D := by have := o.hD2; omega
  have hJK : Kmax + 2 ≤ Klift := by have := o.hK; have := o.hAcl; omega
  have hJr : Nc + (Kmax + 2) ≤ r₀ := by have := o.hordd; omega
  have hNco1 : Nc + Kmax + 1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) := by
    have := o.hNco; omega
  -- the scales
  have hρ : 0 < ρ := lt_of_lt_of_le hrs hrsρ
  have he0 : 0 < ocEpsilon q Λ m := lt_of_lt_of_le hrs hrse
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hℓ : 0 < ocEll q Λ m ν := div_pos he0 hsν
  have he : ocEpsilon q Λ m = ocEll q Λ m ν * Real.sqrt ν := by
    unfold ocEll
    rw [div_mul_cancel₀ _ hsν.ne']
  have hd : ocDStar q Λ m ν B = ocEll q Λ m ν * Real.sqrt B := by
    unfold ocDStar ocEll
    rw [Real.sqrt_div hB.le]
    ring
  have hbill : 0 ≤ bill :=
    (pow_nonneg (div_nonneg (by rw [hd]; exact mul_nonneg hℓ.le (Real.sqrt_nonneg B)) hρ.le)
      Nc).trans hb1
  -- the chains of the approximants
  obtain ⟨Vc, Vn, hch⟩ := w.exists_approxChains (Acl + 2 + Kmax) (Kmax + 1) Acl
    (Acl + 2 + Kmax) (max (Llift + 1) (Llift + 2)) (by omega) (by omega)
    (by have := o.hK2; omega) (by have := o.hrL; omega) (by omega)
    (le_trans (by omega) (le_max_left _ _)) (by have := o.hK2; omega)
    (by rw [max_eq_right (by omega)]; omega)
  -- the trajectory `W`
  obtain ⟨CW, hCW, hWB⟩ := exists_bound_of_continuousOn_family W hWc
  obtain ⟨δ, hδ0, hδ, hWδ⟩ := exists_galerkin_uniform htAZ W hWc
  have hcm : ∀ n r', Measurable fun s => coarseCoeff n W r'
      (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s) := fun n r' =>
    w.coarseCoeff_measurable n r'
  have haRm : Measurable fun q' : Set.Icc tp (tp + Tobs) × Vec 2 => aRep q'.1 q'.2 :=
    classicalRep_joint_measurable (r := r₀) (by have := o.hrK; omega) W hWc aRep w.hrep
  -- the commutator remainders
  have hE0 := w.defect_jets_tendsto (r := Kmax) o.hordd o.hrK o.hNco
  obtain ⟨CE', hCE', hEB⟩ := w.defect_jets_bound (r := Kmax) o.hordd o.hrK o.hNco hCW hWB
  -- the densities
  have hGc : ∀ v, ContinuousOn (fun s => gradFactorialNormSqUpTo
      ρ m' (W v s).val) (Set.Icc tp (tp + Tobs)) := fun v =>
    (continuous_gradFactorialNormSqUpTo _ m').comp_continuousOn
      (continuous_subtype_val.comp_continuousOn (hWc v))
  have hWint : IntegrableOn (fun s => ∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo
      ρ m' (W v s).val) (Set.Icc tp (tp + Tobs)) :=
    (continuousOn_finsetSum _ fun v _ => continuousOn_const.mul (hGc v)).integrableOn_compact
      isCompact_Icc
  have hFint : IntegrableOn (fun s => massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => kc) ρ π (fun v => (Fc v s).val))
      (Set.Icc tp (tp + Tobs)) :=
    integrableOn_of_lintegral_ofReal_lt_top
      (aestronglyMeasurable_massNormSq (fun _ => kc) _ π (fun s v => Fc v s) hFcm)
      (fun s => massNormSq_nonneg _ π hπ _) (lintegral_lt_top_of_coarse_bound hB hY)
  have hG0 : ∀ s, 0 ≤ ∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo
      ρ m' (W v s).val := fun s =>
    Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (gradFactorialNormSqUpTo_nonneg' _ m' _)
  have hF0 : ∀ s, 0 ≤ massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => kc) ρ π (fun v => (Fc v s).val) :=
    fun s => massNormSq_nonneg _ π hπ _
  have hIG : ∫ s in Set.Icc tp (tp + Tobs), ∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo
      ρ m' (W v s).val ≤ X ^ 2 / B :=
    integral_grad_le_of_strongEnergyUpTo_le hB hX0 hπ
      (fun v => (hGc v).aestronglyMeasurable hI) hX
  have hIF : ∫ s in Set.Icc tp (tp + Tobs), massNormSq
      (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
      ρ π (fun v => (Fc v s).val) ≤ B * Y ^ 2 :=
    integral_mass_le_of_coarse_bound hB hY0 hπ hFint hY
  -- the residual flux and force
  obtain ⟨Rr, -, hRm, hRb, hRL, cR, hcR, hcR0, hcRp, hRc⟩ :=
    w.flux_limit hSb o.hAcl o.hK o.hrL o.hord o.hk o.hNχ o.hNχ' hCg hgr Vc Vn hch o.hK2 hD1 hcm
      hFm o.hkres o.hmr hrs hrse hrsρ K hKmax hWint hFint
  obtain ⟨C₃, C₄, -, -, qq, hqlim, hqm, hqb, hqL, cq, hcq, hcq0, hcqp, hqc⟩ :=
    w.force_limit hSb o.hAcl o.hK o.hrL o.hord o.hk o.hNχ o.hNχ' hCg hgr Vc Vn hch o.hK2 hD1
      hcm hFm haRm o.hkres o.hmr o.hrW hNco1 hrs hrse K hKmax hWint hFint hE0 hCE' hCW hEB hWB
  have hmRi : IntegrableOn (fun s => massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
      (K := K) rs π (fun v => (Rr s v).val)) (Set.Icc tp (tp + Tobs)) :=
    integrableOn_of_le_of_nonneg hI (integrableOn_two_density hWint hFint _ _ _ _)
      (aestronglyMeasurable_massNormSq K rs π Rr hRm) (fun s => massNormSq_nonneg rs π hπ _) hRb
  have hmqi : IntegrableOn (fun s => massNormSq (E := h) (K := K) rs π
      (fun v => (qq s v).val)) (Set.Icc tp (tp + Tobs)) :=
    integrableOn_of_le_of_nonneg hI (integrableOn_sum_density_const hIfin hWint hFint _ _ _)
      (aestronglyMeasurable_massNormSq K rs π qq hqm) (fun s => massNormSq_nonneg rs π hπ _) hqb
  have hsqi : IntegrableOn (fun s => Real.sqrt (massNormSq (E := h) (K := K) rs π
      (fun v => (qq s v).val))) (Set.Icc tp (tp + Tobs)) :=
    integrableOn_sqrt_of_integrable hIfin (fun s => massNormSq_nonneg rs π hπ _) hmqi
  -- the coupled weak solution
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℝ, Cn = (∑ i, π i) * (∑ i, (factorialWeightMin rs (K i))⁻¹) :=
    ⟨_, rfl⟩
  have hCn0 : 0 ≤ Cn := by
    rw [hCn]
    exact mul_nonneg (Finset.sum_nonneg fun i _ => (hπ i).le)
      (Finset.sum_nonneg fun i _ => inv_nonneg.2 (factorialWeightMin_pos rs hrs).le)
  have hCRq : IntegrableOn (fun s => 1 + Cn * (massNormSq
      (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) rs π (fun v => (Rr s v).val) +
      massNormSq (E := h) (K := K) rs π (fun v => (qq s v).val))) (Set.Icc tp (tp + Tobs)) :=
    (integrableOn_const hIfin.ne).add ((hmRi.add hmqi).const_mul Cn)
  have hRq : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v, ‖Rr s v‖ ≤ 1 + Cn * (massNormSq
      (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) rs π (fun v => (Rr s v).val) +
      massNormSq (E := h) (K := K) rs π (fun v => (qq s v).val)) ∧
      ‖qq s v‖ ≤ 1 + Cn * (massNormSq
      (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) rs π (fun v => (Rr s v).val) +
      massNormSq (E := h) (K := K) rs π (fun v => (qq s v).val)) := fun s _ v => by
    have h1 := norm_le_one_add_massNormSq K hrs π hπ (Rr s) v
    have h2 := norm_le_one_add_massNormSq K hrs π hπ (qq s) v
    rw [← hCn] at h1 h2
    have hR0 := massNormSq_nonneg (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) rs π hπ
      (fun v => (Rr s v).val)
    have hq0 := massNormSq_nonneg (E := h) (K := K) rs π hπ (fun v => (qq s v).val)
    exact ⟨h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right hq0) hCn0)),
      h2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left hR0) hCn0))⟩
  have hWS := w.physical_weak_solution hKmax hJK o.hJL hJr o.hrK o.hDL o.hAcl (by omega)
    (by omega) (by have := o.hK; omega) (by have := o.hrL; omega) (by omega)
    (le_trans (by omega) (le_max_left _ _)) Vc Vn hch hbm hVb hCA hAb hAm hCW hWB δ hδ0 hδ hWδ
    (fun v s => Rr s v) (fun v s => qq s v) cR cq hcR hcR0 hcRp hcq hcq0 hcqp
    (fun n s hs v => ⟨(w.approxFlux_smooth o.hAcl o.hK o.hrL o.hord Vc Vn hch n hs K
        hKmax).1 v, (w.approxFlux_smooth o.hAcl o.hK o.hrL o.hord Vc Vn hch n hs K hKmax).2 v⟩)
    (fun n s hs v => ⟨(w.approxForce_smooth o.hAcl o.hK o.hrL o.hord hNco1 Vc Vn hch n hs K
        hKmax).1 v,
      (w.approxForce_smooth o.hAcl o.hK o.hrL o.hord hNco1 Vc Vn hch n hs K hKmax).2 v⟩)
    hRc hqc _ hCRq hRq
  -- the bill of the residual flux
  have hRint := integral_le_of_two_density (by positivity)
    (by exact mul_nonneg (tailPhysConst_nonneg _ _ _ _ _ _ _) (sq_nonneg _))
    (by exact add_nonneg (sq_nonneg _) (mul_nonneg (liftPhysConst_nonneg _ _ _ _ _ _ _)
      (by positivity)))
    hI hmRi hWint hFint hRb hIG hIF
  have hRbill := (mul_le_mul_of_nonneg_left hRint (inv_nonneg.2 hν.le)).trans
    (r_bill_le Kmax Nc hν hB hℓ hρ he hd (tailPhysConst_nonneg _ _ _ _ _ _ _)
      (liftPhysConst_nonneg _ _ _ _ _ _ _) hCs hCy hM hX0 hXM hY0 hYM htt le_rfl le_rfl hb1 hb2
      hb3)
  -- the bill of the residual force
  have hθ0 : 0 ≤ reconLiftTheta Acl Kmax H Cg Sb := by
    unfold reconLiftTheta
    positivity
  have hqbill := w.force_bill hSb o.hAcl o.hK o.hrL o.hord o.hk o.hNχ o.hNχ' hCg hgr Vc Vn hch
    o.hkres o.hmr hNco1 hrs hrse K hKmax qq hqlim hqm hE0 hcm hordE hXp hX0 hPB hEn
    (integrableOn_sqrt_of_integrable hIfin
      (two_density_nonneg (by positivity) (by norm_num)
        (by exact mul_nonneg (tailForceConst_nonneg _ _ _ _ _ _ _) (sq_nonneg _))
        (by exact mul_nonneg (liftForceConst_nonneg _ _ _ _ _ _ _) (by positivity)) hG0 hF0)
      (integrableOn_two_density hWint hFint _ _ _ _))
  have hPM' : Xp * X ≤ (Cpx * Cs) * bill * M :=
    (mul_le_mul hPM hXM hX0 (mul_nonneg hCpx hbill)).trans (le_of_eq (by ring))
  have hqint := hqbill.trans (add_le_add (integral_sqrt_two_density_le hI hIfin
    (by positivity) (by exact mul_nonneg (tailForceConst_nonneg _ _ _ _ _ _ _) (sq_nonneg _))
    (by exact mul_nonneg (liftForceConst_nonneg _ _ _ _ _ _ _) (by positivity)) hG0 hF0 hWint
    hFint hIG hIF) le_rfl)
  have hT : (volume (Set.Icc tp (tp + Tobs))).toReal = Tobs := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [w.hTobs])]
    ring
  rw [hT] at hqint
  have hqfin := hqint.trans (add_le_add (q_bill_le Nc Acl hν hB hℓ hρ he hd
    (reconTailS_nonneg _ _ _ _ _ _ _ _ _) hθ0 (tailForceConst_nonneg _ _ _ _ _ _ _)
    (liftForceConst_nonneg _ _ _ _ _ _ _) hCs hCy hM w.hTobs.le hX0 hXM hY0 hYM htt le_rfl
    le_rfl (div_nonneg (sq_nonneg X) hB.le) (mul_nonneg hB.le (sq_nonneg Y)) hb4 hb5 _
    (by positivity)) hPM')
  -- the constant
  obtain ⟨CR, hCR⟩ : ∃ CR : ℝ, CR = Real.sqrt (2 ^ (Kmax + 1) * 3 *
      (tailPhysConst H Nc D Acl Kmax m' (pulseChartD Nχ) *
        reconTailS Klift Llift D H Nc CGl Cw Ca Sb ^ 2 * Cs ^ 2 +
      ((Kmax.factorial : ℝ) ^ 2 + liftPhysConst H Nc Acl Kmax kres Nχ (pulseChartD Nχ) *
        reconLiftTheta Acl Kmax H Cg Sb ^ 2) * Cy ^ 2)) := ⟨_, rfl⟩
  obtain ⟨CQ, hCQ⟩ : ∃ CQ : ℝ, CQ = Real.sqrt (2 * 2 ^ (Kmax + 1)) *
      (Real.sqrt (tailForceConst H Nc D Acl Kmax m' (pulseChartD Nχ)) *
          reconTailS Klift Llift D H Nc CGl Cw Ca Sb * Cs +
        Real.sqrt (liftForceConst H Nc Acl Kmax kres Nχ (pulseChartD Nχ)) *
          reconLiftTheta Acl Kmax H Cg Sb * Cy) := ⟨_, rfl⟩
  have hconst : reconBillConst H Nc D Acl Kmax m' kres Nχ Klift Llift CGl Cw Ca Sb Cg Cs Cy
      (Cpx * Cs) = CR + CQ + (Cpx * Cs) := by
    rw [hCR, hCQ]
    rfl
  have hCR0 : 0 ≤ CR := hCR ▸ Real.sqrt_nonneg _
  have hCp : 0 ≤ (Cpx * Cs) := mul_nonneg hCpx hCs
  have hCQ0 : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (reconTailS_nonneg _ _ _ _ _ _ _ _ _)) hCs)
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hθ0) hCy))
  rw [← hCR] at hRbill
  rw [← hCQ] at hqfin
  have hbM : 0 ≤ bill * M := mul_nonneg hbill hM
  have hRle : CR * bill * M ≤ (CR + CQ + (Cpx * Cs)) * bill * M := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hbM
  have hRbill' : ν⁻¹ * ∫ s in Set.Icc tp (tp + Tobs),
      massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) rs π
        (fun v => (Rr s v).val) ≤ ((CR + CQ + (Cpx * Cs)) * bill * M) ^ 2 :=
    hRbill.trans (pow_le_pow_left₀ (mul_nonneg (mul_nonneg hCR0 hbill) hM) hRle 2)
  have hqle : CQ * bill * M + (Cpx * Cs) * bill * M ≤ (CR + CQ + (Cpx * Cs)) * bill * M := by
    have e : (CR + CQ + (Cpx * Cs)) * bill * M =
        CR * (bill * M) + (CQ * bill * M + (Cpx * Cs) * bill * M) := by
      ring
    rw [e]
    exact le_add_of_nonneg_left (mul_nonneg hCR0 hbM)
  have hqfin' : ∫ s in Set.Icc tp (tp + Tobs),
      Real.sqrt (massNormSq (E := h) (K := K) rs π (fun v => (qq s v).val)) ≤
        (CR + CQ + (Cpx * Cs)) * bill * M := hqfin.trans hqle
  -- the residual norm
  have hres := residualNorm_le_of_mass ν rs π hπ (Set.Icc tp (tp + Tobs))
    (fun v s => Rr s v) (fun v s => qq s v) hmRi hsqi
  have hsR : Real.sqrt (ν⁻¹ * ∫ s in Set.Icc tp (tp + Tobs),
      massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) rs π
        (fun v => (Rr s v).val)) ≤ CR * bill * M := by
    rw [← Real.sqrt_sq (mul_nonneg (mul_nonneg hCR0 hbill) hM)]
    exact Real.sqrt_le_sqrt hRbill
  have hres' : residualNorm ν π (Set.Icc tp (tp + Tobs))
      (fun t x k v => (((fun v s => Rr s v) v t).toFunction.jet (valueIndex2 (K v)) x) k)
      (fun t x v => ((fun v s => qq s v) v t).toFunction.jet (valueIndex2 (K v)) x) ≤
      ENNReal.ofReal ((CR + CQ + (Cpx * Cs)) * bill * M) := by
    refine hres.trans ?_
    have hsum : CR * bill * M + (CQ * bill * M + (Cpx * Cs) * bill * M) =
        (CR + CQ + (Cpx * Cs)) * bill * M := by
      ring
    rw [← hsum, ENNReal.ofReal_add (mul_nonneg (mul_nonneg hCR0 hbill) hM)
      (add_nonneg (mul_nonneg (mul_nonneg hCQ0 hbill) hM) (mul_nonneg (mul_nonneg hCp hbill) hM))]
    exact add_le_add (ENNReal.ofReal_le_ofReal hsR) (ENNReal.ofReal_le_ofReal hqfin)
  -- the clamped glued lift and the start
  have hsm := fun t => w.gluedRep_smooth hKmax hJK o.hJL hJr t
  have htp : tp ∈ Set.Icc tp (tp + Tobs) := ⟨le_rfl, htAZ⟩
  rw [hconst]
  refine ⟨fun v t => periodicHk (K v) (fun x => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B
      ρ tp (tp + Tobs) htAZ (fun k => F.weight (pp k)) Nc H Cc
      aRep t x v) (((hsm t).1 v).of_le (by exact_mod_cast Nat.le_add_right (K v) 2))
      ((hsm t).2 v),
    fun v t => periodicHk (K v + 1) (fun x => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B
      ρ tp (tp + Tobs) htAZ (fun k => F.weight (pp k)) Nc H Cc
      aRep t x v) (((hsm t).1 v).of_le (by exact_mod_cast Nat.le_succ (K v + 1)))
      ((hsm t).2 v),
    fun v s => Rr s v, fun v s => qq s v, ?_, hWS, hres', ?_, hRL, fun v => (hqL v).integrable
      (by norm_num), hRbill', hqfin'⟩
  · intro t ht v
    filter_upwards [periodicHk_value_ae (K v) _ (((hsm t).1 v).of_le
      (by exact_mod_cast Nat.le_add_right (K v) 2)) ((hsm t).2 v)] with x hx
    exact hx.trans (congrFun (obsGluedClamped_of_mem _ _ _ _ _ _ _ _ _ _ _ htAZ _ _ _ _ _ ht x) v)
  · intro v
    have hfun : (fun x => obsGluedClamped α q Λ m (Φ (m - 1)) hφ ν B
        ρ tp (tp + Tobs) htAZ (fun k => F.weight (pp k)) Nc H Cc
        aRep tp x v) = fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs))
          (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ
          (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          aRep tp x v :=
      funext fun x => congrFun (obsGluedClamped_of_mem _ _ _ _ _ _ _ _ _ _ _ htAZ _ _ _ _ _ htp x) v
    have hU : ContDiff ℝ (K v : ℕ∞) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs))
        (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ
        (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
        (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
        aRep tp x v) := by
      rw [← hfun]
      exact ((hsm tp).1 v).of_le (by exact_mod_cast Nat.le_add_right (K v) 2)
    have hp : AVenhance.IsZ2Periodic (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs))
        (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ
        (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
        (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
        aRep tp x v) := by
      rw [← hfun]
      exact (hsm tp).2 v
    rw [← w.physicalLift_start hD1 (ocDStar q Λ m ν B / ρ) v hU hp
      (hNM v) (hKM v) (X0 v) (hXst v)]
    exact periodicHk_congr (K v) hfun _ _ _ _

end Window
end

/-! **The physical reconstruction on a window at a free lift length: the statement** (statement only).

`ReconPhysicalLiftStatement` is the statement of `ReconWindowAt.physical_lift`
(`PhysicalLiftWindow.lean`) with the window `ReconWindowAt … ρ ρc Jm …` in place of the cascade
window, and the lift length `ρ` in place of `√(Bτ_m'')` in every hypothesis and in the conclusion
(the grading `hgr`, `hrsρ`, the partition terms `hPB`, the energies `hEn`, `hX`, the coarse flux
`hY`, the bill terms `hb1`, `hb3`, `hb4`, `hb5`, and the glued lift of the conclusion). The
radius `ρc` and the matrix `Jm` occur in the window only.

The theorem `ReconWindowAt.physical_lift` is stated for `ReconWindowAt`, of which this statement is
the instance at the universe of the weak stages. At `ρ = ρc = √(Bτ_m'')`, `Jm = ocRefFlux` it is the
present theorem. The weak passage uses it at `ρ = ε_{m-1}`, `ρc = c ε_{m-1}`, `Jm = κ_M I`.

At the cascade parameters the statement is `ReconWindowAt.physical_lift` word for
word; no hypothesis asks `ρ/ε_{m-1}` to be small, so `ρ = ε_{m-1}` is admissible; the constant
`reconBillConst` does not read `ρ`, `ρc` or `Jm`. -/

section
/-- **The physical reconstruction on a window, at a lift length `ρ`** (statement). -/
def ReconPhysicalLiftStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {h : ι → Type}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {P' : Type} {Ctx : P' → Type}
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
    {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {D : ℕ}
    {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
    {pp : ℤ → P'} {π : ι → ℝ} {Cpart : ℝ} {H Nc Klift Llift qs qf : ℕ}
    {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
    {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
    {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
    {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
    {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
    {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ}
    (_w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift
      Llift qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep
      r₀)
    {Kmax Acl m' kres Nχ : ℕ}
    (o : ReconOrders D Nc H Klift Llift kc Jc pc r₀ Kmax Acl m' kres Nχ)
    (hKmax : ∀ v, K v ≤ Kmax) (hSb : 0 ≤ Sb) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ Nc →
      ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ Acl + 2 + Kmax →
        schurEnergyJet π (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp /
            ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2))
          Llift j (Cc k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ρ / ocEpsilon q Λ (m - 1)) ^ (n - m'' + j)))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m)
    (hrsρ : rs ≤ ρ)
    (hWc : ∀ v, ContinuousOn (W v) (Set.Icc tp (tp + Tobs)))
    (hFm : ∀ n r', Measurable fun s =>
      coarseModeCoeff n (fun v => Fc v (Set.projIcc tp (tp + Tobs) (by linarith [_w.hTobs]) s)) r')
    (hFcm : ∀ v, AEStronglyMeasurable (Fc v) (volume.restrict (Set.Icc tp (tp + Tobs))))
    {Vb : ℝ}
    (hbm : ∀ s ∈ Set.Ioc tp (tp + Tobs), ∀ k,
      AEStronglyMeasurable (fun x => streamVel (Φ m) s x k) (volume.restrict AVenhance.unitCube))
    (hVb : ∀ s ∈ Set.Ioc tp (tp + Tobs), ∀ x k, |streamVel (Φ m) s x k| ≤ Vb)
    {CA : ℝ} (hCA : 0 ≤ CA)
    (hAb : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v u d x, ‖(edgeCoefficient F ν (ocEpsilon q Λ m)
        (ocEpsilon q Λ (m - 1)) actual K) v u d s x‖ ≤ CA)
    (hAm : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v u d,
      AEStronglyMeasurable ((edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual
        K) v u d s) (volume.restrict AVenhance.unitCube))
    {X Y M tt bill Cs Cy Cpx : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hM : 0 ≤ M) (htt : 0 ≤ tt)
    (hCs : 0 ≤ Cs) (hCy : 0 ≤ Cy) (hCpx : 0 ≤ Cpx)
    {ord : ℕ} (hordE : ord + 1 ≤ kc + 1 + (Nc + D)) {Xp : ℝ} (hXp : 0 ≤ Xp)
    (hPB : ∀ n, ∫⁻ t in Set.Icc tp (tp + Tobs), (∑ j ∈ Finset.range (Kmax + 1),
        ∑ w' : DerivativeWord2 j, scalInt π (fun x => rs ^ j • orderedDerivative w' (fun x' =>
          ∑ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), deriv (F.weight (pp k)) t •
            pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ
              (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H
              (Cc k) (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (coarseTraj n W) t x') x)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal Xp * classicalStrongEnergy ρ B π
        (Set.Icc tp (tp + Tobs)) ord (coarseTraj n W))
    (hEn : strongEnergyUpTo ρ B π tp (tp + Tobs) ord W ≤
      ENNReal.ofReal X)
    (hX : strongEnergyUpTo ρ B π tp (tp + Tobs) m' W ≤
      ENNReal.ofReal X)
    (hY : ENNReal.ofReal (Real.sqrt B)⁻¹ * (∫⁻ s in Set.Icc tp (tp + Tobs), ENNReal.ofReal
        (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
          ρ π (fun v => (Fc v s).val))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal Y)
    (hXM : X ≤ Cs * M) (hYM : Y ≤ Cy * M * tt) (hPM : Xp ≤ Cpx * bill)
    (hb1 : (ocDStar q Λ m ν B / ρ) ^ Nc ≤ bill)
    (hb2 : Real.sqrt (B / ν) * tt ≤ bill)
    (hb3 : (ocDStar q Λ m ν B / ρ) ^ 2 * tt ≤ bill)
    (hb4 : (ocDStar q Λ m ν B / ρ) ^ Nc *
      (Real.sqrt Tobs / ocEll q Λ m ν *
        (ocEpsilon q Λ m / ρ) ^ Acl) ≤ bill)
    (hb5 : (ocDStar q Λ m ν B / ρ) ^ 2 *
      (Real.sqrt Tobs / ocEll q Λ m ν *
        (ocEpsilon q Λ m / ρ) ^ Acl) * tt ≤ bill)
    (Mv : ι → ℕ) (X0 : ∀ v, TorusHk (Mv v) (h v))
    (hNM : ∀ v, kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) ≤ Mv v) (hKM : ∀ v, K v ≤ Mv v)
    (hXst : ∀ v, truncateTorusHk (hNM v) (X0 v) = f0 v),

    ∃ (û : ∀ v, ℝ → TorusHk (K v) (h v)) (ŵ : ∀ v, ℝ → TorusHk (K v + 1) (h v))
      (Rres : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
      (qres : ∀ v, ℝ → TorusHk (K v) (h v)),
      (∀ t ∈ Set.Icc tp (tp + Tobs), ∀ v,
        (û v t).toFunction.jet (valueIndex2 (K v)) =ᵐ[volume.restrict AVenhance.unitCube]
          fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
            (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m)
            (ocDStar q Λ m ν B / ρ) Nc H Cc
            (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
            (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
            aRep t x v) ∧
      IsCoupledWeakSolutionTorus ν tp (tp + Tobs) (streamVel (Φ m)) D K
        (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
        (fun v => û v tp) Rres qres û ŵ ∧
      residualNorm ν π (Set.Icc tp (tp + Tobs))
          (fun t x k v => ((Rres v t).toFunction.jet (valueIndex2 (K v)) x) k)
          (fun t x v => (qres v t).toFunction.jet (valueIndex2 (K v)) x) ≤
        ENNReal.ofReal (reconBillConst H Nc D Acl Kmax m' kres Nχ Klift Llift CGl Cw Ca Sb Cg
          Cs Cy (Cpx * Cs) * bill * M) ∧
      (∀ v, û v tp = truncateTorusHk (hKM v) (X0 v)) ∧
      (∀ v, MemLp (Rres v) 2 (volume.restrict (Set.Icc tp (tp + Tobs)))) ∧
      (∀ v, Integrable (qres v) (volume.restrict (Set.Icc tp (tp + Tobs)))) ∧
      ν⁻¹ * ∫ s in Set.Icc tp (tp + Tobs),
          massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) rs π
            (fun v => (Rres v s).val) ≤
        (reconBillConst H Nc D Acl Kmax m' kres Nχ Klift Llift CGl Cw Ca Sb Cg Cs Cy
          (Cpx * Cs) * bill * M) ^ 2 ∧
      ∫ s in Set.Icc tp (tp + Tobs),
          Real.sqrt (massNormSq (E := h) (K := K) rs π (fun v => (qres v s).val)) ≤
        reconBillConst H Nc D Acl Kmax m' kres Nχ Klift Llift CGl Cw Ca Sb Cg Cs Cy
          (Cpx * Cs) * bill * M

/-- **The physical reconstruction on a window at a free lift length** (the end of the
generalization of `CycleComparison/Reconstruction/`): `ReconWindowAt.physical_lift` at the
universe of the weak stages. -/
theorem reconPhysicalLift : ReconPhysicalLiftStatement :=
  fun w => ReconWindowAt.physical_lift w
end

end AVRegularity.CycleComparison.Reconstruction
end
end

section
/-! **The partition terms of the approximants on a reconstruction window**. With the lift settings of the observed pulses at the raised
orders `(A_cl + 2 + K_max, 2 + K_max, K_max) + D(H+1)N_c` (the partition orders of
`partition_term_bound` at `(k_l, L_l, r) = (2, 0, K_max)`), the quiet entrance traces at the gap
starts are bounded by the lift grading, `I_b = C_I Θ^b` (`setting_quietEntranceTrace`, at one
fast order below the lift sequence, which the lift floor `K_max + D(H+1)N_c + 1 ≤ L_lift`
provides), the label source slices are measurable (`ReconWindowAt.labelSrc_slice_aemeasurable`),
and the partition terms of every approximant `a_n` are bounded by
`C (1+Θ)^H #pulses ℓ τ^{-1/2} e^{-cτ/ℓ²}` times the strong energy of `a_n` at the order
`4(N_c + D) + 2A_cl + 16 + K_max` (`partition_window_input`). The factor `#pulses` is absorbed
into the partition term `ℓ√(#pulses/τ) e^{-(c/2)τ/ℓ²}` of the bill: by the scale laws
`#pulses · e^{-cτ/ℓ²}` is bounded by a constant (`card_exp_le_of_scaleLaws`), so
`#pulses · ℓ√(1/τ) e^{-cτ/ℓ²} ≤ √K ℓ√(#pulses/τ) e^{-(c/2)τ/ℓ²}` (`card_exp_absorb`). -/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.ChartTransport
open scoped ENNReal

universe u v w z

namespace AVRegularity.CycleComparison.Reconstruction

/-- The graded traces `I_b = C_I Θ^b` sum to at most `(H+1)² C_I (1+Θ)^H`. -/
theorem trace_sum_le {Θ CI : ℝ} (hΘ : 0 ≤ Θ) (hCI : 0 ≤ CI) (H : ℕ) :
    ∑ hh ∈ Finset.range (H + 1), ∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * (CI * Θ ^ b) ≤
      ((H + 1 : ℕ) : ℝ) ^ 2 * CI * (1 + Θ) ^ H := by
  have hterm : ∀ hh ∈ Finset.range (H + 1), ∀ b ∈ Finset.range (hh + 1),
      Θ ^ (hh - b) * (CI * Θ ^ b) ≤ CI * (1 + Θ) ^ H := by
    intro hh hhH b hb
    have hbh : b ≤ hh := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
    have hhH' : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhH)
    have e : Θ ^ (hh - b) * (CI * Θ ^ b) = CI * Θ ^ hh := by
      rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel hbh]
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hCI
    calc Θ ^ hh ≤ (1 + Θ) ^ hh := pow_le_pow_left₀ hΘ (by linarith) hh
      _ ≤ (1 + Θ) ^ H := pow_le_pow_right₀ (by linarith) hhH'
  have hc0 : 0 ≤ CI * (1 + Θ) ^ H := mul_nonneg hCI (pow_nonneg (by linarith) H)
  calc ∑ hh ∈ Finset.range (H + 1), ∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * (CI * Θ ^ b)
      ≤ ∑ hh ∈ Finset.range (H + 1), ∑ _b ∈ Finset.range (hh + 1), CI * (1 + Θ) ^ H :=
        Finset.sum_le_sum fun hh hhH => Finset.sum_le_sum fun b hb => hterm hh hhH b hb
    _ ≤ ∑ _hh ∈ Finset.range (H + 1), ((H + 1 : ℕ) : ℝ) * (CI * (1 + Θ) ^ H) := by
        refine Finset.sum_le_sum fun hh hhH => ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hhH' : hh + 1 ≤ H + 1 := Finset.mem_range.1 hhH
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hhH') hc0
    _ = ((H + 1 : ℕ) : ℝ) ^ 2 * CI * (1 + Θ) ^ H := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- **The partition terms of the approximants on a reconstruction window.** For orders with
`1 ≤ A_cl`, there are constants `C, c > 0` such that on every reconstruction window whose lift
sequences are stored at the lift orders `K_lift ≥ A_cl + 2 + K_max + D(H+1)N_c` and
`L_lift ≥ K_max + D(H+1)N_c + 1`, given lift settings of the observed pulses at the partition
orders and `ε_m ≤ ρ`, the `L¹_t` norms of the weighted word derivatives of order `≤ K_max` of the
partition terms of every approximant `a_n` are at most
`C (1 + Θ)^H #pulses ℓ √(1/τ) e^{-cτ/ℓ²}` times the strong energy of `a_n` of order
`4(N_c + D) + 2A_cl + 16 + K_max`. -/
theorem partition_window_input (Acl Nc D H Kmax Klift Llift : ℕ) (CGl Cw : ℕ → ℝ)
    (Ca Cpart : ℝ) (hAcl : 1 ≤ Acl) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
      [∀ i, CompleteSpace (h i)] {P' : Type w} {Ctx : P' → Type z}
      {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ}
      {hφ : IsAdmissibleStream (Φ (m - 1))} {ν B tp Tobs ρs ρ ρc : ℝ}
      {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
      {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p} {K : ι → ℕ} {T : F.Atlas}
      {pp : ℤ → P'} {π : ι → ℝ} {qs qf : ℕ}
      {Cc : ℤ → ℕ → ℕ → LiftCoeff ι h} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
      {bM : ι → ι → ℝ} {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
      {AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
        PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
      {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
        (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
          (PiLp 2 (fun _ : Fin 2 => h v))}
      {Aedge : Matrix ι ι ℝ} {Cstar Θc : ℝ}
      {f0 : ∀ v, TorusHk (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v)}
      {W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v)}
      {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
      {aRep : ℝ → Vec 2 → ∀ i, h i} {r₀ : ℕ},
      ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
        qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀ →
      ∀ (parP : ℤ → Fin 2) (VP : ℤ → ℝ → ℝ → ℝ) (qsP qfP : ℕ),
      (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
        IsLiftSetting (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
            ρ
            (ρ / ocEpsilon q Λ (m - 1)) k
            (F.fiber (pp k) (actual (pp k)))) π
          (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2)
          (ocEpsilon q Λ m) ν B ρ (ocEpsilon q Λ (m - 1))
          (ocEll q Λ m ν) (ocDStar q Λ m ν B)
          (ocDStar q Λ m ν B / ρ)
          (ρ / ocEpsilon q Λ (m - 1))
          (parP k) (VP k) H Nc (Acl + 2 + Kmax + D * (H + 1) * Nc)
          (2 + Kmax + D * (H + 1) * Nc) (0 + Kmax + D * (H + 1) * Nc) qsP qfP CGl Cw
          (fun _ _ => Ca) bM Sb) →
      Acl + 2 + Kmax + D * (H + 1) * Nc ≤ Klift → Kmax + D * (H + 1) * Nc + 1 ≤ Llift →
      0 ≤ Sb → ocEpsilon q Λ m ≤ ρ →
      ∀ rs : ℝ, 0 < rs → rs ≤ ocEpsilon q Λ m → ∀ n,
      ∫⁻ t in Set.Icc tp (tp + Tobs), (∑ j ∈ Finset.range (Kmax + 1),
          ∑ w' : DerivativeWord2 j, scalInt π (fun x => rs ^ j • orderedDerivative w' (fun x' =>
            ∑ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), deriv (F.weight (pp k)) t •
              pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ
                (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H
                (Cc k) (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                (coarseTraj n W) t x') x)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * (1 + Sb) ^ H * ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) *
          ocEll q Λ m ν * Real.sqrt (1 / ocTau α q Λ m) *
          Real.exp (-(c * ocTau α q Λ m / ocEll q Λ m ν ^ 2))) *
        classicalStrongEnergy ρ B π (Set.Icc tp (tp + Tobs))
          (4 * (Nc + D) + 2 * Acl + 16 + Kmax) (coarseTraj n W) := by
  obtain ⟨C, c, hC, hc, hPT⟩ := partition_term_bound.{u, v, w, z} Acl Nc D H 2 0 Kmax CGl Cw
    (fun _ _ => Ca) Cpart hAcl
  obtain ⟨CI, hCI, hTr⟩ := setting_quietEntranceTrace.{u, v} Nc
    (Acl + 2 + Kmax + D * (H + 1) * Nc) (2 + Kmax + D * (H + 1) * Nc)
    (0 + Kmax + D * (H + 1) * Nc) D H CGl Cw (fun _ _ => Ca)
  refine ⟨C * (((H + 1 : ℕ) : ℝ) ^ 2 * CI), c,
    mul_nonneg hC (mul_nonneg (sq_nonneg _) hCI), hc, ?_⟩
  intro ι _ _ h _ _ _ _ _ _ P' Ctx α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π qs qf
    Cc
    par V bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀ wd parP VP qsP qfP
    hsetP hKl hLl hSb heρ rs hrs hrse n
  have hΛ1 : 1 ≤ Λ := by have := wd.hΛ; omega
  have hτ : 0 < ocTau α q Λ m := AVRegularity.Construction.Stream.ocTau_pos hΛ1
  have he0 : 0 < ocEpsilon q Λ m := lt_of_lt_of_le hrs hrse
  have hℓ : 0 < ocEll q Λ m ν := div_pos he0 (Real.sqrt_pos.2 wd.hν)
  have hℓ2 : 0 < ocEll q Λ m ν ^ 2 := pow_pos hℓ 2
  -- the lift sequences at the partition orders
  have hseqP : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
      IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
          ρ
          (ρ / ocEpsilon q Λ (m - 1)) k
          (F.fiber (pp k) (actual (pp k))))
        (Acl + 2 + Kmax + D * (H + 1) * Nc + D + 2)
        (max (2 + Kmax + D * (H + 1) * Nc + 1) (0 + Kmax + D * (H + 1) * Nc + 2))
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) Nc H
        (Cc k) := fun k hk =>
    isLiftSequence_mono (wd.hseq k hk) (by omega)
      (max_le (le_max_of_le_right (by omega)) (le_max_of_le_right (by omega)))
  -- the quiet entrance traces
  have htrace : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
      tp ≤ ((k : ℝ) + 17 / 24) * ocTau α q Λ m →
      ((k : ℝ) + 35 / 48) * ocTau α q Λ m ≤ tp + Tobs →
      HasQuietEntranceTrace π (Cc k) (((k : ℝ) + 17 / 24) * ocTau α q Λ m / ocEll q Λ m ν ^ 2)
        (ρ / ocEpsilon q Λ (m - 1)) Nc H
        (Acl + 2 + Kmax + D * (H + 1) * Nc)
        (max (2 + Kmax) (0 + Kmax + 2) + D * (H + 1) * Nc) (fun b => CI * Sb ^ b) := by
    intro k hk h1 h2
    have hs : ((k : ℝ) + 17 / 24) * ocTau α q Λ m / ocEll q Λ m ν ^ 2 ∈
        Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) := by
      constructor
      · refine div_le_div_of_nonneg_right (max_le ?_ h1) hℓ2.le
        exact mul_le_mul_of_nonneg_right (by linarith) hτ.le
      · refine div_le_div_of_nonneg_right (le_min ?_ ?_) hℓ2.le
        · exact mul_le_mul_of_nonneg_right (by linarith) hτ.le
        · exact (mul_le_mul_of_nonneg_right (by linarith) hτ.le).trans h2
    exact hTr _ π _ _ _ _ _ _ _ _ _ _ _ (parP k) (VP k) qsP qfP bM Sb (hsetP k hk) hSb (Cc k)
      (hseqP k hk) _ hs _ _ le_rfl
      ((Nat.add_le_add_right (max_le le_rfl (by omega)) _).trans (le_max_left _ _))
  -- the partition bound
  have hPB := hPT α s q Λ m ζ Φ wd.hα₀ wd.hα₁ wd.hs₀ wd.hs₁ wd.hq wd.hζ wd.hΛ wd.hΦ wd.hm hφ ν B
    ρ (ocEpsilon q Λ (m - 1)) rs tp (tp + Tobs) hrs hrse heρ
    wd.hRE F actual wd.htorus pp (fun k hk => (wd.hpp k hk).2.2) wd.hquiet
    (fun k => F.weight (pp k)) (ocQuietTimes α q Λ ζ m) wd.hpart π parP VP qsP qfP bM Sb hsetP
    Cc hseqP (fun b => CI * Sb ^ b) hSb (fun b => mul_nonneg hCI (pow_nonneg hSb b)) htrace
    (coarseTraj n W)
    (fun t => (coarseTraj_contDiff n W t)) (fun t => coarseTraj_periodic n W t)
    (fun k hk hh hhH j hj w' => wd.labelSrc_slice_aemeasurable n
      (fun r' => wd.coarseCoeff_measurable n r') hk hhH (by omega) (by omega) w' rs)
  refine hPB.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hS2 := trace_sum_le hSb hCI H
  have hrest : 0 ≤ ocEll q Λ m ν * Real.sqrt (1 / ocTau α q Λ m) *
      Real.exp (-(c * ocTau α q Λ m / ocEll q Λ m ν ^ 2)) :=
    mul_nonneg (mul_nonneg hℓ.le (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  have hCc : 0 ≤ C * ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) :=
    mul_nonneg hC (Nat.cast_nonneg _)
  calc C * ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) *
        (∑ hh ∈ Finset.range (H + 1), ∑ b ∈ Finset.range (hh + 1), Sb ^ (hh - b) * (CI * Sb ^ b)) *
        ocEll q Λ m ν * Real.sqrt (1 / ocTau α q Λ m) *
        Real.exp (-(c * ocTau α q Λ m / ocEll q Λ m ν ^ 2))
      = C * ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) *
        (∑ hh ∈ Finset.range (H + 1), ∑ b ∈ Finset.range (hh + 1), Sb ^ (hh - b) * (CI * Sb ^ b)) *
        (ocEll q Λ m ν * Real.sqrt (1 / ocTau α q Λ m) *
          Real.exp (-(c * ocTau α q Λ m / ocEll q Λ m ν ^ 2))) := by ring
    _ ≤ C * ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) *
        (((H + 1 : ℕ) : ℝ) ^ 2 * CI * (1 + Sb) ^ H) *
        (ocEll q Λ m ν * Real.sqrt (1 / ocTau α q Λ m) *
          Real.exp (-(c * ocTau α q Λ m / ocEll q Λ m ν ^ 2))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS2 hCc) hrest
    _ = C * (((H + 1 : ℕ) : ℝ) ^ 2 * CI) * (1 + Sb) ^ H *
        ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) * ocEll q Λ m ν *
        Real.sqrt (1 / ocTau α q Λ m) * Real.exp (-(c * ocTau α q Λ m / ocEll q Λ m ν ^ 2)) := by
        ring

/-- **The pulse count is absorbed by the quiet exponential.** After the scale laws at a fixed
`Λ` and a window of algebraic length `T_obs ≤ C_obs E^{-A_obs}`, for every rate `c > 0` the
count of observed pulses times `e^{-cτ/ℓ²}` is bounded by one constant. -/
theorem card_exp_le_of_scaleLaws (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (Aobs Cobs c : ℝ) (hc : 0 < c) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (m : ℕ) (ν B : ℝ), Assembly.IsScaleLaws α q Λ m ν B C₀ →
      ∀ tp Tobs : ℝ, 0 < Tobs → Tobs ≤ Cobs * ocEpsilon q Λ (m - 1) ^ (-Aobs) →
        ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) *
          Real.exp (-(c * ocTau α q Λ m / ocEll q Λ m ν ^ 2)) ≤ Kc := by
  have hexp := AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hδ : 0 < ocDelta α q := hexp.2.1
  have hb₁ : 0 ≤ 2 - (1 + α) + 4 * ocDelta α q := by linarith
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  have ha : 0 ≤ max Aobs 0 := le_max_right Aobs 0
  have hT₀ : 0 ≤ max Cobs 0 := le_max_right Cobs 0
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      n = ⌈(max Aobs 0 + (2 - (1 + α) + 4 * ocDelta α q)) / (4 * ocDelta α q)⌉₊ := ⟨_, rfl⟩
  have hn' : max Aobs 0 + (2 - (1 + α) + 4 * ocDelta α q) ≤ 4 * ocDelta α q * (n : ℝ) := by
    rw [hn]
    exact Assembly.le_mul_ceil_div (by linarith)
  have hK : 0 ≤ C₀ ^ n * (n.factorial : ℝ) / c ^ n :=
    div_nonneg (mul_nonneg (pow_nonneg hC₀pos.le n) (Nat.cast_nonneg _)) (pow_nonneg hc.le n)
  have h5 : 0 ≤ 5 * (1 + max Cobs 0 * C₀) := by
    have := mul_nonneg hT₀ hC₀pos.le
    linarith
  refine ⟨5 * (1 + max Cobs 0 * C₀) * (C₀ ^ n * (n.factorial : ℝ) / c ^ n), mul_nonneg h5 hK, ?_⟩
  intro m ν B hL tp Tobs hT hTle
  have hE : 0 < ocEpsilon q Λ (m - 1) :=
    (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 hΛ).1
  have hE1 : ocEpsilon q Λ (m - 1) ≤ 1 :=
    (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 hΛ).2.1
  have hΛ1 : 1 ≤ Λ := by omega
  have hτ : 0 < ocTau α q Λ m := AVRegularity.Construction.Stream.ocTau_pos hΛ1
  have hcount := Assembly.pulseCount_le_powerLaw hE hE1 ha hb₁ hT.le
    (Assembly.window_le hE hE1 hTle) hτ hL.tau_inv_le
    (Assembly.obsPulses_card_le α q hΛ1 m tp hT.le)
  have hy : 0 ≤ c * ocTau α q Λ m / ocEll q Λ m ν ^ 2 :=
    div_nonneg (mul_nonneg hc.le hτ.le) (sq_nonneg _)
  have hq1 : ocEpsilon q Λ (m - 1) ^ (-(4 * ocDelta α q)) ≤
      C₀ * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) := (inv_mul_le_iff₀ hC₀pos).1 hL.quiet_ge
  have hqe : c * ocEpsilon q Λ (m - 1) ^ (-(4 * ocDelta α q)) ≤
      C₀ * (c * ocTau α q Λ m / ocEll q Λ m ν ^ 2) := by
    calc c * ocEpsilon q Λ (m - 1) ^ (-(4 * ocDelta α q))
        ≤ c * (C₀ * (ocTau α q Λ m / ocEll q Λ m ν ^ 2)) := mul_le_mul_of_nonneg_left hq1 hc.le
      _ = C₀ * (c * ocTau α q Λ m / ocEll q Λ m ν ^ 2) := by ring
  have hexpb := Assembly.exp_neg_le_powerLaw hE hc hC₀pos hy hqe n
  have hE1' : ocEpsilon q Λ (m - 1) ^ (-(max Aobs 0 + (2 - (1 + α) + 4 * ocDelta α q))) *
      ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q * (n : ℝ)) ≤ 1 := by
    rw [← Real.rpow_add hE]
    exact Real.rpow_le_one hE.le hE1 (by linarith)
  calc ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) *
        Real.exp (-(c * ocTau α q Λ m / ocEll q Λ m ν ^ 2))
      ≤ (5 * (1 + max Cobs 0 * C₀) *
          ocEpsilon q Λ (m - 1) ^ (-(max Aobs 0 + (2 - (1 + α) + 4 * ocDelta α q)))) *
        (C₀ ^ n * (n.factorial : ℝ) / c ^ n *
          ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q * (n : ℝ))) :=
        mul_le_mul hcount hexpb (Real.exp_pos _).le
          (mul_nonneg h5 (Real.rpow_pos_of_pos hE _).le)
    _ = 5 * (1 + max Cobs 0 * C₀) * (C₀ ^ n * (n.factorial : ℝ) / c ^ n) *
        (ocEpsilon q Λ (m - 1) ^ (-(max Aobs 0 + (2 - (1 + α) + 4 * ocDelta α q))) *
          ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q * (n : ℝ))) := by ring
    _ ≤ 5 * (1 + max Cobs 0 * C₀) * (C₀ ^ n * (n.factorial : ℝ) / c ^ n) * 1 :=
        mul_le_mul_of_nonneg_left hE1' (mul_nonneg h5 hK)
    _ = 5 * (1 + max Cobs 0 * C₀) * (C₀ ^ n * (n.factorial : ℝ) / c ^ n) := mul_one _

/-- **Absorption of the pulse count into the partition term of the bill**: from
`N e^{-cτ/ℓ²} ≤ K`, `N ℓ√(1/τ) e^{-cτ/ℓ²} ≤ √K ℓ√(N/τ) e^{-(c/2)τ/ℓ²}`. -/
theorem card_exp_absorb {N ℓ τ c K : ℝ} (hN : 0 ≤ N) (hℓ : 0 ≤ ℓ) (hτ : 0 < τ)
    (hK : N * Real.exp (-(c * τ / ℓ ^ 2)) ≤ K) :
    N * ℓ * Real.sqrt (1 / τ) * Real.exp (-(c * τ / ℓ ^ 2)) ≤
      Real.sqrt K * (ℓ * Real.sqrt (N / τ) * Real.exp (-(c / 2 * τ / ℓ ^ 2))) := by
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = Real.exp (-(c / 2 * τ / ℓ ^ 2)) := ⟨_, rfl⟩
  have he0 : 0 ≤ e := he ▸ (Real.exp_pos _).le
  have h2 : Real.exp (-(c * τ / ℓ ^ 2)) = e * e := by
    rw [he, ← Real.exp_add]
    congr 1
    ring
  rw [h2, ← he]
  rw [h2] at hK
  have hs : Real.sqrt N * e ≤ Real.sqrt K := by
    rw [← Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg N) he0)]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow, Real.sq_sqrt hN]
    calc N * e ^ 2 = N * (e * e) := by ring
      _ ≤ K := hK
  have hsq : Real.sqrt (1 / τ) * Real.sqrt N = Real.sqrt (N / τ) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  have hNN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN
  have hA : 0 ≤ ℓ * Real.sqrt (N / τ) * e :=
    mul_nonneg (mul_nonneg hℓ (Real.sqrt_nonneg _)) he0
  calc N * ℓ * Real.sqrt (1 / τ) * (e * e)
      = (ℓ * (Real.sqrt (1 / τ) * Real.sqrt N) * e) * (Real.sqrt N * e) := by
        linear_combination (-(ℓ * Real.sqrt (1 / τ) * e * e)) * hNN
    _ = (ℓ * Real.sqrt (N / τ) * e) * (Real.sqrt N * e) := by rw [hsq]
    _ ≤ (ℓ * Real.sqrt (N / τ) * e) * Real.sqrt K := mul_le_mul_of_nonneg_left hs hA
    _ = Real.sqrt K * (ℓ * Real.sqrt (N / τ) * e) := mul_comm _ _

end AVRegularity.CycleComparison.Reconstruction
end
end
