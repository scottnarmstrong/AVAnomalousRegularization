-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Error.Main
public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Applications.Global.CompactRangeMain
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! **Mass bounds after truncation and a change of radius.** Truncating the
residual pair of the window theorem from the slot orders `K_v ≤ K_max` to the common order `k`, and
moving the radius from `r_s` to `r_* ≤ L r_s` (`L ≥ 1`), multiplies the mass norm squared by at most
`L^{2K_max}` (`factorialNormSq_truncateTorusHk_le`, `factorialNormSq_radius_conversion`).

Special cases:
- `L = 1`, `r_* = r_s`: the mass norm only drops (truncation).
- `K_v = k`: no truncation, the cost is the radius conversion. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

/-- **Pointwise**: truncation to the common order `k` and radius conversion. -/
theorem convMass_trunc_le (r' r L : ℝ) (hr' : 0 ≤ r') (hL : 1 ≤ L) (hrL : r' ≤ L * r)
    (K : ι → ℕ) (k Kmax : ℕ) (hK : ∀ v, k ≤ K v) (hKm : ∀ v, K v ≤ Kmax) (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v) (U : ∀ v, TorusHk (K v) (E v)) :
    massNormSq (E := E) (K := fun _ => k) r' π (fun v => (truncateTorusHk (hK v) (U v)).val) ≤
      L ^ (2 * Kmax) * massNormSq (E := E) (K := K) r π (fun v => (U v).val) := by
  unfold massNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have h1 := CycleComparison.Error.factorialNormSq_truncateTorusHk_le (hK v) r' (U v)
  have h2 := CycleJointProofs.factorialNormSq_radius_conversion hr' hL hrL (U v).val
  have h3 : L ^ (2 * K v) ≤ L ^ (2 * Kmax) := pow_le_pow_right₀ hL (by have := hKm v; omega)
  have hf : 0 ≤ factorialNormSq r (U v).val := by
    unfold factorialNormSq
    exact Finset.sum_nonneg fun j _ => mul_nonneg (factorialWeight_nonneg r _)
      (derivativeNormSq_nonneg _ _)
  have hπi : 0 ≤ (π v)⁻¹ := inv_nonneg.2 (hπ v).le
  calc (π v)⁻¹ * factorialNormSq r' (truncateTorusHk (hK v) (U v)).val
      ≤ (π v)⁻¹ * (L ^ (2 * K v) * factorialNormSq r (U v).val) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hπi
    _ ≤ (π v)⁻¹ * (L ^ (2 * Kmax) * factorialNormSq r (U v).val) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hf) hπi
    _ = L ^ (2 * Kmax) * ((π v)⁻¹ * factorialNormSq r (U v).val) := by ring

/-- **The flux bound after truncation and radius conversion.** -/
theorem convMass_flux {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (ν r' r L : ℝ) (hν : 0 < ν) (hr' : 0 ≤ r') (hL : 1 ≤ L) (hrL : r' ≤ L * r)
    (K : ι → ℕ) (k Kmax : ℕ) (hK : ∀ v, k ≤ K v) (hKm : ∀ v, K v ≤ Kmax) (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v) (tp tf : ℝ)
    (R : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v))) (Xb : ℝ) (hXb : 0 ≤ Xb)
    (hR : ∀ v, MemLp (R v) 2 (volume.restrict (Set.Icc tp tf)))
    (hb : ν⁻¹ * ∫ s in Set.Icc tp tf,
      massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) r π
        (fun v => (R v s).val) ≤ Xb ^ 2) :
    FluxMassLe (ι := ι) (h := h) (K := fun _ => k) ν r' π (Set.Icc tp tf)
      (fun v t => truncateTorusHk (hK v) (R v t)) (L ^ Kmax * Xb) := by
  have hmem : ∀ v, MemLp (fun t => truncateTorusHk (hK v) (R v t)) 2
      (volume.restrict (Set.Icc tp tf)) := fun v =>
    (truncateTorusHk (hK v)).lipschitzWith.comp_memLp (by simp) (hR v)
  refine ⟨hmem, ?_⟩
  have hI1 := CycleComparison.Error.integrable_massNormSq
    (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) r' π (K := fun _ => k)
    (fun v t => truncateTorusHk (hK v) (R v t)) hmem
  have hI2 := CycleComparison.Error.integrable_massNormSq
    (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) r π (K := K) R hR
  have hle : ∫ s in Set.Icc tp tf, massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
        (K := fun _ => k) r' π (fun v => (truncateTorusHk (hK v) (R v s)).val) ≤
      L ^ (2 * Kmax) * ∫ s in Set.Icc tp tf,
        massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) r π
          (fun v => (R v s).val) := by
    rw [← integral_const_mul]
    exact integral_mono hI1 (hI2.const_mul _) fun s =>
      convMass_trunc_le r' r L hr' hL hrL K k Kmax hK hKm π hπ (fun v => R v s)
  have hL0 : 0 ≤ L ^ Kmax := pow_nonneg (by linarith) _
  rw [Real.sqrt_le_left (mul_nonneg hL0 hXb)]
  calc ν⁻¹ * _ ≤ ν⁻¹ * (L ^ (2 * Kmax) * ∫ s in Set.Icc tp tf,
        massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) r π
          (fun v => (R v s).val)) := mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hν.le)
    _ = L ^ (2 * Kmax) * (ν⁻¹ * ∫ s in Set.Icc tp tf,
        massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) r π
          (fun v => (R v s).val)) := by ring
    _ ≤ L ^ (2 * Kmax) * Xb ^ 2 :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg (by linarith) _)
    _ = (L ^ Kmax * Xb) ^ 2 := by ring

/-- **The scalar bound after truncation and radius conversion.** -/
theorem convMass_scalar {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (r' r L : ℝ) (hr' : 0 ≤ r') (hL : 1 ≤ L) (hrL : r' ≤ L * r)
    (K : ι → ℕ) (k Kmax : ℕ) (hK : ∀ v, k ≤ K v) (hKm : ∀ v, K v ≤ Kmax) (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v) (tp tf : ℝ)
    (q : ∀ v, ℝ → TorusHk (K v) (h v)) (Xb : ℝ)
    (hq : ∀ v, Integrable (q v) (volume.restrict (Set.Icc tp tf)))
    (hb : ∫ s in Set.Icc tp tf, Real.sqrt (massNormSq (E := h) (K := K) r π
        (fun v => (q v s).val)) ≤ Xb) :
    ScalarMassLe (ι := ι) (h := h) (K := fun _ => k) r' π (Set.Icc tp tf)
      (fun v t => truncateTorusHk (hK v) (q v t)) (L ^ Kmax * Xb) := by
  have hint : ∀ v, Integrable (fun t => truncateTorusHk (hK v) (q v t))
      (volume.restrict (Set.Icc tp tf)) := fun v =>
    (truncateTorusHk (hK v)).integrable_comp (hq v)
  refine ⟨hint, ?_⟩
  have hI1 := CycleComparison.Error.integrable_sqrt_massNormSq (h := h) r' π hπ
    (K := fun _ => k) (fun v t => truncateTorusHk (hK v) (q v t)) hint
  have hI2 := CycleComparison.Error.integrable_sqrt_massNormSq (h := h) r π hπ (K := K) q hq
  have hL0 : 0 ≤ L ^ Kmax := pow_nonneg (by linarith) _
  calc _ ≤ ∫ s in Set.Icc tp tf, L ^ Kmax * Real.sqrt (massNormSq (E := h) (K := K) r π
          (fun v => (q v s).val)) := by
        refine integral_mono hI1 (hI2.const_mul _) fun s => ?_
        have := convMass_trunc_le (E := h) r' r L hr' hL hrL K k Kmax hK hKm π hπ (fun v => q v s)
        calc _ ≤ Real.sqrt (L ^ (2 * Kmax) * massNormSq (E := h) (K := K) r π
              (fun v => (q v s).val)) := Real.sqrt_le_sqrt this
          _ = _ := by
            rw [Real.sqrt_mul (pow_nonneg (by linarith) _), show 2 * Kmax = Kmax * 2 by ring,
              pow_mul, Real.sqrt_sq hL0]
    _ = L ^ Kmax * ∫ s in Set.Icc tp tf, Real.sqrt (massNormSq (E := h) (K := K) r π
          (fun v => (q v s).val)) := integral_const_mul _ _
    _ ≤ L ^ Kmax * Xb := mul_le_mul_of_nonneg_left hb hL0

end AVRegularity.EntryTerminal.Ingredients.Recon
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! **From the window theorem's output to `ReconBound`.** The glued lift is the menu's
lifted field (`stage_gluedLift_eq_menuLiftedRep` at `c_r = 1`; the weights of the natural weak
stage are the cutoffs), the coefficient is the stage's (`edgeCoefficient_actualFamily`,
`G_w.level = M`, `D.kap M = κ_M`), the window is `[t_p, a + T₀]`, and the residual pair is truncated
to the common order `k₀ + ℓ` and moved from `r_s = min(c_K,1) x` to `r_* = c_K x` at the cost
`max(1, c_K)^{K_max}` (`Conv/Mass.lean`).

Special cases:
- `c_K ≤ 1`: `r_s = r_*`, `L = 1`.
- `K_v = k₀ + ℓ`: no truncation. -/

section Context

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **Conv at a context.** -/
theorem reconConv_at
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (ℓ : ℕ) (hcK : 0 < cK) (h128 : 128 ≤ A.Λ) :
    ReconConvAt c x ℓ := by
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, hterm⟩ := c.data
  have hΛ : 128 ≤ c.D.Λ := hΛD ▸ h128
  have hqq : 1 < c.D.q := hq ▸ X.hq.1
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have hinv := c.weak.2.2.2.2.2.2.2.2.2
  have hnat : c.Gw.IsNatural (M + A.Jw) := hinv.1
  have hone := x.one
  have hκM : 0 < c.D.κ M := by
    have hch : IsOCBandChain X.α X.q A.Λ X.ζ M c.D.κ := hchain
    exact CycleReference.bandChain_pos (by omega) X.hζ hch le_rfl
  have hπ : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hqq hΛ c.lawW v.1
  have hwin : c.tp + rTobs c = c.a + A.T₀ := by simp [rTobs]
  intro hdesc Xb hXb û ŵ Rres qres hval hplain hRm hqi hRb hqb
  rw [hwin] at hval hplain hRm hqi hRb hqb
  have hkK : ∀ v, A.k₀ + ℓ ≤ rK c ℓ v := fun v => Nat.le_add_right _ _
  have hKmax : ∀ v, rK c ℓ v ≤ rKmax A ℓ := fun v => by
    have := descSlots_le c.Gw.actualFamily A.dW A.Dt v
    show A.k₀ + ℓ + descSlots c.Gw.actualFamily A.dW A.Dt v ≤ A.k₀ + ℓ + A.Dt * A.dW
    omega
  have hL1 : 1 ≤ max 1 cK := le_max_left _ _
  have hrL : c.D.termRStar cK M ≤ max 1 cK * rRs c := by
    have he : 0 ≤ c.D.eps M := (Applications.eps_pos hqq hΛ).le
    simp only [OCData.termRStar, rRs]
    have : cK = max 1 cK * min cK 1 := by
      rcases le_total cK 1 with h | h
      · rw [max_eq_left h, min_eq_left h]; ring
      · rw [max_eq_right h, min_eq_right h]; ring
    refine le_of_eq ?_
    calc cK * c.D.eps M = (max 1 cK * min cK 1) * c.D.eps M :=
          congrArg (fun z => z * c.D.eps M) this
      _ = _ := by ring
  have hr0 : 0 ≤ c.D.termRStar cK M :=
    mul_nonneg hcK.le (Applications.eps_pos hqq hΛ).le
  refine ⟨rK c ℓ, hkK, û, ŵ, Rres, qres, ?_⟩
  refine ⟨hdesc, ?_, ?_, ?_, ?_⟩
  · intro t ht v
    filter_upwards [hval t ht v] with y hy
    have hid := stage_gluedLift_eq_menuLiftedRep c.Gw (A.Mt M sXT sZT c.tp cr) M A.NT A.dW c.CcT
      c.aRep (tp := c.tp) (tf := c.a + A.T₀) (t := t) y (by omega) hterm.ge hκM.le
      hone (fun p s => by rw [hnat.2.1 p s, hlev]) ht
    rw [hy]
    exact congrFun hid v
  · have hcoef : edgeCoefficient c.Gw.fam (c.D.kap c.Gw.level) (c.D.eps c.Gw.level)
        (c.D.eps (c.Gw.level - 1)) c.Gw.actual (rK c ℓ) =
        edgeCoefficient c.Gw.actualFamily (c.D.κ M) (ocEpsilon c.D.q c.D.Λ M)
          (ocEpsilon c.D.q c.D.Λ (M - 1)) (fun _ => ()) (rK c ℓ) := by
      rw [GenStage.edgeCoefficient_actualFamily]
      have h1 : c.D.kap c.Gw.level = c.D.κ M := by simp [OCData.kap, hlev, hterm]
      have h2 : c.D.eps c.Gw.level = ocEpsilon c.D.q c.D.Λ M := by rw [hlev]; rfl
      have h3 : c.D.eps (c.Gw.level - 1) = ocEpsilon c.D.q c.D.Λ (M - 1) := by rw [hlev]; rfl
      rw [h1, h2, h3]
    rw [hcoef]
    exact hplain
  · exact convMass_flux (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root)
      (c.D.κ M) (c.D.termRStar cK M) (rRs c) (max 1 cK) hκM hr0 hL1 hrL (rK c ℓ) (A.k₀ + ℓ)
      (rKmax A ℓ) hkK hKmax (c.Gw.mass c.lawW) hπ c.tp (c.a + A.T₀) Rres Xb hXb hRm hRb
  · exact convMass_scalar (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root)
      (c.D.termRStar cK M) (rRs c) (max 1 cK) hr0 hL1 hrL (rK c ℓ) (A.k₀ + ℓ)
      (rKmax A ℓ) hkK hKmax (c.Gw.mass c.lawW) hπ c.tp (c.a + A.T₀) qres Xb hqi hqb

end Context

/-- **Conversion.** -/
theorem termReconConv : TermReconConvStatement := by
  intro ℓ X
  refine ⟨128, le_rfl, fun A hΛ hV => ?_⟩
  refine ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW hcK _ _
    cP CP cHP Cw Ce cker hcP
  exact ⟨(), 1, 1, le_rfl, one_pos, fun j₀ _ => ⟨0, fun M _ c x =>
    reconConv_at c x ℓ hcK hΛ⟩⟩

end AVRegularity.EntryTerminal.Ingredients.Recon
end
