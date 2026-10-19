-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Comparison.GateInputs
import AVRegularity.CoupledEnergy.Variational.TorusSpatialFluxTimeLp
import AVRegularity.CycleComparison.Coarse.Fact.FBoundOps
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CycleComparison.Coarse.SecondOrderResponse
import AVRegularity.Proofs.Intermediate.CoupledEnergy.CoupledEnergyTorus
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
public import AVRegularity.EntryWeakAssembly.Assembly.WeakComparisonDescending
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.CycleComparison.Error.WeakSolution

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Comparison

/-! **Energy of one forced row and its incoming coupling** (the rows of the comparison energy).

* `torusForcedRow_energy`: the energy bound of `coupled_energy_torus` on one component without
  coupling: `|u(t)|² + ν/2 ∫|∇w|² ≤ 2|f|² + 8/ν ∫|Q|² + 10 (∫|g|)²` in the factorial norms of
  radius `ρ`.
* `edgeFlux_memLp`: the incoming flux of one edge is square integrable in time, through the
  higher carrier `coupledCarrierHighTime` and `torusCoupledFlux_trajectory_memLp`.
* `edgeFlux_sqrt_le`: its factorial norm is at most the coefficient seminorms times the reserve
  factors times the gradient factorial norm of the source.
* `torusHk_memLp_add`, `torusHk_memLp_finset_sum`: sums of square integrable carrier trajectories
  (`MemLp.add` at `TorusHk` times out on the instance path; `MemLp.sub` does not). -/

section
open CycleJointProofs CycleJointProofs.PathReduction CoupledEnergy.Variational

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- The sum of two square integrable carrier trajectories. -/
theorem torusHk_memLp_add {k : ℕ} {μ : Measure ℝ} {f g : ℝ → TorusHk k E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : MemLp (fun s => f s + g s) 2 μ := by
  have h := hf.sub (hg.continuousLinearMap_comp (-ContinuousLinearMap.id ℝ (TorusHk k E)))
  refine h.ae_eq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Pi.sub_apply, neg_apply, ContinuousLinearMap.id_apply, sub_neg_eq_add]

/-- A finite sum of square integrable carrier trajectories. -/
theorem torusHk_memLp_finset_sum {ι : Type*} {k : ℕ} {μ : Measure ℝ} (s : Finset ι)
    (f : ι → ℝ → TorusHk k E) (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    MemLp (fun t => ∑ i ∈ s, f i t) 2 μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using torusHk_memLp_zero k μ
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using torusHk_memLp_add (hf j (Finset.mem_insert_self j s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Carrier

section Row

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- **Energy of a forced row** (`coupled_energy_torus` on one component without coupling). -/
theorem torusForcedRow_energy {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ}
    (hd : TorusDriftData ν ρ a b v Kmax) (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν)
    {D k : ℕ} (hD : 2 ≤ D) (hk : k ≤ Kmax) {f : TorusHk k E}
    {Q : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E))} {g : ℝ → TorusHk k E}
    (hQ : MemLp Q 2 (volume.restrict (Set.Icc a b)))
    (hg : Integrable g (volume.restrict (Set.Icc a b)))
    {u : ℝ → TorusHk k E} {w : ℝ → TorusHk (k + 1) E}
    (hs : IsTorusForcedRow ν a b v D k f Q g u w) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    factorialNormSq ρ (u t).val + ν / 2 * ∫ s in Set.Icc a b, gradFactorialNormSq ρ (w s).val ≤
      2 * factorialNormSq ρ f.val + 8 / ν * (∫ s in Set.Icc a b, factorialNormSq ρ (Q s).val) +
        10 * (∫ s in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g s).val)) ^ 2 := by
  obtain ⟨a', B₀, lam, ha, hB₀, hlam, hjets, hB, hab'⟩ := hd.jets
  have hgate := coupled_energy_torus a b hab ρ hρ ν hν v hd.bdd hd.meas hd.smooth hd.div hd.per
    a' B₀ lam ha hB₀ hlam Kmax hjets hB hab' D hD (ι := Fin 1) (h := fun _ => E)
    (fun _ => 1) (fun _ => one_pos) (fun _ => k) (fun _ => hk) (fun _ _ _ _ _ => 0)
    (fun _ _ _ => measurable_const) (fun _ _ _ _ _ => contDiff_const)
    (fun _ _ _ _ _ => fun _ _ => rfl)
    (fun _ _ _ => by rw [CycleComparison.Coarse.coefficientSeminorm_const_zero]; exact ENNReal.zero_ne_top)
    (CycleComparison.Coarse.zeroCoupling_schur ν ρ _ _ D a b)
    (fun _ => f) (fun _ => Q) (fun _ => hQ) (fun _ => g) (fun _ => hg)
  have he := hgate.2.2 (fun _ => u) (fun _ => w) hs t ht
  simpa only [massNormSq, massGradNormSq, Fin.sum_univ_one, inv_one, one_mul] using he

end Row

section Edge

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {a b : ℝ} {D : ℕ} {K : ι → ℕ}
  {A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
  {r : ℝ}

/-- **The incoming flux of one edge is square integrable in time.** -/
theorem edgeFlux_memLp (R : TorusCoefficientData (h := h) r K D a b A) (hab : a ≤ b)
    (hA_meas : ∀ i j d, Measurable fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2)
    (w : ∀ j, ℝ → TorusHk (K j + 1) (h j))
    (hw : ∀ j, MemLp (w j) 2 (volume.restrict (Set.Icc a b))) (i j : ι) :
    MemLp (fun s => R.edgeFlux i j s (w j s)) 2 (volume.restrict (Set.Icc a b)) := by
  classical
  have hread := coupledCarrierHighTime_graphReadout_ae K a b w hw
  have hU : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      (coupledHighGraphReadout K j (coupledCarrierHighTime K a b w hw t)).val =
        coupledCarrierHighTime K a b w hw t j := by
    filter_upwards [coupledCarrierHighTime_ae K a b w hw, hread] with t h1 h2 j
    rw [h2 j]
    exact h1 j
  have hd : ∀ d : admissibleOrders K D i j, MemLp (fun s =>
      if hs : s ∈ Set.Icc a b then torusCoupledFluxTerm r R.radius_pos K D a b i j d (A i j d)
        (R.finite i j d) s hs (R.smooth s hs i j d) (R.periodic s hs i j d)
        (coupledHighGraphReadout K j (coupledCarrierHighTime K a b w hw s)) else 0) 2
      (volume.restrict (Set.Icc a b)) := fun d =>
    torusCoupledFlux_trajectory_memLp K D hab r R.radius_pos i j d (A i j d) (R.finite i j d)
      (hA_meas i j d) (fun t ht => R.smooth t ht i j d) (fun t ht => R.periodic t ht i j d)
      (coupledCarrierHighTime K a b w hw) hU _ (fun t ht => dite_eq_left ht)
  refine (torusHk_memLp_finset_sum Finset.univ _ fun d _ => hd d).ae_eq ?_
  filter_upwards [hread, ae_restrict_mem measurableSet_Icc] with s hs hsI
  simp only [TorusCoefficientData.edgeFlux, dite_eq_left hsI, hs j]

omit [Fintype ι] in
/-- **The factorial norm of the incoming flux of one edge.** -/
theorem edgeFlux_sqrt_le (R : TorusCoefficientData (h := h) r K D a b A) (i j : ι) (s : ℝ)
    (hs : s ∈ Set.Icc a b) (w : TorusHk (K j + 1) (h j)) :
    Real.sqrt (factorialNormSq r (R.edgeFlux i j s w).val) ≤
      (∑ d : admissibleOrders K D i j, (coefficientSeminorm r (K i) a b (A i j d)).toReal *
        derivativeReserveFactor r (K i) (d.1 - 2)) * Real.sqrt (gradFactorialNormSq r w.val) := by
  classical
  unfold TorusCoefficientData.edgeFlux
  rw [dite_eq_left hs, Finset.sum_mul]
  refine (CycleComparison.Coarse.sqrt_fNSq_torus_sum_le r Finset.univ _).trans ?_
  exact Finset.sum_le_sum fun d _ => torusCoupledFluxTerm_factorialNorm_le r R.radius_pos K D a b
    i j d (A i j d) (R.finite i j d) s hs (R.smooth s hs i j d) (R.periodic s hs i j d) w

end Edge
end

/-! **The row recursion of a coupled solution** (the comparison energy: rows).

For a coupled solution with zero initial data and incoming couplings of finite seminorm, let
* `X_v = 8/ν ∫|Q_v|² + 10 (∫|g_v|)²`, with `Q_v` the row's own forcing plus its incoming flux,
  in the factorial norms of radius `r`, and
* `Φ_v = 16/ν ∫|F_v|² + 10 (∫|g_v|)²`.

Then `|u_v(t)|² + ν/2 ∫|∇w_v|² ≤ X_v` (`coupledRow_energy`). If the reserve-weighted coupling
constants satisfy `c_vu ≤ ν C √(π_v/π_u) β_vu` and `∑_u β_vu ≤ S`, then
`X_v ≤ Φ_v + 32 S C² ∑_u β_vu (π_v/π_u) X_u` (`coupledRow_recursion`). -/

section
open CycleJointProofs CycleJointProofs.PathReduction CoupledEnergy.Variational

/-- **The squared row bound** (weighted Cauchy–Schwarz). -/
theorem row_sq_bound {ι : Type*} (s : Finset ι) (x a S K : ℝ) (b c β w : ι → ℝ)
    (hx : 0 ≤ x) (hb : ∀ u ∈ s, 0 ≤ b u) (hβ : ∀ u ∈ s, 0 ≤ β u)
    (hc : ∀ u ∈ s, c u ≤ K * w u * β u) (hc0 : ∀ u ∈ s, 0 ≤ c u) (hS : ∑ u ∈ s, β u ≤ S)
    (hxle : x ≤ a + ∑ u ∈ s, c u * b u) :
    x ^ 2 ≤ 2 * a ^ 2 + 2 * S * K ^ 2 * ∑ u ∈ s, β u * (w u ^ 2 * b u ^ 2) := by
  set T := ∑ u ∈ s, c u * b u with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun u hu => mul_nonneg (hc0 u hu) (hb u hu)
  have hTle : T ≤ ∑ u ∈ s, β u * (K * w u * b u) :=
    Finset.sum_le_sum fun u hu => by
      have := mul_le_mul_of_nonneg_right (hc u hu) (hb u hu)
      linarith [show K * w u * β u * b u = β u * (K * w u * b u) by ring]
  have hcs : (∑ u ∈ s, β u * (K * w u * b u)) ^ 2 ≤
      (∑ u ∈ s, β u) * ∑ u ∈ s, β u * (K * w u * b u) ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hβ
      (fun u hu => mul_nonneg (hβ u hu) (sq_nonneg _)) (fun u hu => by nlinarith [hβ u hu])
  have hQ : 0 ≤ ∑ u ∈ s, β u * (K * w u * b u) ^ 2 :=
    Finset.sum_nonneg fun u hu => mul_nonneg (hβ u hu) (sq_nonneg _)
  have hT2 : T ^ 2 ≤ S * ∑ u ∈ s, β u * (K * w u * b u) ^ 2 :=
    (pow_le_pow_left₀ hT0 hTle 2).trans (hcs.trans (mul_le_mul_of_nonneg_right hS hQ))
  have hsum : ∑ u ∈ s, β u * (K * w u * b u) ^ 2 =
      K ^ 2 * ∑ u ∈ s, β u * (w u ^ 2 * b u ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  have hx2 : x ^ 2 ≤ (a + T) ^ 2 := pow_le_pow_left₀ hx hxle 2
  have h1 : (a + T) ^ 2 ≤ 2 * a ^ 2 + 2 * T ^ 2 := by nlinarith [sq_nonneg (a - T)]
  have h2 : T ^ 2 ≤ S * K ^ 2 * ∑ u ∈ s, β u * (w u ^ 2 * b u ^ 2) := by
    rw [hsum] at hT2
    linarith [show S * (K ^ 2 * ∑ u ∈ s, β u * (w u ^ 2 * b u ^ 2)) =
      S * K ^ 2 * ∑ u ∈ s, β u * (w u ^ 2 * b u ^ 2) by ring]
  linarith

section System

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {ν r a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D Kmax : ℕ} {K : ι → ℕ}
  {A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
  {F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))} {g u : ∀ i, ℝ → TorusHk (K i) (h i)}
  {w : ∀ i, ℝ → TorusHk (K i + 1) (h i)}

/-- The forcing of a row: its own forcing plus its incoming flux. -/
def rowForcingFlux (Rd : TorusCoefficientData (h := h) r K D a b A)
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)) (i : ι) (s : ℝ) :
    TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) :=
  F i s + ∑ j, Rd.edgeFlux i j s (w j s)

/-- The energy bound of a row. -/
def rowEnergyBound (ν r a b : ℝ) (Q : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i)) (i : ι) : ℝ :=
  8 / ν * (∫ s in Set.Icc a b, factorialNormSq r (Q i s).val) +
    10 * (∫ s in Set.Icc a b, Real.sqrt (factorialNormSq r (g i s).val)) ^ 2

/-- **The energy of a row of a coupled solution.** -/
theorem coupledRow_energy (Rd : TorusCoefficientData (h := h) r K D a b A)
    (hd : TorusDriftData ν r a b v Kmax) (hν : 0 < ν) (hD : 2 ≤ D) (hK : ∀ i, K i ≤ Kmax)
    (hA_meas : ∀ i j d, Measurable fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2)
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hs : IsCoupledWeakSolutionTorus ν a b v D K A (fun _ => 0) F g u w)
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    factorialNormSq r (u i t).val + ν / 2 * ∫ s in Set.Icc a b, gradFactorialNormSq r (w i s).val ≤
      rowEnergyBound ν r a b (rowForcingFlux Rd F w) g i := by
  have hab : a ≤ b := ht.1.trans ht.2
  have hQ : MemLp (rowForcingFlux Rd F w i) 2 (volume.restrict (Set.Icc a b)) :=
    torusHk_memLp_add (hF i) (torusHk_memLp_finset_sum Finset.univ _ fun j _ =>
      edgeFlux_memLp Rd hab hA_meas w (fun j => hs.2.1 j) i j)
  have he := torusForcedRow_energy hd hab Rd.radius_pos hν hD (hK i) hQ (hg i)
    (torusWeakSolution_forcedRow Rd (fun _ => 0) F g u w hs i) t ht
  have h0 : factorialNormSq r ((fun _ => (0 : TorusHk (K i) (h i))) i).val = 0 := by
    simp [factorialNormSq, derivativeNormSq]
  rw [h0, mul_zero, zero_add] at he
  exact he

/-- **The row recursion of a coupled solution.** -/
theorem coupledRow_recursion (Rd : TorusCoefficientData (h := h) r K D a b A)
    (hd : TorusDriftData ν r a b v Kmax) (hν : 0 < ν) (hD : 2 ≤ D) (hK : ∀ i, K i ≤ Kmax)
    (hab : a ≤ b)
    (hA_meas : ∀ i j d, Measurable fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2)
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hs : IsCoupledWeakSolutionTorus ν a b v D K A (fun _ => 0) F g u w)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (C S : ℝ) (β : ι → ι → ℝ)
    (hβ : ∀ i j, 0 ≤ β i j) (hS : ∀ i, ∑ j, β i j ≤ S)
    (hc : ∀ i j, ∑ d : admissibleOrders K D i j,
      (coefficientSeminorm r (K i) a b (A i j d)).toReal *
        derivativeReserveFactor r (K i) (d.1 - 2) ≤ ν * C * Real.sqrt (π i / π j) * β i j)
    (i : ι) :
    rowEnergyBound ν r a b (rowForcingFlux Rd F w) g i ≤
      (16 / ν * (∫ s in Set.Icc a b, factorialNormSq r (F i s).val) +
        10 * (∫ s in Set.Icc a b, Real.sqrt (factorialNormSq r (g i s).val)) ^ 2) +
      32 * S * C ^ 2 * ∑ j, β i j * (π i / π j) *
        rowEnergyBound ν r a b (rowForcingFlux Rd F w) g j := by
  classical
  set μ := volume.restrict (Set.Icc a b) with hμ
  set cc : ι → ℝ := fun j => ∑ d : admissibleOrders K D i j,
    (coefficientSeminorm r (K i) a b (A i j d)).toReal *
      derivativeReserveFactor r (K i) (d.1 - 2) with hcc
  have hcc0 : ∀ j, 0 ≤ cc j := fun j => Finset.sum_nonneg fun d _ => by
    unfold derivativeReserveFactor
    have := Rd.radius_pos
    positivity
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun j _ => hβ i j).trans (hS i)
  -- the pointwise bound of the forcing
  have hpt : ∀ s ∈ Set.Icc a b, factorialNormSq r (rowForcingFlux Rd F w i s).val ≤
      2 * factorialNormSq r (F i s).val + 2 * S * (ν * C) ^ 2 *
        ∑ j, β i j * ((π i / π j) * gradFactorialNormSq r (w j s).val) := by
    intro s hs'
    have hle : Real.sqrt (factorialNormSq r (rowForcingFlux Rd F w i s).val) ≤
        Real.sqrt (factorialNormSq r (F i s).val) +
          ∑ j, cc j * Real.sqrt (gradFactorialNormSq r (w j s).val) := by
      refine (CycleComparison.Coarse.sqrt_fNSq_torus_add_le r _ _).trans (add_le_add le_rfl ?_)
      exact (CycleComparison.Coarse.sqrt_fNSq_torus_sum_le r Finset.univ _).trans
        (Finset.sum_le_sum fun j _ => edgeFlux_sqrt_le Rd i j s hs' (w j s))
    have hb := row_sq_bound Finset.univ _ _ S (ν * C)
      (fun j => Real.sqrt (gradFactorialNormSq r (w j s).val)) cc (β i)
      (fun j => Real.sqrt (π i / π j)) (Real.sqrt_nonneg _) (fun j _ => Real.sqrt_nonneg _)
      (fun j _ => hβ i j) (fun j _ => by simpa only [cc, mul_assoc] using hc i j)
      (fun j _ => hcc0 j) (hS i) hle
    rw [Real.sq_sqrt (factorialNormSq_nonneg r _), Real.sq_sqrt (factorialNormSq_nonneg r _)]
      at hb
    refine hb.trans (le_of_eq ?_)
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.sq_sqrt (div_nonneg (hπ i).le (hπ j).le),
      Real.sq_sqrt (CycleComparison.Coarse.gradFactorialNormSq_nonneg r _)]
  -- integrate
  have hFi := CycleComparison.Coarse.integrable_factorialNormSq_torus (ρ := r) (hF i)
  have hwi := fun j => CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (ρ := r)
    (hs.2.1 j)
  have hQi : Integrable (fun s => factorialNormSq r (rowForcingFlux Rd F w i s).val) μ :=
    CycleComparison.Coarse.integrable_factorialNormSq_torus (torusHk_memLp_add (hF i)
      (torusHk_memLp_finset_sum Finset.univ _ fun j _ =>
        edgeFlux_memLp Rd hab hA_meas w (fun j => hs.2.1 j) i j))
  have hint : (∫ s in Set.Icc a b, factorialNormSq r (rowForcingFlux Rd F w i s).val) ≤
      2 * (∫ s in Set.Icc a b, factorialNormSq r (F i s).val) + 2 * S * (ν * C) ^ 2 *
        ∑ j, β i j * ((π i / π j) * ∫ s in Set.Icc a b, gradFactorialNormSq r (w j s).val) := by
    have hrhs : Integrable (fun s => 2 * factorialNormSq r (F i s).val + 2 * S * (ν * C) ^ 2 *
        ∑ j, β i j * ((π i / π j) * gradFactorialNormSq r (w j s).val)) μ :=
      (hFi.const_mul 2).add ((integrable_finsetSum Finset.univ fun j _ =>
        ((hwi j).const_mul (π i / π j)).const_mul (β i j)).const_mul _)
    refine (setIntegral_mono_on hQi hrhs measurableSet_Icc hpt).trans (le_of_eq ?_)
    rw [integral_add (hFi.const_mul 2) ((integrable_finsetSum Finset.univ fun j _ =>
        ((hwi j).const_mul (π i / π j)).const_mul (β i j)).const_mul _),
      integral_const_mul, integral_const_mul, integral_finsetSum _ fun j _ =>
        ((hwi j).const_mul (π i / π j)).const_mul (β i j)]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_const_mul]
  -- the gradients of the sources
  have hgrad : ∀ j, (∫ s in Set.Icc a b, gradFactorialNormSq r (w j s).val) ≤
      2 / ν * rowEnergyBound ν r a b (rowForcingFlux Rd F w) g j := by
    intro j
    have he := coupledRow_energy Rd hd hν hD hK hA_meas hF hg hs j a ⟨le_rfl, hab⟩
    have h0 := factorialNormSq_nonneg r (u j a).val
    rw [div_mul_eq_mul_div, le_div_iff₀ hν]
    nlinarith
  have hsum : ∑ j, β i j * ((π i / π j) * ∫ s in Set.Icc a b, gradFactorialNormSq r (w j s).val) ≤
      ∑ j, β i j * ((π i / π j) * (2 / ν * rowEnergyBound ν r a b (rowForcingFlux Rd F w) g j)) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgrad j)
      (div_nonneg (hπ i).le (hπ j).le)) (hβ i j)
  have hkey : 8 / ν * (∫ s in Set.Icc a b, factorialNormSq r (rowForcingFlux Rd F w i s).val) ≤
      16 / ν * (∫ s in Set.Icc a b, factorialNormSq r (F i s).val) +
        32 * S * C ^ 2 * ∑ j, β i j * (π i / π j) *
          rowEnergyBound ν r a b (rowForcingFlux Rd F w) g j := by
    have h8 : 0 ≤ 8 / ν := by positivity
    have hstep := mul_le_mul_of_nonneg_left (hint.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hsum (by positivity)))) h8
    refine hstep.trans (le_of_eq ?_)
    have hre : ∑ j, β i j * ((π i / π j) *
        (2 / ν * rowEnergyBound ν r a b (rowForcingFlux Rd F w) g j)) =
        2 / ν * ∑ j, β i j * (π i / π j) * rowEnergyBound ν r a b (rowForcingFlux Rd F w) g j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hre]
    generalize (∑ j, β i j * (π i / π j) * rowEnergyBound ν r a b (rowForcingFlux Rd F w) g j) = X
    field_simp
    ring
  unfold rowEnergyBound at hkey ⊢
  linarith

end System
end

end AVRegularity.Providers.WeakGen.Comparison
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Comparison

/-! **Regularity of the physical coefficients of a weak passage output** (the comparison energy:
bootstrap).

For a weak passage output `G'` with a flux production `S` (`IndependentWeakStageFluxProduction`):
* the coefficients are jointly measurable in `(t, x)` on every time window
  (`weakProduction_physCoeff_joint_measurable`). The proof is that of
  `native_physCoeff_joint_measurable_of_context`, with the time measurability of the native
  fluxes taken from the production's joint source reserves (`JointSourceReserve.measurable`,
  Carathéodory in `(z, X)`) instead of a context certificate;
* the coefficients are spatially `C^K` for `K ≤ H` (`weakProduction_physCoeff_contDiff`). -/

open EntryWeakProofs CycleJointProofs Construction.Preservation.Buffer

/-- **Carathéodory for a joint source reserve**: measurable in `(t, z)` at fixed `X`, continuous
in `(z, X)` at fixed `t`, hence jointly measurable. -/
theorem jointSourceReserve_joint_measurable {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → Vec 2}
    (Q : JointSourceReserve H f) :
    Measurable (fun X : ℝ × (Vec 2 × Vec 2) => f X.1 X.2.1 X.2.2) := by
  let g := fun Y : Vec 2 × Vec 2 => fun t : ℝ => f t Y.1 Y.2
  have hc t : Continuous (fun Y => g Y t) := (Q.regular t).continuous
  have hm Y : Measurable (g Y) := (Q.measurable Y.2).comp (measurable_id.prodMk measurable_const)
  exact (measurable_uncurry_of_continuous_of_measurable hc hm).comp measurable_swap

variable {D : OCData} {Dm : ℕ} {bw B : ℝ} {j₀ minBase cap H : ℕ}
  {G G' : GenStage D (fun _ => ℝ) Dm bw j₀}

/-- The weighted physical source array of one piece is jointly measurable. -/
theorem weakProduction_weighted_source_array_measurable
    (S : IndependentWeakStageFluxProduction G' minBase cap H B)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hbw : bw ≤ 1 / 10000) (hB : 0 ≤ B)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (Mtop : ℕ) (hG : G'.IsNatural Mtop) (hbase : minBase ≤ G'.level - 1)
    (tS tZ : ℝ) (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (p : OddSlot)
    (a : ℕ) (I : DerivativeWord2 (a - 1)) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 =>
      G'.fam.weight p z.1 • weakStagePhysicalSourceArray G' v u γ z.1 p a I z.2) := by
  classical
  have hw : Measurable (fun z : Set.Icc tS tZ × Vec 2 => G'.fam.weight p z.1) := by
    have he : G'.fam.weight p = ocCutoff D.α D.q D.Λ G'.level p.1 := funext (hG.2.1 p)
    rw [he]
    exact (CycleReference.ocCutoff_contDiff (by omega) p.1).continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_fst)
  refine hw.smul ?_
  by_cases ha : a ∈ Finset.Icc 2 (G'.fam.identity v u γ).maxOrder
  · let c := WeakStageProductionContext.actual G' Mtop hG minBase cap hbase p
    have hc : c.chain.1.children = [] := by
      change (G'.actual p).1.children = []
      rw [hG.2.2.1 p]
      rfl
    obtain ⟨Q, _⟩ := S.native_joint_reserve hq hΛ hζ hband hbw hB P Mn rW Din hp ht c hc v u γ a
      (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2 I
    have hQ := jointSourceReserve_joint_measurable Q
    have he : 0 < D.eps G'.level := Construction.Stream.ocEpsilon_pos (by omega)
    have hE : 0 < D.eps (G'.level - 1) := Construction.Stream.ocEpsilon_pos (by omega)
    have hy : Continuous (fun z : Set.Icc tS tZ × Vec 2 =>
        D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) z.2 z.1) :=
      (CycleReference.streamFlow_joint_smooth (D.hΦ (G'.level - 1))).continuous.comp
        (continuous_const.prodMk (continuous_snd.prodMk
          (continuous_subtype_val.comp continuous_fst)))
    have hy1 : Continuous (fun z : Set.Icc tS tZ × Vec 2 => (D.eps G'.level)⁻¹ •
        D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) z.2 z.1) :=
      (continuous_const_smul (D.eps G'.level)⁻¹).comp hy
    have hy2 : Continuous (fun z : Set.Icc tS tZ × Vec 2 =>
        (D.eps G'.level / D.eps (G'.level - 1)) • ((D.eps G'.level)⁻¹ •
          D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) z.2 z.1)) :=
      (continuous_const_smul (D.eps G'.level / D.eps (G'.level - 1))).comp hy1
    have hm : Measurable (fun z : Set.Icc tS tZ × Vec 2 =>
        ((z.1 : ℝ), ((D.eps G'.level)⁻¹ •
          D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) z.2 z.1,
          (D.eps G'.level / D.eps (G'.level - 1)) • ((D.eps G'.level)⁻¹ •
          D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) z.2 z.1)))) :=
      (measurable_subtype_coe.comp measurable_fst).prodMk (hy1.measurable.prodMk hy2.measurable)
    convert hQ.comp hm using 1
    funext z
    simp only [Function.comp_apply, weakStagePhysicalSourceArray, ite_eq_left ha]
    rw [native_inverse_material_eq_flow hG p z.1]
    exact congrFun (dimensionalSourcePhysicalChartSample_eq
      (fun t Y X => G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
        p (G'.actual p) v u γ a I t Y X) (D.eps (G'.level - 1)) (D.eps G'.level) hE he
      (fun x => D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) x z.1) z.1) z.2
  · have he : (fun z : Set.Icc tS tZ × Vec 2 =>
        weakStagePhysicalSourceArray G' v u γ z.1 p a I z.2) = fun _ => 0 := by
      funext z
      exact ite_eq_right ha
    rw [he]
    exact measurable_const

/-- The weighted Piola array of one piece is jointly measurable. -/
theorem weakProduction_weighted_piece_array_measurable
    (S : IndependentWeakStageFluxProduction G' minBase cap H B)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hbw : bw ≤ 1 / 10000) (hB : 0 ≤ B)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (Mtop : ℕ) (hG : G'.IsNatural Mtop) (hbase : minBase ≤ G'.level - 1)
    (tS tZ : ℝ) (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (p : OddSlot)
    (d : ℕ) (hd : 2 ≤ d) (A : DerivativeWord2 (d - 1)) (k : Fin 2) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 => G'.fam.weight p z.1 *
      transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material z.1).symm)
        (G'.fam.identity v u γ).maxOrder
        (fun d' I => G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
          p (G'.actual p) v u γ d' I z.1 (((G'.fam.piece p).material z.1).symm z.2)
          ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material z.1).symm z.2)) (d - 1) A z.2 k) := by
  let K := naturalPreparationJacobian (D.hΦ (G'.level - 1)) (D.slotAnchor G'.level p.1)
  let Bf := fun a (I : DerivativeWord2 (a - 1)) (z : Set.Icc tS tZ × Vec 2) =>
    G'.fam.weight p z.1 • weakStagePhysicalSourceArray G' v u γ z.1 p a I z.2
  have hB' : ∀ a I i, Measurable (fun z => Bf a I z i) := fun a I i =>
    (measurable_pi_apply i).comp (weakProduction_weighted_source_array_measurable S hq hΛ hζ hband hbw hB P Mn
      rW Din hp ht Mtop hG hbase tS tZ v u γ p a I)
  have hm := transportedCoeff_joint_measurable tS tZ K
    (naturalPreparationJacobian_entry_smooth (D.hΦ (G'.level - 1)) (D.slotAnchor G'.level p.1))
    (G'.fam.identity v u γ).maxOrder Bf hB' (d - 1) A k
  convert hm using 1
  funext z
  simp only [Bf, K]
  rw [transportedCoeff_smul_native, Pi.smul_apply, smul_eq_mul,
    ← native_inverse_jacobian_eq_natural hG p z.1,
    weakStagePhysicalSourceArray_transport_eq G' v u γ z.1 p d hd A z.2]

/-- **The physical coefficients of a weak passage output are jointly measurable** on every time
window. -/
theorem weakProduction_physCoeff_joint_measurable
    (S : IndependentWeakStageFluxProduction G' minBase cap H B)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hbw : bw ≤ 1 / 10000) (hB : 0 ≤ B)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (Mtop : ℕ) (hG : G'.IsNatural Mtop) (hbase : minBase ≤ G'.level - 1)
    (tS tZ : ℝ) (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (d : ℕ) (hd : 2 ≤ d) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 => G'.physCoeff v u γ d z.1 z.2) := by
  let b := fun p (z : Set.Icc tS tZ × Vec 2) k (A : DerivativeWord2 (d - 1)) =>
    transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material z.1).symm)
      (G'.fam.identity v u γ).maxOrder
      (fun d' I => G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
        p (G'.actual p) v u γ d' I z.1 (((G'.fam.piece p).material z.1).symm z.2)
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material z.1).symm z.2)) (d - 1) A z.2 k
  change Measurable (fun z : Set.Icc tS tZ × Vec 2 => ∑ᶠ p,
    G'.fam.weight p z.1 • nativeArrayAssembly (d - 1) (G'.fam.identity v u γ).map (b p z))
  refine measurable_piece_finsum_onWindow G'.fam tS tZ
    (fun p z => G'.fam.weight p z.1 •
      nativeArrayAssembly (d - 1) (G'.fam.identity v u γ).map (b p z)) ?_ ?_
  · intro p
    have hm := nativeArrayAssembly_measurable (d - 1) (G'.fam.identity v u γ).map
      (fun z k A => G'.fam.weight p z.1 * b p z k A)
      (fun k A => weakProduction_weighted_piece_array_measurable S hq hΛ hζ hband hbw hB P Mn rW Din hp ht
        Mtop hG hbase tS tZ v u γ p d hd A k)
    convert hm using 1
    funext z
    exact ((nativeArrayAssembly (d - 1) (G'.fam.identity v u γ).map).map_smul
      (G'.fam.weight p z.1) (b p z)).symm
  · intro p z hout
    rw [G'.fam.weight_zero p z.1 hout]
    exact zero_smul ℝ (nativeArrayAssembly (d - 1) (G'.fam.identity v u γ).map (b p z))

/-- **The physical coefficients of a weak passage output are spatially `C^K`** for `K ≤ H`. -/
theorem weakProduction_physCoeff_contDiff
    (S : IndependentWeakStageFluxProduction G' minBase cap H B)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hbw : bw ≤ 1 / 10000) (hB : 0 ≤ B)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (Mtop : ℕ) (hG : G'.IsNatural Mtop) (hbase : minBase ≤ G'.level - 1)
    (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (d : ℕ) (hd : 2 ≤ d) (Ks : ℕ) (hKs : Ks ≤ H)
    (t : ℝ) : ContDiff ℝ (Ks : ℕ) (G'.physCoeff v u γ d t) :=
  weak_constituentPhysical_spatial_contDiff G'.fam _ _ _ G'.actual v u γ d Ks t
    (fun p _ => S.physical_piece_contDiff hq hΛ hζ hband hbw hB P Mn rW Din hp ht Mtop hG hbase
      v u γ d hd Ks hKs t p)

end AVRegularity.Providers.WeakGen.Comparison
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Comparison

/-! **Inputs of the bootstrap of the comparison energy at one weak passage.**

* `weakPassage_physCoeff_regular`: above the coefficient floor, the physical coefficients of
  every passage stage are jointly measurable, spatially `C^K` and periodic, with finite
  seminorms at radius `ε_i` up to the largest reserve of the comparison.
* `weakComparisonDescendingCoeff_gate`: hence the summed coefficients at the descending reserves
  satisfy the coefficient hypotheses of `coupled_energy_torus` at every radius `ρ ≤ ε_i`.
* `weakComparison_forcing_lp`: a finite row forcing cost and the measurability of the forcings
  give the time integrability that `coupled_energy_torus` needs. -/

section
open WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs Construction.Preservation.Buffer

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The base facts of the instance data. -/
theorem weakPassageInstance_base (c : WeakPassageInstance plan R) :
    128 ≤ c.D.Λ ∧ 1 < c.D.q ∧ IsFastProfile c.D.ζ ∧
      IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
  refine ⟨c.base_eq ▸ (plan.base_ge B).trans c.base_ge, c.q_eq ▸ B.hq.1, c.profile_eq ▸ B.hζ, ?_⟩
  rw [c.alpha, c.q_eq, c.base_eq, c.profile_eq, c.terminal]
  exact c.band

/-- **Regularity of the physical coefficients of a passage stage**, above the coefficient
floor. -/
theorem weakPassage_physCoeff_regular (c : WeakPassageInstance plan R)
    (hfloor : weakComparisonCoeffFloor R ≤ c.M) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (t₀ t₁ : ℝ) (v u : CompIn (c.stage i).comps)
    (γ : (c.stage i).fam.Γ v u) (d : ℕ) (hd : 2 ≤ d) :
    Measurable (fun z : Set.Icc t₀ t₁ × Vec 2 => (c.stage i).physCoeff v u γ d z.1 z.2) ∧
    (∀ k ≤ A.Jw * A.Rw * (A.Jw * A.Nw - 1), ∀ t,
      ContDiff ℝ (k : ℕ) ((c.stage i).physCoeff v u γ d t)) ∧
    (∀ t, AVenhance.IsZ2Periodic ((c.stage i).physCoeff v u γ d t)) ∧
    (∀ k ≤ A.Jw * A.Rw * (A.Jw * A.Nw - 1),
      coefficientSeminorm (c.D.eps i) k t₀ t₁ ((c.stage i).physCoeff v u γ d) ≠ ⊤) := by
  by_cases hiJ : i = c.M + A.Jw
  · subst hiJ
    exact ((c.construction.2.1.2.2.1 v u).false γ).elim
  have hit' : i < c.M + A.Jw := lt_of_le_of_ne hit hiJ
  have hΛ : 128 ≤ A.Λ := (plan.base_ge B).trans c.base_ge
  obtain ⟨hDΛ, hq, hζ, hband⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  unfold weakComparisonCoeffFloor at hfloor
  rw [dite_eq_left hΛ] at hfloor
  obtain ⟨hB1, hspec⟩ := Classical.choose_spec
    (uniform_weak_construction_flux_production B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
      A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw R.sZ
      (A.Jw * A.Rw * (A.Jw * A.Nw - 1)) A.Jw_pos)
  obtain ⟨-, hprod⟩ := Classical.choose_spec hspec
  obtain ⟨-, hcoef⟩ := Classical.choose_spec (Classical.choose_spec
    (uniform_weak_physical_coefficient_production B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
      A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw R.sZ
      (A.Jw * A.Rw * (A.Jw * A.Nw - 1)) A.Jw_pos)).2
  have hM₀ := (le_max_left _ _).trans hfloor
  have hM₁ := (le_max_right _ _).trans hfloor
  obtain ⟨S⟩ := hprod c.D (hM₀.trans c.terminal.symm.le) c.alpha c.q_eq c.base_eq c.profile_eq
    c.streams hband c.Dm c.order_ge c.j₀ c.stage c.P
    (⟨A.Nw, A.Rw, R.sX, R.sZ, A.η₀, c.M + A.Jw⟩ : WeakMenu) c.M 0 (c.D.termRW A.σw c.M)
    rfl rfl rfl c.construction _ le_rfl i hi.le hit
  have hl := weakConstruction_level c.P _ c.M A.Jw 0 _ c.stage c.construction i hi.le hit
  have hnat := weakConstruction_output_natural c.P _ c.M A.Jw 0 _ c.stage c.construction i
    hi.le hit'
  have htags := weakConstruction_stage_hasTags c.P _ c.M A.Jw 0 _ c.construction i hi.le hit
  have hp := (c.construction.2.2 (i + 1) (by omega) (by omega)).1
  rw [Nat.add_sub_cancel] at hp
  have hbase : Classical.choose hspec ≤ (c.stage i).level - 1 := by
    rw [hl]
    omega
  have hshift := weakConstruction_shiftInvariant c.P _ c.M A.Jw 0 _ c.stage c.construction hζ
    (fun _ => Construction.Stream.ocTau_pos hΛ1) (fun _ => Construction.Stream.ocEpsilon_pos hΛ1)
    (fun m _ _ => (weakData_cellScaleSq_pos c.D hΛ1 hζ hband m).le) i hi.le hit
  refine ⟨weakProduction_physCoeff_joint_measurable S hq hDΛ hζ hband A.bw_small
      (zero_le_one.trans hB1) c.P _ _ _ hp htags (c.M + A.Jw) hnat hbase t₀ t₁ v u γ d hd,
    fun k hk t => weakProduction_physCoeff_contDiff S hq hDΛ hζ hband A.bw_small
      (zero_le_one.trans hB1) c.P _ _ _ hp htags (c.M + A.Jw) hnat hbase v u γ d hd k hk t,
    fun t => native_physCoeff_periodic hnat (hshift) v u γ d t, fun k hk => ?_⟩
  by_cases hdn : d ≤ ((c.stage i).fam.identity v u γ).maxOrder
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hcoef c.D (hM₁.trans c.terminal.symm.le) c.alpha c.q_eq c.base_eq c.profile_eq c.streams
        hband c.Dm c.order_ge c.j₀ c.stage c.P c.M R.sX 0 A.η₀ (c.D.termRW A.σw c.M) c.terminal
        c.construction i hi.le hit' v u γ d k hd hdn hk t₀ t₁)
  · have hz : (c.stage i).physCoeff v u γ d = fun _ _ => 0 := by
      funext t x
      exact constituentPhysical_zero_above_max (c.stage i).fam _ _ _ (c.stage i).actual v u γ d
        (not_le.mp hdn) t x
    rw [hz, coefficientSeminorm_zero_function]
    exact ENNReal.zero_ne_top

/-- **The descending coefficients satisfy the coefficient hypotheses of `coupled_energy_torus`**
at every radius `ρ ≤ ε_i`. -/
theorem weakComparisonDescendingCoeff_gate (c : WeakPassageInstance plan R)
    (hfloor : weakComparisonCoeffFloor R ≤ c.M) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (a b ρ : ℝ) (hρ : 0 < ρ) (hρe : ρ ≤ c.D.eps i)
    (v u : CompIn (c.stage i).comps)
    (d : admissibleOrders (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1)
      (1 + A.Jw * A.Nw) v u) :
    Measurable (fun p : Set.Icc a b × Vec 2 => weakComparisonDescendingCoeff c i v u d p.1 p.2) ∧
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (weakComparisonReserve R v.1 : ℕ)
      (weakComparisonDescendingCoeff c i v u d t)) ∧
    (∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (weakComparisonDescendingCoeff c i v u d t)) ∧
    coefficientSeminorm ρ (weakComparisonReserve R v.1) a b
      (weakComparisonDescendingCoeff c i v u d) ≠ ⊤ := by
  have hd : 2 ≤ d.1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 d.2).1).1
  have hK := weak_comparison_reserve_le R v.1
  have hreg := fun γ => weakPassage_physCoeff_regular c hfloor i hi hit a b v u γ d.1 hd
  refine ⟨Finset.measurable_sum _ fun γ _ => (hreg γ).1,
    fun t _ => ContDiff.sum fun γ _ => (hreg γ).2.1 _ hK t,
    fun t _ n x => Finset.sum_congr rfl fun γ _ => (hreg γ).2.2.1 t n x, ?_⟩
  refine ne_top_of_le_ne_top ?_ (CycleComparison.Error.coefficientSeminorm_finset_sum_le Finset.univ ρ hρ.le
    (weakComparisonReserve R v.1) a b (fun γ => (c.stage i).physCoeff v u γ d.1)
    (fun γ _ t _ => (hreg γ).2.1 _ hK t))
  exact ENNReal.sum_ne_top.2 fun γ _ => coefficientSeminorm_radius_ne_top ρ (c.D.eps i) hρ.le hρe
    _ a b _ ((hreg γ).2.2.2 _ hK)

/-- **A finite row forcing cost gives the time integrability of the forcings.** -/
theorem weakComparison_forcing_lp {c : WeakPassageInstance plan R} {r : WeakPassageRun c}
    {i : ℕ} (h : WeakComparisonEnergyInput r i) (v : CompIn (c.stage i).comps)
    (hf : weakComparisonRowForcing h v ≠ ⊤) :
    MemLp (h.F v) 2 (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))) ∧
      Integrable (h.g v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))) := by
  obtain ⟨hDΛ, -, -, -⟩ := weakPassageInstance_base c
  have hρ : 0 < plan.radius R * c.D.eps i :=
    mul_pos (plan.radius_pos R) (Construction.Stream.ocEpsilon_pos (by omega))
  have hπ : (ENNReal.ofReal (weakMass c.D A.Nw A.Jw A.η₀ v.1))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hκ : (ENNReal.ofReal (c.D.κ c.M))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hb : ∀ {x y : ℝ≥0∞}, x ≠ 0 → x * y ≠ ⊤ → y ≠ ⊤ :=
    fun hx hxy hy => hxy (ENNReal.mul_eq_top.2 (Or.inl ⟨hx, hy⟩))
  unfold weakComparisonRowForcing at hf
  obtain ⟨h1, h2⟩ := ENNReal.add_ne_top.1 (hb hπ hf)
  have hI₂ : (∫⁻ t in Set.Icc (r.tq i) (r.a + A.T₀),
      ENNReal.ofReal (Real.sqrt (factorialNormSq (plan.radius R * c.D.eps i) (h.g v t).val))) ≠ ⊤ :=
    fun ht => h2 (by rw [ht]; exact ENNReal.top_pow two_ne_zero)
  exact ⟨torusHk_memLp_of_factorial hρ (h.F_meas v) (hb hκ h1),
    torusHk_integrable_of_factorial hρ (h.g_meas v) hI₂⟩
end

/-! **Record-size coupling constants of the rows** (the comparison energy: rows).

Above the coefficient floor, every physical coefficient of a passage stage has seminorm at most
`C_K · size · κ_M · ε_i^{d-2}` at radius `ε_i` (`weakPassage_physCoeff_seminorm_le`, from
`uniform_weak_physical_coefficient_production`). Hence the coupling coefficients of a row at the
radius `ρ ε_i` (`ρ ≤ 1`) and its reserve, weighted by the reserve factors of the flux bound, are
at most `κ_M · C_R · ∑_γ size_γ` (`weakComparison_edge_le`). Here
`C_R = C_K ∑_{n < J_w N_w} ρ^{-n} (K_max + n)!` (`weakComparisonEdgeConst`) depends on the request
and the plan's radius only. -/

section
open WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The record-size seminorm constant of the coefficient production at the largest reserve of the
comparison energy. -/
def weakComparisonCK {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) : ℝ :=
  if hΛ : 128 ≤ A.Λ then
    Classical.choose (uniform_weak_physical_coefficient_production B.α B.s B.q B.hα₀ B.hα₁ B.hs₀
      B.hs₁ B.hq A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw R.sZ
      (A.Jw * A.Rw * (A.Jw * A.Nw - 1)) A.Jw_pos)
  else 0

theorem weakComparisonCK_nonneg (R : WeakPassageRequest A) : 0 ≤ weakComparisonCK R := by
  unfold weakComparisonCK
  split
  · exact (Classical.choose_spec (uniform_weak_physical_coefficient_production B.α B.s B.q B.hα₀
      B.hα₁ B.hs₀ B.hs₁ B.hq A.Λ ‹_› B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw R.sZ
      (A.Jw * A.Rw * (A.Jw * A.Nw - 1)) A.Jw_pos)).1
  · exact le_rfl

/-- The edge constant of the rows. -/
def weakComparisonEdgeConst (plan : WeakPassagePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) : ℝ :=
  weakComparisonCK R * ∑ n ∈ Finset.range (A.Jw * A.Nw),
    (plan.radius R)⁻¹ ^ n * ((A.Jw * A.Rw * (A.Jw * A.Nw - 1) + n).factorial : ℝ)

/-- The scale factor of the production bound is at most `ε_i^{d-2}`. -/
theorem production_scale_le {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 ≤ ε') (hle : ε' ≤ ε) {d mo : ℕ}
    (hd : 2 ≤ d) (hdm : d ≤ mo) : ε' ^ (mo - 2) * ε ^ ((d : ℝ) - (mo : ℝ)) ≤ ε ^ (d - 2) := by
  have h1 : ε' ^ (mo - 2) ≤ ε ^ (mo - 2) := pow_le_pow_left₀ hε' hle _
  have h2 : ε ^ (mo - 2) * ε ^ ((d : ℝ) - (mo : ℝ)) = ε ^ (d - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hε]
    congr 1
    push_cast [Nat.cast_sub (show 2 ≤ mo by omega), Nat.cast_sub hd]
    ring
  calc _ ≤ ε ^ (mo - 2) * ε ^ ((d : ℝ) - (mo : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hε.le _)
    _ = _ := h2

/-- **Record-size seminorms** of the physical coefficients of a passage stage, above the
coefficient floor. -/
theorem weakPassage_physCoeff_seminorm_le (c : WeakPassageInstance plan R)
    (hfloor : weakComparisonCoeffFloor R ≤ c.M) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (t₀ t₁ : ℝ) (v u : CompIn (c.stage i).comps)
    (γ : (c.stage i).fam.Γ v u) (d : ℕ) (hd : 2 ≤ d) (k : ℕ)
    (hk : k ≤ A.Jw * A.Rw * (A.Jw * A.Nw - 1)) :
    coefficientSeminorm (c.D.eps i) k t₀ t₁ ((c.stage i).physCoeff v u γ d) ≤
      ENNReal.ofReal (weakComparisonCK R * ((c.stage i).fam.identity v u γ).record.size *
        c.D.κ c.M * c.D.eps i ^ (d - 2)) := by
  by_cases hiJ : i = c.M + A.Jw
  · subst hiJ
    exact ((c.construction.2.1.2.2.1 v u).false γ).elim
  have hit' : i < c.M + A.Jw := lt_of_le_of_ne hit hiJ
  have hΛ : 128 ≤ A.Λ := (plan.base_ge B).trans c.base_ge
  obtain ⟨hDΛ, hq, hζ, hband⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hε : ∀ j, 0 < c.D.eps j := fun _ => Construction.Stream.ocEpsilon_pos hΛ1
  have hκ : 0 ≤ c.D.κ c.M := by
    have := weakData_kap_pos c.D hΛ1 hζ hband c.D.term
    rw [weakData_kap_terminal c.D c.D.term le_rfl, c.terminal] at this
    exact this.le
  unfold weakComparisonCoeffFloor at hfloor
  rw [dite_eq_left hΛ] at hfloor
  have hM₁ := (le_max_right _ _).trans hfloor
  obtain ⟨-, hcoef⟩ := Classical.choose_spec (Classical.choose_spec
    (uniform_weak_physical_coefficient_production B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
      A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw R.sZ
      (A.Jw * A.Rw * (A.Jw * A.Nw - 1)) A.Jw_pos)).2
  have hCK : weakComparisonCK R = Classical.choose (uniform_weak_physical_coefficient_production
      B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw
      A.Rw R.sZ (A.Jw * A.Rw * (A.Jw * A.Nw - 1)) A.Jw_pos) := by
    unfold weakComparisonCK
    rw [dite_eq_left hΛ]
  by_cases hdn : d ≤ ((c.stage i).fam.identity v u γ).maxOrder
  · refine (hcoef c.D (hM₁.trans c.terminal.symm.le) c.alpha c.q_eq c.base_eq c.profile_eq
      c.streams hband c.Dm c.order_ge c.j₀ c.stage c.P c.M R.sX 0 A.η₀ (c.D.termRW A.σw c.M)
      c.terminal c.construction i hi.le hit' v u γ d k hd hdn hk t₀ t₁).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [← hCK]
    have hscale := production_scale_le (hε i) (hε (i + 1)).le
      (EntryScales.epsilon_antitone hq (by omega) (Nat.le_succ i)) hd hdn
    have hpos : 0 ≤ weakComparisonCK R * ((c.stage i).fam.identity v u γ).record.size *
        c.D.κ c.M := mul_nonneg (mul_nonneg (weakComparisonCK_nonneg R)
          ((c.stage i).fam.identity v u γ).record.size_nonneg) hκ
    calc weakComparisonCK R * ((c.stage i).fam.identity v u γ).record.size * c.D.κ c.M *
          c.D.eps (i + 1) ^ (((c.stage i).fam.identity v u γ).maxOrder - 2) *
          c.D.eps i ^ ((d : ℝ) - (((c.stage i).fam.identity v u γ).maxOrder : ℝ))
        = weakComparisonCK R * ((c.stage i).fam.identity v u γ).record.size * c.D.κ c.M *
          (c.D.eps (i + 1) ^ (((c.stage i).fam.identity v u γ).maxOrder - 2) *
          c.D.eps i ^ ((d : ℝ) - (((c.stage i).fam.identity v u γ).maxOrder : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale hpos
  · have hz : (c.stage i).physCoeff v u γ d = fun _ _ => 0 := by
      funext t x
      exact constituentPhysical_zero_above_max (c.stage i).fam _ _ _ (c.stage i).actual v u γ d
        (not_le.mp hdn) t x
    rw [hz, coefficientSeminorm_zero_function]
    exact bot_le

/-- The algebra of one order of the edge constant. -/
theorem edge_order_term_le (x ε ρ : ℝ) (hx : 0 ≤ x) (hε : 0 < ε) (hρ : 0 < ρ) (r K Kmax : ℕ)
    (hK : K ≤ Kmax) :
    x * ε ^ r * derivativeReserveFactor (ρ * ε) K r ≤ x * (ρ⁻¹ ^ r * ((Kmax + r).factorial : ℝ)) := by
  unfold derivativeReserveFactor
  have hf : ((K + r).factorial : ℝ) / (K.factorial : ℝ) ≤ ((Kmax + r).factorial : ℝ) := by
    rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos K)]
    have h1 : ((K + r).factorial : ℝ) ≤ ((Kmax + r).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have h2 : (1 : ℝ) ≤ (K.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos K
    nlinarith [Nat.cast_nonneg (α := ℝ) (Kmax + r).factorial]
  have he : x * ε ^ r * (((ρ * ε) ^ r)⁻¹ * ((K + r).factorial : ℝ) / (K.factorial : ℝ)) =
      x * (ρ⁻¹ ^ r * (((K + r).factorial : ℝ) / (K.factorial : ℝ))) := by
    rw [mul_pow, mul_inv, inv_pow]
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf
    (pow_nonneg (inv_nonneg.2 hρ.le) _)) hx

/-- **The edge constant of a row.** -/
theorem weakComparison_edge_le (c : WeakPassageInstance plan R)
    (hfloor : weakComparisonCoeffFloor R ≤ c.M) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (a b : ℝ) (hrad : plan.radius R ≤ 1)
    (v u : CompIn (c.stage i).comps) :
    ∑ d : admissibleOrders (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1)
        (1 + A.Jw * A.Nw) v u,
      (coefficientSeminorm (plan.radius R * c.D.eps i) (weakComparisonReserve R v.1) a b
        (weakComparisonDescendingCoeff c i v u d)).toReal *
        derivativeReserveFactor (plan.radius R * c.D.eps i) (weakComparisonReserve R v.1)
          (d.1 - 2) ≤
      c.D.κ c.M * weakComparisonEdgeConst plan R *
        ∑ γ : (c.stage i).fam.Γ v u, ((c.stage i).fam.identity v u γ).record.size := by
  classical
  obtain ⟨hDΛ, hq, hζ, hband⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hε : 0 < c.D.eps i := Construction.Stream.ocEpsilon_pos hΛ1
  have hr := plan.radius_pos R
  have hκ : 0 ≤ c.D.κ c.M := by
    have := weakData_kap_pos c.D hΛ1 hζ hband c.D.term
    rw [weakData_kap_terminal c.D c.D.term le_rfl, c.terminal] at this
    exact this.le
  set S := ∑ γ : (c.stage i).fam.Γ v u, ((c.stage i).fam.identity v u γ).record.size with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun γ _ => ((c.stage i).fam.identity v u γ).record.size_nonneg
  have hK := weak_comparison_reserve_le R v.1
  have hterm : ∀ d : admissibleOrders (fun v : CompIn (c.stage i).comps =>
      weakComparisonReserve R v.1) (1 + A.Jw * A.Nw) v u,
      (coefficientSeminorm (plan.radius R * c.D.eps i) (weakComparisonReserve R v.1) a b
        (weakComparisonDescendingCoeff c i v u d)).toReal *
        derivativeReserveFactor (plan.radius R * c.D.eps i) (weakComparisonReserve R v.1)
          (d.1 - 2) ≤
      weakComparisonCK R * S * c.D.κ c.M * ((plan.radius R)⁻¹ ^ (d.1 - 2) *
        ((A.Jw * A.Rw * (A.Jw * A.Nw - 1) + (d.1 - 2)).factorial : ℝ)) := by
    intro d
    have hd : 2 ≤ d.1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 d.2).1).1
    have hreg := fun γ => weakPassage_physCoeff_regular c hfloor i hi hit a b v u γ d.1 hd
    have hsem : coefficientSeminorm (plan.radius R * c.D.eps i) (weakComparisonReserve R v.1) a b
        (weakComparisonDescendingCoeff c i v u d) ≤
        ENNReal.ofReal (weakComparisonCK R * S * c.D.κ c.M * c.D.eps i ^ (d.1 - 2)) := by
      refine (coefficientSeminorm_radius_mono _ (c.D.eps i) (mul_pos hr hε).le
        (by nlinarith) _ a b _).trans ?_
      refine (CycleComparison.Error.coefficientSeminorm_finset_sum_le Finset.univ (c.D.eps i)
        hε.le (weakComparisonReserve R v.1) a b (fun γ => (c.stage i).physCoeff v u γ d.1)
        (fun γ _ t _ => (hreg γ).2.1 _ hK t)).trans ?_
      refine (Finset.sum_le_sum fun γ _ => weakPassage_physCoeff_seminorm_le c hfloor i hi hit
        a b v u γ d.1 hd _ hK).trans ?_
      rw [← ENNReal.ofReal_sum_of_nonneg fun γ _ => mul_nonneg (mul_nonneg (mul_nonneg
        (weakComparisonCK_nonneg R) ((c.stage i).fam.identity v u γ).record.size_nonneg) hκ)
        (pow_nonneg hε.le _)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [hS, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    have hx : 0 ≤ weakComparisonCK R * S * c.D.κ c.M :=
      mul_nonneg (mul_nonneg (weakComparisonCK_nonneg R) hS0) hκ
    have hreal := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hx (pow_nonneg hε.le _)) hsem
    have hdrf : 0 ≤ derivativeReserveFactor (plan.radius R * c.D.eps i)
        (weakComparisonReserve R v.1) (d.1 - 2) := by
      unfold derivativeReserveFactor
      positivity
    exact (mul_le_mul_of_nonneg_right hreal hdrf).trans
      (edge_order_term_le _ _ _ hx hε hr (d.1 - 2) _ _ hK)
  refine (Finset.sum_le_sum fun d _ => hterm d).trans ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ d : admissibleOrders (fun v : CompIn (c.stage i).comps =>
      weakComparisonReserve R v.1) (1 + A.Jw * A.Nw) v u,
      ((plan.radius R)⁻¹ ^ (d.1 - 2) *
        ((A.Jw * A.Rw * (A.Jw * A.Nw - 1) + (d.1 - 2)).factorial : ℝ)) ≤
      ∑ n ∈ Finset.range (A.Jw * A.Nw),
        (plan.radius R)⁻¹ ^ n * ((A.Jw * A.Rw * (A.Jw * A.Nw - 1) + n).factorial : ℝ) := by
    have himg := Finset.sum_image (s := Finset.univ) (f := fun n : ℕ =>
      (plan.radius R)⁻¹ ^ n * ((A.Jw * A.Rw * (A.Jw * A.Nw - 1) + n).factorial : ℝ))
      (g := fun d : admissibleOrders (fun v : CompIn (c.stage i).comps =>
        weakComparisonReserve R v.1) (1 + A.Jw * A.Nw) v u => d.1 - 2) (fun d _ d' _ hdd => by
      have h1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 d.2).1).1
      have h2 := (Finset.mem_Icc.1 (Finset.mem_filter.1 d'.2).1).1
      exact Subtype.ext (by simp only at hdd; omega))
    rw [← himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ =>
      mul_nonneg (pow_nonneg (inv_nonneg.2 hr.le) _) (Nat.cast_nonneg _)
    intro n hn
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hn
    have h := Finset.mem_Icc.1 (Finset.mem_filter.1 d.2).1
    exact Finset.mem_range.2 (by omega)
  calc weakComparisonCK R * S * c.D.κ c.M * ∑ d : admissibleOrders (fun v : CompIn
        (c.stage i).comps => weakComparisonReserve R v.1) (1 + A.Jw * A.Nw) v u,
        ((plan.radius R)⁻¹ ^ (d.1 - 2) *
          ((A.Jw * A.Rw * (A.Jw * A.Nw - 1) + (d.1 - 2)).factorial : ℝ))
      ≤ weakComparisonCK R * S * c.D.κ c.M * ∑ n ∈ Finset.range (A.Jw * A.Nw),
        (plan.radius R)⁻¹ ^ n * ((A.Jw * A.Rw * (A.Jw * A.Nw - 1) + n).factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (mul_nonneg (weakComparisonCK_nonneg R) hS0) hκ)
    _ = _ := by unfold weakComparisonEdgeConst; ring
end

end AVRegularity.Providers.WeakGen.Comparison
end
end
end
