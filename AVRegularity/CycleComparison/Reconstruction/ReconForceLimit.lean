-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.ReconForcePieces
public import AVRegularity.CycleComparison.Reconstruction.PartitionBound
public import AVRegularity.CycleComparison.Reconstruction.ReconPeriodic
import AVRegularity.CycleComparison.Reconstruction.FiniteRankIdentity
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.Reconstruction.ReconChains
import AVRegularity.CycleComparison.Reconstruction.ReconForceCarrier
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

@[expose] public noncomputable section

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The residual force carriers of the approximants are Cauchy**. A sequence whose
differences are bounded by a weighted square sum of the differences of two Galerkin sequences is
Cauchy (`cauchySeq_of_galerkin_sq_bound`); hence the carriers of the glued residual force of the
approximants are Cauchy at every time of the window (`ReconWindowAt.approxResForce_carrier_cauchy`).
-/

section
/-- **Differences bounded by Galerkin differences.** A sequence whose differences are bounded by
`M √(C (∑_u π_u⁻¹ c_A ‖A_n u - A_n' u‖² + ∑_u π_u⁻¹ c_B ‖B_n u - B_n' u‖²))`, for two convergent
families of sequences `A`, `B`, is Cauchy. -/
theorem cauchySeq_of_galerkin_sq_bound {X : Type*} [SeminormedAddCommGroup X] {κ : Type*}
    [Fintype κ] {EA EB : κ → Type*} [∀ u, SeminormedAddCommGroup (EA u)]
    [∀ u, SeminormedAddCommGroup (EB u)] (G : ℕ → X) (A : ℕ → ∀ u, EA u)
    (Bs : ℕ → ∀ u, EB u) (A₀ : ∀ u, EA u) (B₀ : ∀ u, EB u)
    (hA : ∀ u, Tendsto (fun n => A n u) atTop (𝓝 (A₀ u)))
    (hB : ∀ u, Tendsto (fun n => Bs n u) atTop (𝓝 (B₀ u))) (π : κ → ℝ) (hπ : ∀ u, 0 < π u)
    {cA cB Mv C : ℝ} (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) (hMv : 0 ≤ Mv) (hC : 0 ≤ C)
    (hG : ∀ n n', ‖G n - G n'‖ ≤ Mv * Real.sqrt (C * ((∑ u, (π u)⁻¹ * (cA * ‖A n u - A n' u‖ ^ 2))
      + ∑ u, (π u)⁻¹ * (cB * ‖Bs n u - Bs n' u‖ ^ 2)))) :
    CauchySeq G := by
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ, ∀ n, S n = ∑ u, (‖A n u - A₀ u‖ + ‖Bs n u - B₀ u‖) :=
    ⟨_, fun _ => rfl⟩
  have hS0 : ∀ n, 0 ≤ S n := fun n => (hS n).symm ▸
    Finset.sum_nonneg fun u _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∑ u, (π u)⁻¹ * (cA + cB) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := hP ▸ Finset.sum_nonneg fun u _ =>
    mul_nonneg (inv_nonneg.2 (hπ u).le) (add_nonneg hcA hcB)
  have hSt : Tendsto S atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset κ) fun u _ =>
      (tendsto_iff_norm_sub_tendsto_zero.1 (hA u)).add
        (tendsto_iff_norm_sub_tendsto_zero.1 (hB u))
    simp only [add_zero, Finset.sum_const_zero] at h
    exact h.congr fun n => (hS n).symm
  refine cauchySeq_of_dist_le_add G (fun n => Mv * Real.sqrt (C * P) * S n) ?_ fun n n' => ?_
  · simpa using hSt.const_mul (Mv * Real.sqrt (C * P))
  rw [dist_eq_norm]
  refine (hG n n').trans ?_
  -- the bound of each difference by the distances to the limits
  have hab : ∀ u, ‖A n u - A n' u‖ + ‖Bs n u - Bs n' u‖ ≤ S n + S n' := fun u => by
    have h1 := norm_sub_le_norm_sub_add_norm_sub' (A n u) (A₀ u) (A n' u)
    have h2 := norm_sub_le_norm_sub_add_norm_sub' (Bs n u) (B₀ u) (Bs n' u)
    have hu : ∀ m : ℕ, ‖A m u - A₀ u‖ + ‖Bs m u - B₀ u‖ ≤ S m := fun m => (hS m).symm ▸
      Finset.single_le_sum (f := fun u => ‖A m u - A₀ u‖ + ‖Bs m u - B₀ u‖)
        (fun u _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ u)
    calc ‖A n u - A n' u‖ + ‖Bs n u - Bs n' u‖
        ≤ (‖A n u - A₀ u‖ + ‖A n' u - A₀ u‖) + (‖Bs n u - B₀ u‖ + ‖Bs n' u - B₀ u‖) :=
          add_le_add h1 h2
      _ = (‖A n u - A₀ u‖ + ‖Bs n u - B₀ u‖) + (‖A n' u - A₀ u‖ + ‖Bs n' u - B₀ u‖) := by ring
      _ ≤ S n + S n' := add_le_add (hu n) (hu n')
  have hsum : (∑ u, (π u)⁻¹ * (cA * ‖A n u - A n' u‖ ^ 2)) +
      ∑ u, (π u)⁻¹ * (cB * ‖Bs n u - Bs n' u‖ ^ 2) ≤ P * (S n + S n') ^ 2 := by
    rw [← Finset.sum_add_distrib, hP, Finset.sum_mul]
    refine Finset.sum_le_sum fun u _ => ?_
    have hw := inv_nonneg.2 (hπ u).le
    have ha := norm_nonneg (A n u - A n' u)
    have hb := norm_nonneg (Bs n u - Bs n' u)
    have hsq : ‖A n u - A n' u‖ ^ 2 ≤ (S n + S n') ^ 2 :=
      pow_le_pow_left₀ ha ((le_add_of_nonneg_right hb).trans (hab u)) 2
    have hsq' : ‖Bs n u - Bs n' u‖ ^ 2 ≤ (S n + S n') ^ 2 :=
      pow_le_pow_left₀ hb ((le_add_of_nonneg_left ha).trans (hab u)) 2
    calc (π u)⁻¹ * (cA * ‖A n u - A n' u‖ ^ 2) + (π u)⁻¹ * (cB * ‖Bs n u - Bs n' u‖ ^ 2)
        ≤ (π u)⁻¹ * (cA * (S n + S n') ^ 2) + (π u)⁻¹ * (cB * (S n + S n') ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hcA) hw)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq' hcB) hw)
      _ = (π u)⁻¹ * (cA + cB) * (S n + S n') ^ 2 := by ring
  have hroot : Real.sqrt (C * ((∑ u, (π u)⁻¹ * (cA * ‖A n u - A n' u‖ ^ 2)) +
      ∑ u, (π u)⁻¹ * (cB * ‖Bs n u - Bs n' u‖ ^ 2))) ≤ Real.sqrt (C * P) * (S n + S n') := by
    rw [← Real.sqrt_sq (add_nonneg (hS0 n) (hS0 n')), ← Real.sqrt_mul (mul_nonneg hC hP0)]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hsum hC
  calc Mv * Real.sqrt (C * ((∑ u, (π u)⁻¹ * (cA * ‖A n u - A n' u‖ ^ 2)) +
        ∑ u, (π u)⁻¹ * (cB * ‖Bs n u - Bs n' u‖ ^ 2)))
      ≤ Mv * (Real.sqrt (C * P) * (S n + S n')) := mul_le_mul_of_nonneg_left hroot hMv
    _ = Mv * Real.sqrt (C * P) * S n + Mv * Real.sqrt (C * P) * S n' := by ring

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

/-- **The glued residual force carriers of the approximants are Cauchy** at every time of the
window. -/
theorem ReconWindowAt.approxResForce_carrier_cauchy
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (hSb : 0 ≤ Sb) {Acl r m' kres Nχ : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (hk : Acl + 2 + r + Nc + 1 ≤ kres) (hNχ : m' + 1 ≤ Nχ) (hNχ' : kres + 1 ≤ Nχ)
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ Nc →
      ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ Acl + 2 + r →
        schurEnergyJet π (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp /
            ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2))
          Llift j (Cc k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ρ / ocEpsilon q Λ (m - 1)) ^ (n - m'' + j)))
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (hkres : kres ≤ kc) (hmr : m' + 1 ≤ r₀) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r)
    (v : ι) :
    CauchySeq (fun n => carrierOf (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B
        ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v)) := by
  have hπ := w.hcs.mass_pos
  have hwW : 0 ≤ factorialWeightMax ρ (kc + 1 + (Nc + D)) :=
    (factorialWeight_nonneg _ 0).trans (factorialWeight_le_max _ (0 : Fin (kc + 1 + (Nc + D) + 1)))
  have hwF : 0 ≤ factorialWeightMax ρ kc :=
    (factorialWeight_nonneg _ 0).trans (factorialWeight_le_max _ (0 : Fin (kc + 1)))
  have hCF : 0 ≤ (2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m' (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) := by
    have := tailForceConst_nonneg H Nc D Acl r m' (pulseChartD Nχ)
    have := liftForceConst_nonneg H Nc Acl r kres Nχ (pulseChartD Nχ)
    positivity
  refine cauchySeq_of_galerkin_sq_bound _ (fun n u => galerkinProj n (W u t))
    (fun n u => galerkinProj n (Fc u t)) (fun u => W u t) (fun u => Fc u t)
    (fun u => galerkinProj_tendsto (W u t)) (fun u => galerkinProj_tendsto (Fc u t)) π hπ hwW hwF
    (Real.sqrt_nonneg (π v / factorialWeightMin rs (Kc v))) hCF fun n n' => ?_
  have hm := w.approxResForce_carrier_sub_mass_le hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr Vc Vn
    hch hkres hmr n n' ht hrs hrse Kc hKr
  refine (norm_le_sqrt_massNormSq (E := h) Kc hrs π hπ
    (fun u => carrierOf (Kc u) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x u) -
      carrierOf (Kc u) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
        tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n') (Vn n') t x u)) v).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) (Real.sqrt_nonneg _)
end

/-! **The lifted pieces of the residual force of the approximants at one time**.
The partition weights are bounded by one and their derivatives by `|C_part/τ|`, both supported in
the pulse windows (`ReconWindowAt.abs_weight_le`, `ReconWindowAt.abs_deriv_weight_le`). At every time
of the window, the carriers of the partition term `∑_k ϖ_k' 𝒯_k a_n` of the approximants are
Cauchy (`ReconWindowAt.partition_carrier_cauchy`) and bounded uniformly in `n`
(`ReconWindowAt.partition_carrier_le`); the carriers of the glued lift of the commutator remainder
`e_n` tend to zero when the jets of `e_n` do (`ReconWindowAt.defectLift_carrier_tendsto`) and are
bounded by its jets (`ReconWindowAt.defectLift_carrier_le`). -/

section
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

/-- The partition weights vanish off the pulse windows. -/
theorem ReconWindowAt.weight_window
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀) :
    ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ t ∈ Set.Icc tp (tp + Tobs), F.weight (pp k) t ≠ 0 →
      t ∈ ocPulseWindow α q Λ m k :=
  fun k hk t _ hw => w.hpart.2.2.2.1 k hk t hw

/-- The partition weights are bounded by one on the window. -/
theorem ReconWindowAt.abs_weight_le
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀) :
    ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ t ∈ Set.Icc tp (tp + Tobs), |F.weight (pp k) t| ≤ 1
        := fun k hk t ht => by
  rw [abs_of_nonneg (w.hpart.1 k hk t)]
  exact (Finset.single_le_sum (f := fun k => F.weight (pp k) t) (fun k hk => w.hpart.1 k hk t)
    hk).trans_eq (w.hpart.2.2.1 t ht)

/-- The derivatives of the partition weights vanish off the pulse windows. -/
theorem ReconWindowAt.deriv_weight_window
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀) :
    ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ t ∈ Set.Icc tp (tp + Tobs), deriv (F.weight (pp k))
        t ≠ 0 →
      t ∈ ocPulseWindow α q Λ m k :=
  fun k hk _ _ hw => mem_of_deriv_ne_zero (S := ocPulseWindow α q Λ m k) isClosed_Icc
    (w.hpart.2.2.2.1 k hk) hw

/-- The derivatives of the partition weights are bounded by `|C_part/τ|`. -/
theorem ReconWindowAt.abs_deriv_weight_le
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀) :
    ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ t ∈ Set.Icc tp (tp + Tobs), |deriv (F.weight (pp k))
        t| ≤ |Cpart / ocTau α q Λ m| :=
  fun k hk t _ => (w.hpart.2.2.2.2.1 k hk t).trans (le_abs_self _)

/-- **The partition term carriers of the approximants are Cauchy** at every time of the window. -/
theorem ReconWindowAt.partition_carrier_cauchy
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {r : ℕ} (hrK : r ≤ Klift) (hrL : r ≤ Llift) (hrW : Nc + r + 2 ≤ kc + 1 + (Nc + D))
    {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) (v : ι) :
    CauchySeq (fun n => carrierOf (Kc v) (fun x =>
      gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => deriv (F.weight (pp k))) (ocEll q Λ m
          ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) t x v)) := by
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  obtain ⟨M, hM0, hM⟩ := w.gluedPiece_carrier_le hrK hrL Kc hKr
  obtain ⟨Ca, hCa0, hCa⟩ := coarseTraj_sub_iteratedFDeriv_le (h := h) hrW
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ, ∀ n, S n = ∑ u, ‖galerkinProj n (W u t) - W u t‖ :=
    ⟨_, fun _ => rfl⟩
  have hS0 : ∀ n, 0 ≤ S n := fun n => (hS n).symm ▸ Finset.sum_nonneg fun u _ => norm_nonneg _
  have hSt : Tendsto S atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset ι) fun u _ =>
      tendsto_iff_norm_sub_tendsto_zero.1 (galerkinProj_tendsto (W u t))
    simp only [Finset.sum_const_zero] at h
    exact h.congr fun n => (hS n).symm
  obtain ⟨Cv, hCv⟩ : ∃ Cv : ℝ, Cv = (Fintype.card (JetIndex2 (Kc v)) : ℝ) *
      (|Cpart / ocTau α q Λ m| * M * Ca) := ⟨_, rfl⟩
  refine cauchySeq_of_dist_le_add _ (fun n => Cv * S n) (by simpa using hSt.const_mul Cv)
    fun n n' => ?_
  rw [dist_eq_norm]
  have hsm := fun n₀ : ℕ => w.gluedPiece_smooth hrK hrL (fun k => deriv (F.weight (pp k)))
      (w.deriv_weight_window)
    (coarseTraj n₀ W) ht ((coarseTraj_contDiff n₀ W t).of_le (by exact_mod_cast le_top))
    (coarseTraj_periodic n₀ W t) Kc hKr
  rw [carrierOf_sub (Kc v) ((hsm n).1 v) ((hsm n').1 v) ((hsm n).2 v) ((hsm n').2 v)]
  have hdiff : (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => deriv (F.weight
      (pp k))) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) t x v -
      gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => deriv (F.weight (pp k))) (ocEll q Λ m
          ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n'
              W) t x v) = fun x =>
      gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => deriv (F.weight (pp k))) (ocEll q Λ m
          ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (fun s y =>
              coarseTraj n W s y - coarseTraj n' W s y) t x v := by
    funext x
    rw [gluedLift_sub_input_oc hφ hℓ _ _ _ _ _ _ _ _ (coarseTraj n W) (coarseTraj n' W) (t := t)
      ((coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top))
      ((coarseTraj_contDiff n' W t).of_le (by exact_mod_cast le_top)) x]
    rfl
  rw [hdiff]
  have hB : ∀ u, ‖galerkinProj n (W u t) - galerkinProj n' (W u t)‖ ≤ S n + S n' := fun u => by
    have h1 := norm_sub_le_norm_sub_add_norm_sub' (galerkinProj n (W u t)) (W u t)
      (galerkinProj n' (W u t))
    have hu : ∀ m₀ : ℕ, ‖galerkinProj m₀ (W u t) - W u t‖ ≤ S m₀ := fun m₀ => (hS m₀).symm ▸
      Finset.single_le_sum (f := fun u => ‖galerkinProj m₀ (W u t) - W u t‖)
        (fun u _ => norm_nonneg _) (Finset.mem_univ u)
    exact h1.trans (add_le_add (hu n) (hu n'))
  have hb := hM (fun k => deriv (F.weight (pp k))) |Cpart / ocTau α q Λ m| (abs_nonneg _)
      (w.deriv_weight_window)
    (fun s y => coarseTraj n W s y - coarseTraj n' W s y) t ht
    (fun k hk => w.abs_deriv_weight_le k hk t ht)
    (((coarseTraj_contDiff n W t).sub (coarseTraj_contDiff n' W t)).of_le
      (by exact_mod_cast le_top))
    (fun l x => by
      show coarseTraj n W t (x + latticeShift l) - coarseTraj n' W t (x + latticeShift l) =
        coarseTraj n W t x - coarseTraj n' W t x
      exact congrArg₂ (· - ·) (coarseTraj_periodic n W t l x) (coarseTraj_periodic n' W t l x))
    (Ca * (S n + S n')) (mul_nonneg hCa0 (add_nonneg (hS0 n) (hS0 n')))
    (hCa n n' W t (add_nonneg (hS0 n) (hS0 n')) hB) v
  refine hb.trans (le_of_eq ?_)
  rw [hCv]
  ring

/-- **The partition term carriers of the approximants are bounded uniformly in `n`.** -/
theorem ReconWindowAt.partition_carrier_le
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {r : ℕ} (hrK : r ≤ Klift) (hrL : r ≤ Llift) (hrW : Nc + r + 2 ≤ kc + 1 + (Nc + D))
    (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc tp (tp + Tobs) → ∀ CW : ℝ, 0 ≤ CW → (∀ u, ‖W u
        t‖ ≤ CW) →
      ∀ v, ‖carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k =>
          deriv (F.weight (pp k))) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) t x v)‖ ≤
        (Fintype.card (JetIndex2 (Kc v)) : ℝ) * (|Cpart / ocTau α q Λ m| * M * CW) := by
  obtain ⟨M, hM0, hM⟩ := w.gluedPiece_carrier_le hrK hrL Kc hKr
  obtain ⟨Ca, hCa0, hCa⟩ := coarseTraj_iteratedFDeriv_le (h := h) hrW
  refine ⟨M * Ca, mul_nonneg hM0 hCa0, fun n t ht CW hCW hW v => ?_⟩
  refine (hM (fun k => deriv (F.weight (pp k))) |Cpart / ocTau α q Λ m| (abs_nonneg _)
      (w.deriv_weight_window)
    (coarseTraj n W) t ht (fun k hk => w.abs_deriv_weight_le k hk t ht)
    ((coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top)) (coarseTraj_periodic n W t)
    (Ca * CW) (mul_nonneg hCa0 hCW) (hCa n W t hCW hW) v).trans (le_of_eq ?_)
  ring

/-- **The commutator remainder of an approximant is smooth and periodic** at a time of the
window. -/
theorem ReconWindowAt.defectRemainder_smooth
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {N : ℕ} (hN : N + 1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc tp (tp + Tobs)) :
    ContDiff ℝ (N : ℕ∞) ((defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W aRep) t) ∧ IsZ2Periodic ((defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD
        CE Jm W aRep) t) :=
  ⟨defectRemainder_contDiff n W aRep (fun d => (w.hcs.AD_smooth d t ht).of_le
      (WithTop.coe_le_coe.mpr (by exact_mod_cast hN)))
    (fun r hr v u d => (w.hcs.CE_smooth r hr v u d t ht).of_le
      (WithTop.coe_le_coe.mpr (by exact_mod_cast hN)))
    ((w.hcs.drift_smooth t ht).of_le (by exact_mod_cast le_top)),
  defectRemainder_periodic n W aRep (w.hrep t ht) (fun d => w.hcs.AD_per d t ht)
    (fun r hr v u d => w.hcs.CE_per r hr v u d t ht) (w.hcs.drift_per t ht)⟩

/-- **The glued lift carriers of the commutator remainders are bounded by their jets.** -/
theorem ReconWindowAt.defectLift_carrier_le
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {r : ℕ} (hrK : r ≤ Klift) (hrL : r ≤ Llift)
    (hNco : Nc + r + 1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
    (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc tp (tp + Tobs) → ∀ CE' : ℝ, 0 ≤ CE' →
      (∀ j ≤ Nc + r, ∀ x, ‖iteratedFDeriv ℝ j ((defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H
          AD CE Jm W aRep) t) x‖ ≤ CE') →
      ∀ v, ‖carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k =>
          F.weight (pp k)) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W
              aRep) t x v)‖ ≤
        (Fintype.card (JetIndex2 (Kc v)) : ℝ) * (M * CE') := by
  obtain ⟨M, hM0, hM⟩ := w.gluedPiece_carrier_le hrK hrL Kc hKr
  refine ⟨M, hM0, fun n t ht CE' hCE' hjet v => ?_⟩
  obtain ⟨hs, hp⟩ := w.defectRemainder_smooth hNco n ht
  refine (hM (fun k => F.weight (pp k)) 1 zero_le_one (w.weight_window) (defectRemainder n
      (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W aRep) t ht
    (fun k hk => w.abs_weight_le k hk t ht) hs hp CE' hCE' hjet v).trans (le_of_eq ?_)
  ring

/-- **The glued lift carriers of the commutator remainders tend to zero** at a time of the window
at which the jets of the remainders do. -/
theorem ReconWindowAt.defectLift_carrier_tendsto
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {r : ℕ} (hrK : r ≤ Klift) (hrL : r ≤ Llift)
    (hNco : Nc + r + 1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
    (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs))
    (hE0 : ∀ ε > 0, ∀ᶠ n in atTop, ∀ j ≤ Nc + r, ∀ x,
      ‖iteratedFDeriv ℝ j ((defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W aRep) t) x‖ ≤ ε) (v : ι) :
    Tendsto (fun n => carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun
        k => F.weight (pp k)) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W
              aRep) t x v)) atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := w.defectLift_carrier_le hrK hrL hNco Kc hKr
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (Fintype.card (JetIndex2 (Kc v)) : ℝ) * M := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ mul_nonneg (Nat.cast_nonneg _) hM0
  have hδ : 0 < ε / (c + 1) := div_pos hε (by linarith)
  filter_upwards [hE0 (ε / (c + 1)) hδ] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  refine (hM n t ht _ hδ.le hn v).trans_lt ?_
  have h1 : (Fintype.card (JetIndex2 (Kc v)) : ℝ) * (M * (ε / (c + 1))) = c * (ε / (c + 1)) := by
    rw [hc]
    ring
  rw [h1]
  calc c * (ε / (c + 1)) < (c + 1) * (ε / (c + 1)) :=
        mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := by field_simp
end

/-! **Time measurability of the partition term carriers**. The carriers of the
partition term `∑_k ϖ_k' 𝒯_k a_n` of the approximants are a.e. strongly measurable on the window
(`ReconWindowAt.partition_carrier_aesm`): their tested values are measurable in the clamped time
(`glued_pulseLift_joint_measurable` with the derivative weights), hence so are the carriers
(`Coarse.aestronglyMeasurable_of_weak`). -/

section
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

/-- **The partition term carriers of an approximant are a.e. strongly measurable on the
window.** -/
theorem ReconWindowAt.partition_carrier_aesm
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (n : ℕ) {r : ℕ} (hrK : r ≤ Klift) (hrL : r ≤ Llift)
    (hcm : ∀ r', Measurable fun s => coarseCoeff n W r'
      (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s))
    (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) (v : ι) :
    AEStronglyMeasurable (fun s => carrierOf (Kc v) (fun x =>
      gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => deriv (F.weight (pp k))) (ocEll q Λ m
          ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) s x v)) (volume.restrict (Set.Icc tp (tp + Tobs))) := by
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ1
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of w.hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hℓ).symm
  have htAZ : tp ≤ tp + Tobs := by linarith [w.hTobs]
  have hcm' : ∀ r', Measurable fun s : Set.Icc tp (tp + Tobs) => coarseCoeff n W r' s :=
    fun r' => by
      have h1 := (hcm r').comp (measurable_subtype_coe (p := fun s => s ∈ Set.Icc tp (tp + Tobs)))
      simpa only [Function.comp_def, Set.projIcc_val] using h1
  have hχ : ∀ k : ℤ, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 =>
      ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) p.1 p.2 := fun k =>
    Charts.contDiff_ocChart_joint hφ α q Λ m (ocPulseChartIndex α q Λ m k)
  have hψc : ∀ k : ℤ, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 =>
      ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) p.1 p.2 := fun k =>
    Charts.contDiff_ocChartInv_joint hφ α q Λ m (ocPulseChartIndex α q Λ m k)
  have hphys : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ τ ∈ Set.Icc
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2),
      ocEll q Λ m ν ^ 2 * τ ∈ Set.Icc tp (tp + Tobs) := fun _ _ _ hτ => physTime_mem_obs hc0 hτ
  have hwin' : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ t ∈ Set.Icc tp (tp + Tobs),
      deriv (F.weight (pp k)) t ≠ 0 → (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) :=
    fun k hk t ht hw => cellTime_mem_pulseLiftWindow hc0 (w.deriv_weight_window k hk t ht hw) ht
  have hD := glued_pulseLift_joint_measurable (ocObsPulses α q Λ m tp (tp + Tobs))
    (fun k : ℤ => max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
    (fun k : ℤ => min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2)
    htAZ hphys (χs := fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (ψs := fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) hχ hψc
    (fun k => deriv (F.weight (pp k))) (fun k _ => measurable_deriv (F.weight (pp k))) hwin'
    (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B ρ
      (ρ / ocEpsilon q Λ (m - 1)) k (F.fiber (pp k) (actual (pp k))))
          w.hsetting Cc w.hseq
    (coarseTraj n W) (jointlyMeas_coarseTraj n W hcm')
    (fun s _ => (coarseTraj_contDiff n W s).of_le (order_natCast_le_top _)) ρ
    (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ)
  refine Coarse.aestronglyMeasurable_of_weak fun ψ hψ hψp => ?_
  have hjoint : Measurable fun p : ℝ × Vec 2 => inner ℝ
      (gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => deriv (F.weight (pp k))) (ocEll q Λ
          m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) (Set.projIcc tp (tp + Tobs) htAZ p.1) p.2 v)
      (ψ p.2) :=
    Measurable.inner ((measurable_pi_apply v).comp hD) (hψ.continuous.measurable.comp
      measurable_snd)
  have hmeas := (hjoint.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict AVenhance.unitCube)).measurable
  refine hmeas.aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
  obtain ⟨hsm, hpm⟩ := w.gluedPiece_smooth hrK hrL (fun k => deriv (F.weight (pp k)))
      (w.deriv_weight_window)
    (coarseTraj n W) hs ((coarseTraj_contDiff n W s).of_le (by exact_mod_cast le_top))
    (coarseTraj_periodic n W s) Kc hKr
  dsimp only
  rw [projIcc_val_of_mem htAZ hs, carrierOf_eq (Kc v) (hsm v) (hpm v)]
  unfold Coarse.tval cellInner
  refine integral_congr_ae ?_
  filter_upwards [periodicHk_value_ae (Kc v) _ (hsm v) (hpm v)] with x hx
  rw [hx]
end

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The residual force carriers of the approximants**. At every time of the window
the carrier of the forcing residual `approxForce … n` of the `n`-th approximant is the sum of the
carriers of the glued residual force, of the glued lift of the commutator remainder and of the
partition term (`ReconWindowAt.approxForce_carrier_eq`); it is Cauchy in `n` when the jets of the
commutator remainders tend to zero (`ReconWindowAt.approxForce_carrier_cauchy`), and its
mass-weighted norm is bounded uniformly in `n` by the densities of the retained field and of the
flux and by bounds of the jets of the commutator remainder and of the norms of the retained field
(`ReconWindowAt.approxForce_carrier_mass_le`). -/

/-- The square of a sum of three terms is at most three times the sum of the squares. -/
theorem sq_add_three_le (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

section Mass

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, CompleteSpace (E i)]

/-- **The mass-weighted norm of a sum of three carrier families.** -/
theorem massNormSq_le_of_eq_add3 (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Q A B C : ∀ i, TorusHk (K i) (E i)) (hQ : ∀ i, Q i = A i + B i + C i) {X b c : ℝ}
    (hA : massNormSq ρ π (fun i => (A i).val) ≤ X)
    (hB : Real.sqrt (massNormSq ρ π (fun i => (B i).val)) ≤ b)
    (hC : Real.sqrt (massNormSq ρ π (fun i => (C i).val)) ≤ c) :
    massNormSq ρ π (fun i => (Q i).val) ≤ 3 * (X + b ^ 2 + c ^ 2) := by
  have hQ' : Q = A + B + C := funext hQ
  have hn : ‖massWeightedCarrierCLM K ρ π Q‖ ≤ ‖massWeightedCarrierCLM K ρ π A‖ +
      ‖massWeightedCarrierCLM K ρ π B‖ + ‖massWeightedCarrierCLM K ρ π C‖ := by
    rw [hQ', map_add, map_add]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  rw [← massWeightedCarrierCLM_normSq K ρ π hπ Q]
  rw [← massWeightedCarrierCLM_normSq K ρ π hπ A] at hA
  rw [← massWeightedCarrierCLM_norm K ρ π hπ B] at hB
  rw [← massWeightedCarrierCLM_norm K ρ π hπ C] at hC
  have hB2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
  have hC2 := pow_le_pow_left₀ (norm_nonneg _) hC 2
  refine (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans ((sq_add_three_le _ _ _).trans ?_)
  have := add_le_add (add_le_add hA hB2) hC2
  linarith

end Mass

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

/-- **The carrier of the forcing residual of an approximant is the sum of the carriers of its
three pieces** at a time of the window. -/
theorem ReconWindowAt.approxForce_carrier_eq
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r m' : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (hNco : Nc + r + 1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) (v : ι) :
    carrierOf (Kc v) (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v t x) =
      carrierOf (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
          tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v) +
        carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight
            (pp k)) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W
              aRep) t x v) +
        carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => deriv
            (F.weight (pp k))) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) t x v) := by
  have hrK : r ≤ Klift := by omega
  obtain ⟨h12s, h12p⟩ := w.approxResForce_smooth hAcl hK hrL hord Vc Vn hch n ht Kc hKr
  obtain ⟨hEs, hEp⟩ := w.defectRemainder_smooth (N := Nc + r) hNco n ht
  obtain ⟨h3s, h3p⟩ := w.gluedPiece_smooth hrK hrL (fun k => F.weight (pp k)) (w.weight_window)
      (defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W aRep) ht
      hEs hEp
    Kc hKr
  obtain ⟨h4s, h4p⟩ := w.gluedPiece_smooth hrK hrL (fun k => deriv (F.weight (pp k)))
      (w.deriv_weight_window)
    (coarseTraj n W) ht ((coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top))
    (coarseTraj_periodic n W t) Kc hKr
  have e : (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp
      + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v t x) = fun x =>
      (reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
          tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v + gluedLift
              (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W
              aRep) t x v) + gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => deriv
              (F.weight (pp k))) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) t x v := rfl
  rw [e, carrierOf_add (Kc v) ((h12s v).add (h3s v)) (h4s v) (fun l x => by
      show reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
          tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t (x + latticeShift l) v
              + gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k)) (ocEll q Λ
              m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W
              aRep) t (x + latticeShift l) v =
        reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
          tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v + gluedLift
              (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W
              aRep) t x v
      exact congrArg₂ (· + ·) (h12p v l x) (h3p v l x)) (h4p v),
    carrierOf_add (Kc v) (h12s v) (h3s v) (h12p v) (h3p v)]

/-- **The forcing residual carriers of the approximants are Cauchy** at a time of the window at
which the jets of the commutator remainders tend to zero. -/
theorem ReconWindowAt.approxForce_carrier_cauchy
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (hSb : 0 ≤ Sb) {Acl r m' kres Nχ : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (hk : Acl + 2 + r + Nc + 1 ≤ kres) (hNχ : m' + 1 ≤ Nχ) (hNχ' : kres + 1 ≤ Nχ)
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ Nc →
      ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ Acl + 2 + r →
        schurEnergyJet π (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp /
            ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2))
          Llift j (Cc k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ρ / ocEpsilon q Λ (m - 1)) ^ (n - m'' + j)))
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (hkres : kres ≤ kc) (hmr : m' + 1 ≤ r₀)
    (hrW : Nc + r + 2 ≤ kc + 1 + (Nc + D))
    (hNco : Nc + r + 1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
    {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m)
    (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r)
    (hE0 : ∀ ε > 0, ∀ᶠ n in atTop, ∀ j ≤ Nc + r, ∀ x,
      ‖iteratedFDeriv ℝ j ((defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W aRep) t) x‖ ≤ ε) (v : ι) :
    CauchySeq (fun n => carrierOf (Kc v) (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v t x)) := by
  have hrK : r ≤ Klift := by omega
  have e : (fun n => carrierOf (Kc v) (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v t x)) = fun n =>
      carrierOf (Kc v) (fun x => reconResForce α q Λ m (Φ (m - 1)) hφ ν B ρ
          tp (tp + Tobs) (fun k => F.weight (pp k)) H Nc Acl (Vc n) (Vn n) t x v) +
        carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight
            (pp k)) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W
              aRep) t x v) +
        carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => deriv
            (F.weight (pp k))) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) t x v) :=
    funext fun n => w.approxForce_carrier_eq hAcl hK hrL hord hNco Vc Vn hch n ht Kc hKr v
  rw [e]
  exact ((w.approxResForce_carrier_cauchy hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr Vc Vn hch
    hkres hmr ht hrs hrse Kc hKr v).add (w.defectLift_carrier_tendsto hrK hrL hNco Kc hKr ht hE0
      v).cauchySeq).add (w.partition_carrier_cauchy hrK hrL hrW ht Kc hKr v)

/-- **The uniform bound of the forcing residual carriers of the approximants.** -/
theorem ReconWindowAt.approxForce_carrier_mass_le
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (hSb : 0 ≤ Sb) {Acl r m' kres Nχ : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (hk : Acl + 2 + r + Nc + 1 ≤ kres) (hNχ : m' + 1 ≤ Nχ) (hNχ' : kres + 1 ≤ Nχ)
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ Nc →
      ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ Acl + 2 + r →
        schurEnergyJet π (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp /
            ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2))
          Llift j (Cc k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ρ / ocEpsilon q Λ (m - 1)) ^ (n - m'' + j)))
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (hkres : kres ≤ kc) (hmr : m' + 1 ≤ r₀)
    (hrW : Nc + r + 2 ≤ kc + 1 + (Nc + D))
    (hNco : Nc + r + 1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) :
    ∃ C₃ C₄ : ℝ, 0 ≤ C₃ ∧ 0 ≤ C₄ ∧ ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc tp (tp + Tobs) → ∀ CE' CW : ℝ, 0 ≤
        CE' →
      0 ≤ CW → (∀ j ≤ Nc + r, ∀ x, ‖iteratedFDeriv ℝ j ((defectRemainder n (streamVel (Φ (m - 1)))
          (Nc + D) H AD CE Jm W aRep) t) x‖ ≤ CE') →
      (∀ u, ‖W u t‖ ≤ CW) →
      massNormSq (E := h) (K := Kc) rs π
          (fun v => (carrierOf (Kc v) (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v t x)).val) ≤
        3 * ((2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m' (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) *
          ((∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
            (W v t).val) +
          massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v t).val)) + (C₃ * CE') ^ 2 + (C₄ *
                CW) ^ 2) := by
  have hπ := w.hcs.mass_pos
  have hrK : r ≤ Klift := by omega
  obtain ⟨M₃, hM₃, hM₃b⟩ := w.defectLift_carrier_le hrK hrL hNco Kc hKr
  obtain ⟨M₄, hM₄, hM₄b⟩ := w.partition_carrier_le hrK hrL hrW Kc hKr
  obtain ⟨Tn, hTn⟩ : ∃ Tn : ℝ, Tn = ‖massWeightedCarrierCLM (E := h) Kc rs π‖ := ⟨_, rfl⟩
  have hTn0 : 0 ≤ Tn := by rw [hTn]; exact norm_nonneg (massWeightedCarrierCLM (E := h) Kc rs π)
  obtain ⟨cC, hcC⟩ : ∃ cC : ℝ, cC = ∑ v, (Fintype.card (JetIndex2 (Kc v)) : ℝ) := ⟨_, rfl⟩
  have hcC0 : 0 ≤ cC := hcC ▸ Finset.sum_nonneg fun v _ => Nat.cast_nonneg _
  have hcv : ∀ v, (Fintype.card (JetIndex2 (Kc v)) : ℝ) ≤ cC := fun v => hcC ▸
    Finset.single_le_sum (f := fun v => (Fintype.card (JetIndex2 (Kc v)) : ℝ))
      (fun v _ => Nat.cast_nonneg _) (Finset.mem_univ v)
  refine ⟨Tn * (cC * M₃), Tn * (cC * (|Cpart / ocTau α q Λ m| * M₄)),
    mul_nonneg hTn0 (mul_nonneg hcC0 hM₃),
    mul_nonneg hTn0 (mul_nonneg hcC0 (mul_nonneg (abs_nonneg _) hM₄)),
    fun n t ht CE' CW hCE' hCW hE hW => ?_⟩
  have h12 := w.approxResForce_carrier_mass_le hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr Vc Vn hch
    hkres hmr n ht hrs hrse Kc hKr
  have h3 := sqrt_massNormSq_le_of_norm_le Kc rs π hπ
    (fun v => carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k =>
        F.weight (pp k)) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
              (defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W
              aRep) t x v))
    (mul_nonneg hcC0 (mul_nonneg hM₃ hCE')) fun v =>
      (hM₃b n t ht CE' hCE' hE v).trans
        (mul_le_mul_of_nonneg_right (hcv v) (mul_nonneg hM₃ hCE'))
  have h4 := sqrt_massNormSq_le_of_norm_le Kc rs π hπ
    (fun v => carrierOf (Kc v) (fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k =>
        deriv (F.weight (pp k))) (ocEll q Λ m ν ^ 2)
          ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) Nc H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)) (coarseTraj n
              W) t x v))
    (mul_nonneg hcC0 (mul_nonneg (mul_nonneg (abs_nonneg _) hM₄) hCW)) fun v =>
      (hM₄b n t ht CW hCW hW v).trans
        (mul_le_mul_of_nonneg_right (hcv v) (mul_nonneg (mul_nonneg (abs_nonneg _) hM₄) hCW))
  rw [← hTn] at h3 h4
  exact massNormSq_le_of_eq_add3 Kc rs π hπ _ _ _ _
    (fun v => w.approxForce_carrier_eq hAcl hK hrL hord hNco Vc Vn hch n ht Kc hKr v) h12
    (h3.trans_eq (by ring)) (h4.trans_eq (by ring))

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The residual force of the physical reconstruction**. The components of the
forcing residuals of the approximants are smooth and periodic at the times of the window
(`ReconWindowAt.approxForce_smooth`), their carriers are a.e. strongly measurable on the window
(`ReconWindowAt.approxForce_carrier_aesm`, from the tested measurability
`approxForce_tested_measurable` and weak measurability), Cauchy and uniformly bounded
(`ReconWindowAt.approxForce_carrier_cauchy`, `ReconWindowAt.approxForce_carrier_mass_le`); hence
they converge at every window time to a residual force `qq`, square integrable in time, with a
uniform bound, and the distances are bounded by functions whose integrals tend to zero
(`ReconWindowAt.force_limit`, by `exists_residual_limit`). -/

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

/-- **The components of the forcing residual of an approximant are smooth and periodic** at a
time of the window. -/
theorem ReconWindowAt.approxForce_smooth
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r m' : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (hNco : Nc + r + 1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc tp (tp + Tobs)) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) :
    (∀ v, ContDiff ℝ (Kc v : ℕ∞) (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v t x)) ∧
    (∀ v, IsZ2Periodic (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v t x)) := by
  have hrK : r ≤ Klift := by omega
  obtain ⟨h12s, h12p⟩ := w.approxResForce_smooth hAcl hK hrL hord Vc Vn hch n ht Kc hKr
  obtain ⟨hEs, hEp⟩ := w.defectRemainder_smooth (N := Nc + r) hNco n ht
  obtain ⟨h3s, h3p⟩ := w.gluedPiece_smooth hrK hrL (fun k => F.weight (pp k)) (w.weight_window)
      (defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W aRep) ht
      hEs hEp
    Kc hKr
  obtain ⟨h4s, h4p⟩ := w.gluedPiece_smooth hrK hrL (fun k => deriv (F.weight (pp k)))
      (w.deriv_weight_window)
    (coarseTraj n W) ht ((coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top))
    (coarseTraj_periodic n W t) Kc hKr
  exact ⟨fun v => ((h12s v).add (h3s v)).add (h4s v), fun v l x =>
    congrArg₂ (· + ·) (congrArg₂ (· + ·) (h12p v l x) (h3p v l x)) (h4p v l x)⟩

/-- **The forcing residual carriers of an approximant are a.e. strongly measurable on the
window.** -/
theorem ReconWindowAt.approxForce_carrier_aesm
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    {Acl r m' : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (hNco : Nc + r + 1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (hK2 : 2 * Acl + 2 + r ≤ Klift + D + 2) (hD1 : 1 ≤ D)
    (hcm : ∀ n r', Measurable fun s => coarseCoeff n W r'
      (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s))
    (hFm : ∀ n r', Measurable fun s =>
      coarseModeCoeff n (fun v => Fc v (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s)) r')
    (haRm : Measurable fun q' : Set.Icc tp (tp + Tobs) × Vec 2 => aRep q'.1 q'.2)
    (n : ℕ) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r) (v : ι) :
    AEStronglyMeasurable (fun s => carrierOf (Kc v) (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B
        ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v s x))
      (volume.restrict (Set.Icc tp (tp + Tobs))) := by
  have hΛ1 : 1 ≤ Λ := by have := w.hΛ; omega
  have htAZ : tp ≤ tp + Tobs := by linarith [w.hTobs]
  have hN1 : ((1 : ℕ∞) : WithTop ℕ∞) ≤
      ((kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) : ℕ) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (by exact_mod_cast (by omega :
      1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)))
  refine Coarse.aestronglyMeasurable_of_weak fun ψ hψ hψp => ?_
  have hmeas := approxForce_tested_measurable hφ hΛ1 w.hν htAZ (fun k => F.weight (pp k))
    w.hpart (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B ρ
      (ρ / ocEpsilon q Λ (m - 1)) k (F.fiber (pp k) (actual (pp k))))
          w.hsetting Cc w.hseq
    hAcl (by omega : 1 ≤ Acl + 2 + r) (by omega : 1 ≤ r + 1) (by omega) (by omega)
    (by omega : 1 ≤ Acl + 2 + r) (by omega : 1 ≤ max (Llift + 1) (Llift + 2)) (by omega)
    (by omega) n aRep w.hrep w.hcs.D_ge w.hDr
    (fun s hs d => (w.hcs.AD_smooth d s hs).of_le hN1)
    (fun s hs r' hr' v' u d => (w.hcs.CE_smooth r' hr' v' u d s hs).of_le hN1)
    (continuous_streamVel_of_admissible hφ)
    (fun s hs => (w.defectRemainder_smooth (N := Nc) (by omega) n hs).1)
    (hcm n) (hFm n) w.hcs.drift_meas w.hcs.J_meas w.hcs.AD_meas w.hcs.CE_meas haRm
    (Vc n) (hch n).1 (Vn n) (hch n).2 v ψ hψ.continuous
  refine hmeas.aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
  obtain ⟨hsm, hpm⟩ := w.approxForce_smooth hAcl hK hrL hord hNco Vc Vn hch n hs Kc hKr
  beta_reduce
  rw [projIcc_val_of_mem htAZ hs, carrierOf_eq (Kc v) (hsm v) (hpm v)]
  unfold Coarse.tval cellInner
  refine integral_congr_ae ?_
  filter_upwards [periodicHk_value_ae (Kc v) _ (hsm v) (hpm v)] with x hx
  rw [hx]

/-- **The residual force of the physical reconstruction.** The forcing residual carriers of the
approximants converge at every window time to a residual force `qq`, a.e. strongly measurable and
square integrable on the window, with a uniform bound; their distances to `qq` are bounded by
functions whose window integrals tend to zero. The commutator remainders enter through the
convergence to zero and the uniform bound of their jets (`hE0`, `hEB`). -/
theorem ReconWindowAt.force_limit
    (w : ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs ρ ρc Jm F actual K T pp π Cpart H Nc Klift Llift
      qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀)
    (hSb : 0 ≤ Sb) {Acl r m' kres Nχ : ℕ} (hAcl : 1 ≤ Acl) (hK : Acl + 2 + r ≤ Klift)
    (hrL : r ≤ Llift) (hord : Acl + 2 + r + (2 * Nc + D) ≤ m' + 1)
    (hk : Acl + 2 + r + Nc + 1 ≤ kres) (hNχ : m' + 1 ≤ Nχ) (hNχ' : kres + 1 ≤ Nχ)
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ Nc →
      ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ Acl + 2 + r →
        schurEnergyJet π (Set.Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp /
            ocEll q Λ m ν ^ 2)
          (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2))
          Llift j (Cc k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ρ / ocEpsilon q Λ (m - 1)) ^ (n - m'' + j)))
    (Vc : ℕ → ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (Vn : ℕ → ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hch : ∀ n, w.IsApproxChains n (Acl + 2 + r) (r + 1) Acl (Acl + 2 + r)
      (max (Llift + 1) (Llift + 2)) (Vc n) (Vn n))
    (hK2 : 2 * Acl + 2 + r ≤ Klift + D + 2) (hD1 : 1 ≤ D)
    (hcm : ∀ n r', Measurable fun s => coarseCoeff n W r'
      (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s))
    (hFm : ∀ n r', Measurable fun s =>
      coarseModeCoeff n (fun v => Fc v (Set.projIcc tp (tp + Tobs) (by linarith [w.hTobs]) s)) r')
    (haRm : Measurable fun q' : Set.Icc tp (tp + Tobs) × Vec 2 => aRep q'.1 q'.2)
    (hkres : kres ≤ kc) (hmr : m' + 1 ≤ r₀) (hrW : Nc + r + 2 ≤ kc + 1 + (Nc + D))
    (hNco : Nc + r + 1 ≤ kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon q Λ m) (Kc : ι → ℕ) (hKr : ∀ v, Kc v ≤ r)
    (hWint : IntegrableOn (fun s => ∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
      (W v s).val) (Set.Icc tp (tp + Tobs)))
    (hFint : IntegrableOn (fun s => massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => kc) ρ π (fun v => (Fc v s).val)) (Set.Icc tp
          (tp + Tobs)))
    (hE0 : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ ε > 0, ∀ᶠ n in atTop, ∀ j ≤ Nc + r, ∀ x,
      ‖iteratedFDeriv ℝ j ((defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W aRep) s) x‖ ≤ ε)
    {CE' CW : ℝ} (hCE' : 0 ≤ CE') (hCW : 0 ≤ CW)
    (hEB : ∀ n, ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ j ≤ Nc + r, ∀ x,
      ‖iteratedFDeriv ℝ j ((defectRemainder n (streamVel (Φ (m - 1))) (Nc + D) H AD CE Jm W aRep) s) x‖ ≤ CE')
    (hWB : ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ u, ‖W u s‖ ≤ CW) :
    ∃ C₃ C₄ : ℝ, 0 ≤ C₃ ∧ 0 ≤ C₄ ∧
    ∃ qq : ℝ → ∀ v, TorusHk (Kc v) (h v),
      (∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v, Tendsto (fun n => carrierOf (Kc v) (fun x => approxForce α
          q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v s x))
        atTop (𝓝 (qq s v))) ∧
      (∀ v, AEStronglyMeasurable (fun s => qq s v) (volume.restrict (Set.Icc tp (tp + Tobs)))) ∧
      (∀ s ∈ Set.Icc tp (tp + Tobs), massNormSq (E := h) (K := Kc) rs π (fun v => (qq s v).val) ≤
        3 * ((2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m' (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) *
          ((∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
            (W v s).val) +
          massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v s).val)) + (C₃ * CE') ^ 2 + (C₄ *
                CW) ^ 2)) ∧
      (∀ v, MemLp (fun s => qq s v) 2 (volume.restrict (Set.Icc tp (tp + Tobs)))) ∧
      ∃ c : ℕ → ℝ → ℝ, (∀ n, IntegrableOn (c n) (Set.Icc tp (tp + Tobs))) ∧
        Tendsto (fun n => ∫ s in Set.Icc tp (tp + Tobs), c n s) atTop (𝓝 0) ∧ (∀ n s, 0 ≤ c n s) ∧
        ∀ n, ∀ s ∈ Set.Icc tp (tp + Tobs), ∀ v,
          ‖carrierOf (Kc v) (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v s x) - qq s v‖ ≤ c n s := by
  obtain ⟨C₃, C₄, hC₃, hC₄, hb⟩ := w.approxForce_carrier_mass_le hSb hAcl hK hrL hord hk hNχ
    hNχ' hCg hgr Vc Vn hch hkres hmr hrW hNco hrs hrse Kc hKr
  refine ⟨C₃, C₄, hC₃, hC₄, ?_⟩
  have hI : volume (Set.Icc tp (tp + Tobs)) < ⊤ := measure_Icc_lt_top
  have hc3 : IntegrableOn (fun _ : ℝ => (C₃ * CE') ^ 2) (Set.Icc tp (tp + Tobs)) :=
      integrableOn_const hI.ne
  have hc4 : IntegrableOn (fun _ : ℝ => (C₄ * CW) ^ 2) (Set.Icc tp (tp + Tobs)) :=
      integrableOn_const hI.ne
  exact exists_residual_limit measurableSet_Icc measure_Icc_lt_top Kc hrs π w.hcs.mass_pos
    (fun n s v => carrierOf (Kc v) (fun x => approxForce α q Λ m (Φ (m - 1)) hφ ν B ρ tp (tp + Tobs)
          (fun k => F.weight (pp k)) H Nc Acl Cc (Vc n) (Vn n) n (streamVel (Φ (m - 1)))
          (Nc + D) AD CE Jm W aRep v s x))
    (fun n v => w.approxForce_carrier_aesm hAcl hK hrL hord hNco Vc Vn hch hK2 hD1 hcm hFm haRm
      n Kc hKr v)
    (fun s hs v => w.approxForce_carrier_cauchy hSb hAcl hK hrL hord hk hNχ hNχ' hCg hgr Vc Vn
      hch hkres hmr hrW hNco hs hrs hrse Kc hKr (hE0 s hs) v)
    (fun s => 3 * ((2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m' (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))) *
          ((∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m'
            (W v s).val) +
          massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => kc)
            ρ π (fun v => (Fc v s).val)) + (C₃ * CE') ^ 2 + (C₄ *
                CW) ^ 2))
    (((((hWint.add hFint).const_mul ((2 ^ (r + 1) * (2 * (tailForceConst H Nc D Acl r m'
        (pulseChartD Nχ) *
          (((ocEll q Λ m ν ^ 2)⁻¹ *
          (ocDStar q Λ m ν B / ρ) ^ (Nc + 1) *
          (ocEpsilon q Λ m / ρ) ^ Acl *
          ρ * reconTailS Klift Llift D H Nc CGl Cw Ca Sb) ^ 2) +
        liftForceConst H Nc Acl r kres Nχ (pulseChartD Nχ) *
          ((ρ⁻¹ *
          (ocEpsilon q Λ m / ρ) ^ Acl) ^ 2 *
          (ocDStar q Λ m ν B / ρ) ^ 2 *
          reconLiftTheta Acl r H Cg Sb ^ 2)))))).add hc3).add hc4).const_mul 3)
    (fun n s hs => hb n s hs CE' CW hCE' hCW (hEB n s hs) (hWB s hs))

end AVRegularity.CycleComparison.Reconstruction
end
