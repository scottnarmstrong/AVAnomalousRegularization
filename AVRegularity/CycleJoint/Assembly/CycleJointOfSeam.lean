-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.SeamAllocationLetterFacts
import AVRegularity.CycleJoint.Assembly.WordGeometryOfRetained
import AVRegularity.CycleJoint.Assembly.B1Family
public import AVRegularity.CycleJoint.Assembly.PriceLedgerC2
import AVRegularity.CycleJoint.Assembly.ScalarResidualContraction
import AVRegularity.CycleJoint.PathReduction.Main
import AVRegularity.CycleWords.Assembly.SeamNorms

section
/-! **The seam for one family**.

`seamAllocation_family`: for one family with the joint premises, given the seam's body for every
allocation `σ = (wo, wf)` with its constants `Q_σ, qΥ_σ, c_σ, CM_σ, CN_σ`, uniform constants
dominating them, and the scale conditions, the cell model `Σ_σ Kp_σ (input of wo)` has the model and
error bounds of `SeamAllocationStatement`. The window objects (clamped metrics, packages,
transition, letters) are shared by all allocations.

For a family without edges the same kernels give the cell model at slot `0` from the word
chains of the two-block theorem at slot `0`; on truncated data it is the cell model at slots `K`, because the old word
chains at slot `0` end at the truncations of those at slots `K`
(`JointPremisesGen.oldChains_slotZero`) and the seam's input reads only values. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- The scaled cutoff `θ ↦ χ(θ/√η)` vanishes outside the disc of radius `√η ξ₀`. -/
theorem cutoff_scaled_radial {χm : Vec 2 → ℝ} {ξ0 η : ℝ} (hη : 0 < η)
    (hsupp : ∀ ξ, ξ0 ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0) (θ : Vec 2)
    (hθ : Real.sqrt η * ξ0 ≤ Real.sqrt (vecDot θ θ)) : χm ((Real.sqrt η)⁻¹ • θ) = 0 := by
  apply hsupp
  have hs := Real.sqrt_pos.2 hη
  have hdot : vecDot ((Real.sqrt η)⁻¹ • θ) ((Real.sqrt η)⁻¹ • θ) =
      ((Real.sqrt η)⁻¹) ^ 2 * vecDot θ θ := by
    simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdot, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hs.le), le_inv_mul_iff₀ hs]
  exact hθ

section Family

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- **Assembly of the seam**: linear inputs and the sum over the allocations, from uniform bounds of
the allocations. -/
theorem seamAllocation_assemble
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    {χm : Vec 2 → ℝ} {ξ0 : ℝ} (hχs : ContDiff ℝ (⊤ : ℕ∞) χm)
    (hχsupp : ∀ ξ, ξ0 ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0)
    {Jpre Jpost pout Mb Ns Q : ℕ} {c CM CN Cθ : ℝ} (Υ : Vec 2 → Vec 2)
    (Kpf : List Bool × List Bool → (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (CMf CNf : List Bool × List Bool → ℕ → ℝ)
    (hCMf : ∀ σ M, 0 < CMf σ M) (hCNf : ∀ σ N, 0 < CNf σ N) (hCθ0 : 0 ≤ Cθ)
    (hprice0 : 0 ≤ seamWindowPrice α q Λ m ν B Q Ns c)
    (hCM : ∀ M ≤ Mb, ∑ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      CMf σ M * Cθ ^ (σ.1.length + σ.2.length) ≤ CM)
    (hCN : ∑ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      CNf σ Ns * Cθ ^ (σ.1.length + σ.2.length) ≤ CN)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (uO : ∀ wo : List Bool, (∀ i, TorusHk (K i) (h i)) → ∀ (_ : Fin (wo.length + 1)) (x : ι),
      ℝ → PlaneHk Set.univ (K x) (h x))
    (uF : List Bool → ∀ wf : List Bool, (∀ i, TorusHk (K i) (h i)) →
      ∀ (_ : Fin (wf.length + 1)) (x : ι), ℝ → PlaneHk Set.univ (K x) (h x))
    (hlin : ∀ wo ∈ blockWords Jpre H, ∀ (c' : ℝ) (ξ ξ' : ∀ i, TorusHk (K i) (h i)) j x,
      ∀ t ∈ Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)),
      uO wo (c' • ξ + ξ') j x t = c' • uO wo ξ j x t + uO wo ξ' j x t)
    (hKu : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H, ∀ ξ,
      (∀ x (M : ℕ), ContDiff ℝ M (Kpf σ (seamInput χm (ν / B) Υ
        (fun x => uO σ.1 ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀)))) x)) ∧
      (∀ M ≤ Mb,
        weightedJetNorm π (pout : ℝ) M (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
            (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
            (fun x _ wd z => orderedDerivative wd (Kpf σ (seamInput χm (ν / B) Υ
              (fun x => uO σ.1 ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀)))) x) z) ≤
          ENNReal.ofReal (CMf σ M * Cθ ^ (σ.1.length + σ.2.length)) *
            momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
              (fun x => planeValue (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ x))) ∧
      weightedJetNorm π (pout : ℝ) Kmax (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
          (r / ocEpsilon q Λ m)
          (fun x a' wd z => if a' ≤ K x then
            planeJetOrder (uF σ.1 σ.2 ξ (Fin.last _) x (cellTime q Λ m ν (twoTp α q Λ m l₀))) a'
                wd z -
              orderedDerivative wd (Kpf σ (seamInput χm (ν / B) Υ
                (fun x => uO σ.1 ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀)))) x) z
            else 0) ≤
        ENNReal.ofReal (CNf σ Ns * Cθ ^ (σ.1.length + σ.2.length) *
            seamWindowPrice α q Λ m ν B Q Ns c) *
          momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
            (fun x => planeValue (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ x))) :
    ∃ Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x),
      (∀ ξ, Mc ξ = ∑ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H, Kpf σ (seamInput χm (ν / B) Υ
        (fun x => uO σ.1 ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀))))) ∧
      (∀ ξ x (M : ℕ), ContDiff ℝ M (Mc ξ x)) ∧
      (∀ ξ, ∀ M ≤ Mb,
        weightedJetNorm π (pout : ℝ) M (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
            (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
            (fun x _ wd z => orderedDerivative wd (Mc ξ x) z) ≤
          ENNReal.ofReal CM *
            momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
              (fun x => planeValue (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ x))) ∧
      ∀ ξ, weightedJetNorm π (pout : ℝ) Kmax (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
          (r / ocEpsilon q Λ m)
          (fun x a' wd z => if a' ≤ K x then
            planeJetOrder (∑ wo ∈ blockWords Jpre H, ∑ wf ∈ blockWords Jpost H,
              uF wo wf ξ (Fin.last _) x (cellTime q Λ m ν (twoTp α q Λ m l₀))) a' wd z -
              orderedDerivative wd (Mc ξ x) z else 0) ≤
        ENNReal.ofReal (CN * seamWindowPrice α q Λ m ν B Q Ns c) *
          momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
            (fun x => planeValue (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ x))  := by
  obtain ⟨hν, hB, -⟩ := hp.cov.pos
  have hab : cellTime q Λ m ν (twoSeam α q Λ m l₀) ∈
      Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) :=
    ⟨(hp.windows hΛ).ab.le, le_rfl⟩
  have hη : 0 < ν / B := div_pos hν hB
  have hlinIn : ∀ wo ∈ blockWords Jpre H, ∀ (c' : ℝ) (ξ ξ' : ∀ i, TorusHk (K i) (h i)),
      seamInput χm (ν / B) Υ
          (fun x => uO wo (c' • ξ + ξ') (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀))) =
        c' • seamInput χm (ν / B) Υ
            (fun x => uO wo ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀))) +
          seamInput χm (ν / B) Υ
            (fun x => uO wo ξ' (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀))) := by
    intro wo hwo c' ξ ξ'
    have hfun : (fun x => uO wo (c' • ξ + ξ') (Fin.last _) x
        (cellTime q Λ m ν (twoSeam α q Λ m l₀))) = fun x =>
          c' • uO wo ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀)) +
            uO wo ξ' (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀)) :=
      funext fun x => hlin wo hwo c' ξ ξ' _ x _ hab
    rw [hfun]
    exact seamInput_linear χm (ν / B) Υ (Real.sqrt (ν / B) * ξ0)
      (cutoff_scaled_radial hη hχsupp) (hχs.comp (contDiff_id.const_smul _)) c' _ _
  obtain ⟨Mc, hMc, hsm, hmod, herr⟩ := seamSum_bounds_prod (blockWords Jpre H) (blockWords Jpost H)
    (fun wo ξ => seamInput χm (ν / B) Υ
      (fun x => uO wo ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀)))) hlinIn Kpf
    (fun wo wf ξ x => uF wo wf ξ (Fin.last _) x (cellTime q Λ m ν (twoTp α q Λ m l₀))) π
    (pout : ℝ) Mb Kmax (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m)
    (fun ξ => momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
      (fun x => planeValue (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ x)))
    (fun σ M => CMf σ M * Cθ ^ (σ.1.length + σ.2.length))
    (fun σ => CNf σ Ns * Cθ ^ (σ.1.length + σ.2.length) * seamWindowPrice α q Λ m ν B Q Ns c)
    (fun σ _ M => mul_nonneg (hCMf σ M).le (pow_nonneg hCθ0 _))
    (fun σ _ => mul_nonneg (mul_nonneg (hCNf σ Ns).le (pow_nonneg hCθ0 _)) hprice0)
    (fun σ hσ ξ => (hKu σ hσ ξ).1) (fun σ hσ ξ => (hKu σ hσ ξ).2.1)
    (fun σ hσ ξ => (hKu σ hσ ξ).2.2)
  refine ⟨Mc, hMc, hsm, fun ξ M hM => ennreal_bound_mono (hCM M hM) (hmod ξ M hM),
    fun ξ => ennreal_bound_mono ?_ (herr ξ)⟩
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hCN hprice0

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The cell model at slot `0` on truncated data is the cell model at slots `K`, when the old
endpoints at slot `0` are the truncations of those at slots `K`. -/
theorem seamModel_slotZero_eq (S : Finset (List Bool × List Bool))
    (Kpf : List Bool × List Bool → (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (χm : Vec 2 → ℝ) (η : ℝ) (Υ : Vec 2 → Vec 2) (b : ℝ)
    (uO : ∀ wo : List Bool, (∀ i, TorusHk (K i) (h i)) → ∀ (_ : Fin (wo.length + 1)) (x : ι),
      ℝ → PlaneHk Set.univ (K x) (h x))
    (uO0 : ∀ wo : List Bool, (∀ i, TorusHk 0 (h i)) → ∀ (_ : Fin (wo.length + 1)) (x : ι),
      ℝ → PlaneHk Set.univ 0 (h x))
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (Mc0 : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hMc : ∀ ξ, Mc ξ = ∑ σ ∈ S, Kpf σ (seamInput χm η Υ (fun x => uO σ.1 ξ (Fin.last _) x b)))
    (hMc0 : ∀ ξ, Mc0 ξ = ∑ σ ∈ S, Kpf σ (seamInput χm η Υ (fun x => uO0 σ.1 ξ (Fin.last _) x b)))
    (ξ : ∀ i, TorusHk (K i) (h i))
    (heq : ∀ σ ∈ S, ∀ x, uO0 σ.1 (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i))
      (Fin.last _) x b = truncatePlaneHk (Nat.zero_le (K x)) (uO σ.1 ξ (Fin.last _) x b)) :
    Mc0 (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i)) = Mc ξ := by
  rw [hMc0, hMc]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  congr 1
  funext x z
  simp only [seamInput, heq σ hσ, planeValue_truncate]

/-- **Uniqueness for the old word chains of the two-block theorem**: for a family without edges, the old word chains at slot
`0` from the truncated datum end at the truncations of the old word chains at slots `K`
(through `oldChain_slotZero_eq`). -/
theorem JointPremisesGen.oldChains_slotZero (hU : WordChainUniqueStatement.{u, v})
    (hcongr : PlaneChainMetricCongrStatement.{u, v})
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hedge : ∀ v u, IsEmpty (F.Γ v u)) (hΛ : 1 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ) (hD : 2 ≤ D)
    (GO : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hGO : ∀ t ∈ Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)),
      GO t = twoGpre hp t 0)
    (hGmO : IsCellMetric (fun t _ => GO t)) (hg4 : g ≤ 1 / 4)
    (hGnO : IsMetricNearIdentity (fun t _ => GO t) g)
    (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν (twoYc hp)))
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (ocCellDrift α q Λ ζ m ν (twoYc hp) t))
    {CL : ℝ} (R : ℕ)
    (hM : IsCycleLetter π (twoMpre hp (CL * g) (fun v u => if v = u then CL * g else 0))
      (Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) ×ˢ Set.univ) R H)
    (hS : IsCycleLetter π (twoSpre hp (CL * (Cth * Θ))
        (fun v u => CL * (Real.sqrt (π u / π v) * A v u)))
      (Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) ×ˢ Set.univ) R H)
    (hMm : ∀ x y o, ∀ γ ∈ (twoMpre hp (CL * g) (fun v u => if v = u then CL * g else 0)).edge
      x y o, ∀ β X z, Measurable fun t => γ.coeff β t X z)
    (hSm : ∀ x y o, ∀ γ ∈ (twoSpre hp (CL * (Cth * Θ))
      (fun v u => CL * (Real.sqrt (π u / π v) * A v u))).edge x y o, ∀ β X z,
      Measurable fun t => γ.coeff β t X z)
    (hMK : ∀ x y (o : Finset.Icc 2 D),
      (twoMpre hp (CL * g) (fun v u => if v = u then CL * g else 0)).edge x y o ≠ [] →
      K x + o.1 ≤ K y + 2)
    (hSK : ∀ x y (o : Finset.Icc 2 D), (twoSpre hp (CL * (Cth * Θ))
      (fun v u => CL * (Real.sqrt (π u / π v) * A v u))).edge x y o ≠ [] → K x + o.1 ≤ K y + 2)
    {Jpre Jpost Npatch : ℕ} {hNpatch : 0 < Npatch} {patch : Fin 2 → ℤ}
    {uO wO uF wF} (hch : SeamWordChains hp hΛ hchart hζ CL Jpre Jpost Npatch hNpatch patch uO wO
      uF wF)
    {uO0 wO0 uF0 wF0} (hch0 : SeamWordChains (hp.slotZero hedge) hΛ hchart hζ CL Jpre Jpost
      Npatch hNpatch patch uO0 wO0 uF0 wF0)
    (hEO : SeamOldMoments hp Jpre wO) (hEO0 : SeamOldMoments (hp.slotZero hedge) Jpre wO0) :
    ∀ wo ∈ blockWords Jpre H, ∀ (ξ : ∀ i, TorusHk (K i) (h i)) x,
      uO0 wo (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i)) (Fin.last _) x
          (cellTime q Λ m ν (twoSeam α q Λ m l₀)) =
        truncatePlaneHk (Nat.zero_le (K x))
          (uO wo ξ (Fin.last _) x (cellTime q Λ m ν (twoSeam α q Λ m l₀))) := by
  intro wo hwo ξ x
  obtain ⟨hν, hB, hr⟩ := hp.cov.pos
  have hε := Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hϖ : 0 < ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m) :=
    div_pos hε (Real.sqrt_pos.2 (mul_pos hB (Construction.Stream.ocTauPP_pos hΛ)))
  have hb : cellTime q Λ m ν (twoSeam α q Λ m l₀) ∈
      Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) :=
    ⟨(hp.windows hΛ).ab.le, le_rfl⟩
  have hchO0 := SeamWordChains.slotZero_old (K := K) (hp := hp) (hedge := hedge) hch0
  exact oldChain_slotZero_eq hU hcongr hD π hp.hπ (fun t => twoGpre hp t 0) GO
    (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (hp.windows hΛ).ab.le
    (fun s hs => (hGO s hs).symm) hGmO g hg4 hGnO (ocCellDrift α q Λ ζ m ν (twoYc hp)) hv hvs R H K
    (twoMpre hp (CL * g) (fun v u => if v = u then CL * g else 0))
    (twoSpre hp (CL * (Cth * Θ)) (fun v u => CL * (Real.sqrt (π u / π v) * A v u)))
    hM hS hMm hSm hMK hSK (blockMetricLetter_slotZero _ _ _ _ _ _)
    (blockSourceLetter_slotZero F hedge _ actual hφ _ l₀ _ _ _ _ _ Ks _ _) wo
    ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
    (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ)
    (twoV₀ (hp.slotZero hedge) hΛ hchart hζ Npatch hNpatch patch
      (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i)))
    (twoV₀_slotZero hp hedge hΛ hchart hζ Npatch hNpatch patch ξ) (uO wo ξ) (wO wo ξ)
    (hch.1 wo hwo ξ) (uO0 wo (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i)))
    (wO0 wo (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i)))
    (hchO0 wo hwo (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i)))
    (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m) hϖ (div_pos hr hε)
    (hEO wo hwo ξ) (hEO0 wo hwo (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i))) (Fin.last _)
    x _ hb

/-- **The seam for one family.** -/
theorem seamAllocation_family (hcongr : PlaneChainMetricCongrStatement.{u, v})
    (hclamp : ClampedMetricStatement) (hshrink : PackageBufferShrinkStatement)
    (hU : WordChainUniqueStatement.{u, v})
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hD : 2 ≤ D) (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    {Kc : ScalarConstants} {Θ₀ g₁s : ℝ} (hcl : ScalarPackageClause α q Λ ζ Kc Θ₀) (hΘ₀ : 1 ≤ Θ₀)
    {Jstar : ℕ} {CL : ℝ}
    (hLb : BlockLettersBody.{u, v, w, x} D Kmax Ks Ls Jm Jchart qJ Jstar Ca Cm Cchart CG CL)
    (hCL : 0 ≤ CL) {CU : ℝ}
    (hTb : BlockTransitionBody.{u, v, w, x, v} Kmax Jchart Cchart CG Cpad Cage CU)
    {χm : Vec 2 → ℝ} (hχs : ContDiff ℝ (⊤ : ℕ∞) χm)
    (hχsupp : ∀ ξ, 2 * Kc.ξlo ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0)
    {Jpre Jpost pout Mb Ns Q : ℕ} {Cs c CM CN : ℝ}
    (Qf qf : List Bool × List Bool → ℕ) (cf : List Bool × List Bool → ℝ)
    (CMf CNf : List Bool × List Bool → ℕ → ℝ)
    (hbody : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      SeamPairBody.{u, v} Kc g₁s D H Kmax pout (seamOrderK D Kmax σ.1) σ.1.length σ.2.length
        (wordOrders D σ.1) (wordSlow Ks σ.1) (wordPositive σ.1) (wordOrders D σ.2)
        (wordSlow Ks σ.2) (wordPositive σ.2) (Qf σ) Mb Ns (qf σ) 1 1 Cs CU 1 χm (cf σ) (CMf σ)
        (CNf σ))
    (hCMf : ∀ σ M, 0 < CMf σ M) (hCNf : ∀ σ N, 0 < CNf σ N)
    (hQ : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H, Qf σ ≤ Q)
    (hqΥ : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H, qf σ ≤ Jchart + 1)
    (hc : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H, c ≤ cf σ)
    (hR : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      seamReserve D Kmax pout Ks σ.1 σ.2 ≤ Jstar)
    (hCM : ∀ M ≤ Mb, ∑ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      CMf σ M * (CL * max 1 (max Cth 0)) ^ (σ.1.length + σ.2.length) ≤ CM)
    (hCN : ∑ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      CNf σ Ns * (CL * max 1 (max Cth 0)) ^ (σ.1.length + σ.2.length) ≤ CN)
    (hNs : 1 ≤ Ns) (hg₀ : g₀ ≤ min (min g₁s Kc.g0) (1 / 4)) (hθ : 0 ≤ Cth * Θ)
    (hgU : g + ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ min (min g₁s Kc.g0) (1 / 4))
    (hlong : max Θ₀ (3 * max Kc.θs 1) ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2)
    (hbudget : seamWindowBudget α q Λ m ν B Q c ≤ 1) :
    ∀ (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ),
      SeamDatumSupport hp hΛ hchart hζ Cs Npatch hNpatch patch →
    ∀ uO wO uF wF, SeamWordChains hp hΛ hchart hζ CL Jpre Jpost Npatch hNpatch patch uO wO uF wF →
    ∃ Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x),
      SeamModelClauses hp hΛ hchart hζ Jpre Jpost Mb pout Q Ns CM CN c Npatch hNpatch patch uF
        Mc ∧
      ∀ hedge : ∀ v u, IsEmpty (F.Γ v u), SeamOldMoments hp Jpre wO →
        SeamDatumSupport (hp.slotZero hedge) hΛ hchart hζ Cs Npatch hNpatch patch →
      ∀ uO0 wO0 uF0 wF0, SeamWordChains (hp.slotZero hedge) hΛ hchart hζ CL Jpre Jpost Npatch
        hNpatch patch uO0 wO0 uF0 wF0 → SeamOldMoments (hp.slotZero hedge) Jpre wO0 →
      ∃ Mc0 : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x),
        SeamModelClauses (hp.slotZero hedge) hΛ hchart hζ Jpre Jpost Mb pout Q Ns CM CN c Npatch
          hNpatch patch uF0 Mc0 ∧
        ∀ ξ, Mc0 (fun i => truncateTorusHk (Nat.zero_le (K i)) (ξ i)) = Mc ξ := by
  obtain ⟨hν, hB, hr⟩ := hp.cov.pos
  have hl := ocEll_sq_pos_of (q := q) (m := m) hΛ hν
  have hνB : ν ≤ B := by
    have h1 := CycleReference.meanFlux_ge_input (α := α) (q := q) (m := m) hΛ hζ hν
    have h2 : κ (m - 1) = ocMeanFlux α q Λ ζ m (κ m) :=
      hp.hband.2 m (by have := hp.hm2; omega) hp.hmM
    rw [← hp.hB, h2, hp.hν]
    exact h1
  have hS := seamS_ge_one hΛ hν hp.cov.ellT
  have hS0 : 0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 := by linarith
  have hg0 : 0 ≤ g := hp.cov.g_range.1
  have hgg : g ≤ g₀ := hp.cov.g_range.2
  have hA0 : 0 ≤ ocA α q Λ (m - 1) * ocTauPP α q Λ m :=
    mul_nonneg (ocA_nonneg_of hΛ (m - 1)) (Construction.Stream.ocTauPP_pos hΛ).le
  have hg1 : g ≤ min (min g₁s Kc.g0) (1 / 4) := le_trans (by linarith) hgU
  have hgs : g ≤ g₁s := hg1.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hgK : g ≤ Kc.g0 := hg1.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hg4 : g ≤ 1 / 4 := hg1.trans (min_le_right _ _)
  have hg₀4 : g₀ ≤ 1 / 4 := hg₀.trans (min_le_right _ _)
  have hgUK : 0 ≤ g + ocA α q Λ (m - 1) * ocTauPP α q Λ m ∧
      g + ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ Kc.g0 :=
    ⟨by linarith, hgU.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  obtain ⟨GO, GF, hGmO, hGnO, hGO, hGmF, hGnF, hGF⟩ := hp.seamMetrics hclamp hΛ (by linarith)
  obtain ⟨regO, regF, ⟨pkgO⟩, ⟨pkgF⟩, hqO, hpO, hqF, hpF, hjO, hbO, hjF, hbF, hseamQ, hquietMargin⟩ :=
    hp.seamBlocks hΛ hζ hcl hΘ₀ (le_max_left _ _) (le_max_right _ _) hshrink hlong GO GF hGmO
      hGnO hGmF hGnF hgK
  have hdO := seamDrift_facts hcl hp.hband hp.hm2 hp.hmM hp.hν hp.hB (twoYc hp) GO g hGmO hg0
    hgK hGnO
  have hdF := seamDrift_facts hcl hp.hband hp.hm2 hp.hmM hp.hν hp.hB (twoYcPost hp) GF g hGmF
    hg0 hgK hGnF
  obtain ⟨Υ, Υinv, hΥt, hΥt0, hΥ, hΥs⟩ := hp.seamTransition hΛ hchart hTb hg₀4
  have hlet := fun R hRJ => hp.seamLetterFacts hΛ hLb hD hg₀4 hθ heE R hRJ regO regF hpO hpF hqO hqF
  have hC0f : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      peFactor (ν / B) ^ Qf σ * (1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ Qf σ *
        (1 + regF.joins) * Real.exp (-cf σ * regF.buffer) ≤ 1 := by
    intro σ hσ
    rw [hbF]
    exact seamBudget_of_window (hQ σ hσ) (hc σ hσ) hjF hS0 (seamBuffer_nonneg hΛ hν) hbudget
  have hC0Of : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      peFactor (ν / B) ^ Qf σ * (1 + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ^ Qf σ *
        (1 + regO.joins) * Real.exp (-cf σ * regO.buffer) ≤ 1 := by
    intro σ hσ
    rw [hbO]
    exact seamBudget_of_window (hQ σ hσ) (hc σ hσ) hjO hS0 (seamBuffer_nonneg hΛ hν) hbudget
  choose! Kpf hKpf using fun σ (hσ : σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H) =>
    seamPair_apply hcongr hp hΛ σ.1 σ.2 (hbody σ hσ) hNs hν hB hνB hS hp.cov.RE hr
      hp.cov.rho_e GO GF hGmO hGnO hGO hGmF hGnF hGF hg0 hgK hgs hdO hdF regO regF pkgO pkgF
      hseamQ hquietMargin (hC0f σ hσ) (hC0Of σ hσ) Υ Υinv (hΥ.mono (hqΥ σ hσ)) hΥs hgUK _ _ _ _
      ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
      (hlet _ (hR σ hσ)).1 (hlet _ (hR σ hσ)).2.1 (hlet _ (hR σ hσ)).2.2.1
      (hlet _ (hR σ hσ)).2.2.2
  have hCθ0 : 0 ≤ CL * max 1 (max Cth 0) := mul_nonneg hCL (zero_le_one.trans (le_max_left _ _))
  have hηg0 := seamEtaG_pos (α := α) (q := q) (m := m) hΛ hB
  have hηg1 := seamEtaG_le_one (α := α) (q := q) (m := m) hΛ hp.cov.RE
  have hθM0 : 0 ≤ CL * g := mul_nonneg hCL hg0
  have hθM1 : CL * g ≤ CL * max 1 (max Cth 0) := mul_le_mul_of_nonneg_left
    ((by linarith : g ≤ 1).trans (le_max_left _ _)) hCL
  have hθS0 : 0 ≤ CL * (Cth * Θ) := mul_nonneg hCL hθ
  have hθS1 : CL * (Cth * Θ) ≤ CL * max 1 (max Cth 0) := by
    refine mul_le_mul_of_nonneg_left ?_ hCL
    have h1 : Cth * Θ ≤ max Cth 0 * Θ := mul_le_mul_of_nonneg_right (le_max_left _ _) hp.hΘ₀
    have h2 : max Cth 0 * Θ ≤ max Cth 0 :=
      mul_le_of_le_one_right (le_max_right _ _) hp.hΘ₁
    exact h1.trans (h2.trans (le_max_right _ _))
  have hΘw := fun σ : List Bool × List Bool => theta_pair_le hCθ0
    (wordTheta_nonneg_le (M := twoMpre hp (CL * g) (fun v u => if v = u then CL * g else 0))
      (S := twoSpre hp (CL * (Cth * Θ)) (fun v u => CL * (Real.sqrt (π u / π v) * A v u)))
      hηg0 hηg1 hθM0 hθM1 hθS0 hθS1 σ.1)
    (wordTheta_nonneg_le (M := twoMpost hp (CL * g) (fun v u => if v = u then CL * g else 0))
      (S := twoSpost hp (CL * (Cth * Θ)) (fun v u => CL * (Real.sqrt (π u / π v) * A v u)))
      hηg0 hηg1 hθM0 hθM1 hθS0 hθS1 σ.2)
  have hpr := fun σ (hσ : σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H) =>
    seamPrice_le_window (B := B) (Ns := Ns) (hQ σ hσ) (hc σ hσ) hjF hbF hS0
      (seamBuffer_nonneg hΛ hν) (trimmedQuietMargin_nonneg hΛ hν)
  intro Npatch hNpatch patch hsupp uO wO uF wF hch
  have hchO := hch.1
  have hchF := hch.2.1
  have hlin := hch.2.2
  obtain ⟨Mc, hMc, hsm, hmod, herr⟩ := seamAllocation_assemble hp hΛ hchart hζ hχs hχsupp Υ Kpf
    CMf CNf hCMf hCNf hCθ0 (seamWindowPrice_nonneg hΛ hS0) hCM hCN Npatch hNpatch patch uO uF
    hlin (fun σ hσ ξ => by
      have hk := hKpf σ hσ K hp.hK (hlet _ (hR σ hσ)).1.2.2.2.2 (hlet _ (hR σ hσ)).2.1.2.2.2.2
        (hlet _ (hR σ hσ)).2.2.1.2.2.2.2 (hlet _ (hR σ hσ)).2.2.2.2.2.2.2
        (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch) hsupp (twoTransit hp hΛ hchart) hΥt
        (uO σ.1) (wO σ.1) (uF σ.1 σ.2) (wF σ.1 σ.2) (hchO σ.1 (Finset.mem_product.1 hσ).1)
        (hchF σ.1 (Finset.mem_product.1 hσ).1 σ.2 (Finset.mem_product.1 hσ).2) ξ
      exact ⟨hk.1, fun M hM => ennreal_bound_mono
        (mul_le_mul_of_nonneg_left (hΘw σ).2 (hCMf σ M).le) (hk.2.1 M hM),
        ennreal_bound_mono (error_const_le (hCNf σ Ns).le (hΘw σ) (hpr σ hσ)) hk.2.2⟩)
  refine ⟨Mc, ⟨hsm, hmod, herr⟩, fun hedge hEO hsupp0 uO0 wO0 uF0 wF0 hch0 hEO0 => ?_⟩
  have hchO0 := SeamWordChains.slotZero_old (K := K) (hp := hp) (hedge := hedge) hch0
  have hchF0 := SeamWordChains.slotZero_future (K := K) (hp := hp) (hedge := hedge) hch0
  have hlin0 := hch0.2.2
  have hdM : ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (X₀ : Vec 2) (δ θ : ℝ)
      (b : ι → ι → ℝ) x y (o : Finset.Icc 2 D),
      (blockMetricLetter (D := D) (h := h) G X₀ δ Ks θ b).edge x y o ≠ [] →
        (fun _ => 0 : ι → ℕ) x + o.1 ≤ (fun _ => 0 : ι → ℕ) y + 2 :=
    fun G X₀ δ θ b => blockMetricLetter_slotZero G X₀ δ Ks θ b
  obtain ⟨Mc0, hMc0, hsm0, hmod0, herr0⟩ := seamAllocation_assemble (hp.slotZero hedge) hΛ hchart
    hζ hχs hχsupp Υ Kpf CMf CNf hCMf hCNf hCθ0 (seamWindowPrice_nonneg hΛ hS0) hCM hCN Npatch
    hNpatch patch uO0 uF0 hlin0 (fun σ hσ ξ => by
      have hk := hKpf σ hσ (fun _ => 0) (fun _ => Nat.zero_le _) (hdM _ _ _ _ _)
        (blockSourceLetter_slotZero F hedge _ actual hφ _ l₀ _ _ _ _ _ Ks _ _) (hdM _ _ _ _ _)
        (blockSourceLetter_slotZero F hedge _ actual hφ _ (l₀ + 1) _ _ _ _ _ Ks _ _)
        (twoV₀ (hp.slotZero hedge) hΛ hchart hζ Npatch hNpatch patch) hsupp0
        (twoTransit (hp.slotZero hedge) hΛ hchart) (hΥt0 hedge)
        (uO0 σ.1) (wO0 σ.1) (uF0 σ.1 σ.2) (wF0 σ.1 σ.2) (hchO0 σ.1 (Finset.mem_product.1 hσ).1)
        (hchF0 σ.1 (Finset.mem_product.1 hσ).1 σ.2 (Finset.mem_product.1 hσ).2) ξ
      exact ⟨hk.1, fun M hM => ennreal_bound_mono
        (mul_le_mul_of_nonneg_left (hΘw σ).2 (hCMf σ M).le) (hk.2.1 M hM),
        ennreal_bound_mono (error_const_le (hCNf σ Ns).le (hΘw σ) (hpr σ hσ)) hk.2.2⟩)
  refine ⟨Mc0, ⟨hsm0, hmod0, herr0⟩, fun ξ => ?_⟩
  have hagree := hp.oldChains_slotZero hU hcongr hedge hΛ hchart hζ hD GO hGO hGmO hg4 hGnO
    hdO.1 hdO.2.2.1 Jstar (hlet Jstar le_rfl).1.1 (hlet Jstar le_rfl).2.1.1
    (hlet Jstar le_rfl).1.2.2.2.1 (hlet Jstar le_rfl).2.1.2.2.2.1 (hlet Jstar le_rfl).1.2.2.2.2
    (hlet Jstar le_rfl).2.1.2.2.2.2 hch hch0 hEO hEO0
  exact seamModel_slotZero_eq _ Kpf χm (ν / B) Υ _ uO uO0 Mc Mc0 hMc hMc0 ξ fun σ hσ x =>
    hagree σ.1 (Finset.mem_product.1 hσ).1 ξ x

end Family

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The seam on the two blocks**.

`seamAllocation_of_ingredients`: `SeamAllocationStatement` from `cycle_seam` (its text copy
`CycleSeamStatement`) and the three adaptations of the seam statement (buffer shrink, chain congruence in the
metric, clamped metric); the block letters and the block transition are proved (`blockLetters`, `blockTransition`) and the scalar
packages come from the proof of `scalar_package_interior`.

The seam's constants depend on the shape of an allocation; there are finitely many allocations,
and the constants are made uniform: `Q`, `qΥ` and the fast reserve are maxima, the rate is
`c = 1/(1 + Σ_σ 1/c_σ) ≤ c_σ`, and `CM`, `CN` are sums over the allocations weighted by
`Cθ^{|wo| + |wf|}` (the bound of the word weights `Θ_w`, `Cθ = CL max(1, Cth, 0)`). The cutoff is
`χ(ξ) = smoothTransition((r² - |ξ|²)/(3r²/4))` with `r = 2 ξ_lo`: it vanishes outside the retained
disc `|ξ| < 2 ξ_lo` and is `1` on `|ξ| ≤ ξ_lo`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- A smooth even cutoff, `0` outside the disc of radius `ξ₀`, `1` on the disc of radius `ξ₀/2`. -/
theorem exists_seam_cutoff {ξ0 : ℝ} (hξ0 : 0 < ξ0) :
    ∃ χm : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χm ∧ (∀ ξ, χm (-ξ) = χm ξ) ∧
      (∀ ξ, ξ0 ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → χm ξ = 1 := by
  have hd : 0 < ξ0 ^ 2 * (3 / 4) := by positivity
  have hdot0 : ∀ ξ : Vec 2, 0 ≤ vecDot ξ ξ := fun ξ =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg (ξ i)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Vec 2 => vecDot ξ ξ) := by
    unfold vecDot
    exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)
  refine ⟨fun ξ => Real.smoothTransition ((ξ0 ^ 2 - vecDot ξ ξ) / (ξ0 ^ 2 * (3 / 4))),
    Real.smoothTransition.contDiff.comp ((contDiff_const.sub hsm).div_const _), fun ξ => ?_,
    fun ξ hξ => ?_, ξ0 / 2, by positivity, fun ξ hξ => ?_⟩
  · have : vecDot (-ξ) (-ξ) = vecDot ξ ξ := by
      unfold vecDot
      exact Finset.sum_congr rfl fun i _ => by simp
    simp only [this]
  · apply Real.smoothTransition.zero_of_nonpos
    have h2 : ξ0 ^ 2 ≤ vecDot ξ ξ := by
      have := pow_le_pow_left₀ hξ0.le hξ 2
      rwa [Real.sq_sqrt (hdot0 ξ)] at this
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  · apply Real.smoothTransition.one_of_one_le
    have h2 : vecDot ξ ξ ≤ (ξ0 / 2) ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hξ 2
      rwa [Real.sq_sqrt (hdot0 ξ)] at this
    rw [le_div_iff₀ hd]
    nlinarith

/-- `1/(1 + Σ_b 1/f b) ≤ f a` for positive `f`. -/
theorem one_div_one_add_sum_le {β : Type*} {S : Finset β} {f : β → ℝ} (hf : ∀ b ∈ S, 0 < f b)
    {a : β} (ha : a ∈ S) : 1 / (1 + ∑ b ∈ S, 1 / f b) ≤ f a := by
  have h1 : 1 / f a ≤ ∑ b ∈ S, 1 / f b :=
    Finset.single_le_sum (fun b hb => (one_div_pos.2 (hf b hb)).le) ha
  have h2 : 0 < 1 / f a := one_div_pos.2 (hf a ha)
  calc 1 / (1 + ∑ b ∈ S, 1 / f b) ≤ 1 / (1 / f a) :=
        one_div_le_one_div_of_le h2 (by linarith)
    _ = f a := one_div_one_div _

theorem one_div_one_add_sum_pos {β : Type*} {S : Finset β} {f : β → ℝ} (hf : ∀ b ∈ S, 0 < f b) :
    0 < 1 / (1 + ∑ b ∈ S, 1 / f b) :=
  one_div_pos.2 (by
    have := Finset.sum_nonneg fun b hb => (one_div_pos.2 (hf b hb)).le
    linarith)

/-- The body of the seam statement from the seam's bodies of the allocations with uniform constants. -/
theorem seamAllocationBody_of (hcongr : PlaneChainMetricCongrStatement.{u, v})
    (hclamp : ClampedMetricStatement) (hshrink : PackageBufferShrinkStatement)
    (hU : WordChainUniqueStatement.{u, v})
    {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (heE : ∀ m : ℕ, 2 ≤ m → ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    {Kc : ScalarConstants} {Θ₀ g₁s : ℝ} (hcl : ScalarPackageClause α q Λ ζ Kc Θ₀) (hΘ₀ : 1 ≤ Θ₀)
    {D H Kmax Ks Jpre Jpost Mb pout Q Ns Ls Jm qJ Jchart : ℕ} (hchart : Kmax + D + 2 ≤ Jchart)
    (hD : 2 ≤ D) {Ca Cs Cpad Cage : ℝ} {Cm CG Cchart : ℕ → ℝ} {Jstar : ℕ} {CL : ℝ}
    (hLb : BlockLettersBody.{u, v, w, x} D Kmax Ks Ls Jm Jchart qJ Jstar Ca Cm Cchart CG CL)
    (hCL : 0 ≤ CL) {CU : ℝ}
    (hTb : BlockTransitionBody.{u, v, w, x, v} Kmax Jchart Cchart CG Cpad Cage CU)
    {χm : Vec 2 → ℝ} (hχs : ContDiff ℝ (⊤ : ℕ∞) χm)
    (hχsupp : ∀ ξ, 2 * Kc.ξlo ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0)
    (Qf qf : List Bool × List Bool → ℕ) (cf : List Bool × List Bool → ℝ)
    (CMf CNf : List Bool × List Bool → ℕ → ℝ)
    (hbody : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      SeamPairBody.{u, v} Kc g₁s D H Kmax pout (seamOrderK D Kmax σ.1) σ.1.length σ.2.length
        (wordOrders D σ.1) (wordSlow Ks σ.1) (wordPositive σ.1) (wordOrders D σ.2)
        (wordSlow Ks σ.2) (wordPositive σ.2) (Qf σ) Mb Ns (qf σ) 1 1 Cs CU 1 χm (cf σ) (CMf σ)
        (CNf σ))
    (hCMf : ∀ σ M, 0 < CMf σ M) (hCNf : ∀ σ N, 0 < CNf σ N)
    (hQ : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H, Qf σ ≤ Q)
    (hqΥ : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H, qf σ ≤ Jchart + 1)
    {c : ℝ} (hc : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H, c ≤ cf σ)
    (hR : ∀ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      seamReserve D Kmax pout Ks σ.1 σ.2 ≤ Jstar)
    (Cth : ℝ) {CM CN : ℝ}
    (hCM : ∀ M ≤ Mb, ∑ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      CMf σ M * (CL * max 1 (max Cth 0)) ^ (σ.1.length + σ.2.length) ≤ CM)
    (hCN : ∑ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      CNf σ Ns * (CL * max 1 (max Cth 0)) ^ (σ.1.length + σ.2.length) ≤ CN)
    (hNs : 1 ≤ Ns) :
    SeamAllocationBody.{u, v, w, x} α q Λ hζ (min (min g₁s Kc.g0) (1 / 4))
      (max Θ₀ (3 * max Kc.θs 1)) D H Kmax Ks Jpre Jpost Mb pout Q Ns Ls Jm qJ Jchart hchart
      Ca Cs Cpad Cage Cm CG Cchart CL Cth CM CN c := by
  intro g₀ Cb COld Crat Npad mStar hΛ1 ι _ _ h _ _ _ _ _ _ π K Φ M' κ m ν B hφ tS g a B₀ lam l₀
    P y₀ P' Ctx F actual A Θ T r ρold hp hg₀ hθ hgU hlong hbudget
  exact seamAllocation_family hcongr hclamp hshrink hU hp hΛ1 hchart hζ hD (heE m hp.hm2) hcl hΘ₀
    hLb hCL hTb hχs hχsupp Qf qf cf CMf CNf hbody hCMf hCNf hQ hqΥ hc hR hCM hCN hNs hg₀ hθ hgU
    hlong hbudget

/-- **The seam on the two blocks from its ingredients.** -/
theorem seamAllocation_of_ingredients (hseam : CycleSeamStatement.{u, v})
    (hshrink : PackageBufferShrinkStatement) (hcongr : PlaneChainMetricCongrStatement.{u, v})
    (hclamp : ClampedMetricStatement) (hU : WordChainUniqueStatement.{u, v}) :
    SeamAllocationStatement.{u, v, w, x} := by
  intro α s q hα0 hα1 hs0 hs1 hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, hpk⟩ := scalarPackage_clause α s hα0 hα1 hs0 hs1 q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ?_⟩
  have heE : ∀ m : ℕ, 2 ≤ m → ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) := by
    intro m hm
    have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
    have h1 := (Scales.admissible_space_scale_facts hq h128 (by omega : 1 ≤ m)).2.2.1
    have hE := (Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1)
      (by omega : 1 ≤ Λ)).le
    exact h1.trans (div_le_self hE (by norm_num))
  obtain ⟨g₀p, ξ₀, ξmax, cG, CgG, hg₀p, hξmax, hξ, -, -, hK⟩ := hpk Λ hΛ
  obtain ⟨Kc, Θ₀, hξloeq, hg0eq, -, -, -, hΘ₀, hcl⟩ := hK (ξmax / 2) (by linarith) (by linarith)
  have hξlo : 0 < 2 * Kc.ξlo := by rw [hξloeq]; linarith
  obtain ⟨χm, hχs, hχe, hχsupp, hχone⟩ := exists_seam_cutoff hξlo
  obtain ⟨g₁s, hg₁s, hS1⟩ := cycleSeam_body hseam Kc
  refine ⟨min (min g₁s Kc.g0) (1 / 4), max Θ₀ (3 * max Kc.θs 1),
    lt_min (lt_min hg₁s (hg0eq ▸ hg₀p)) (by norm_num),
    fun D H Kmax Ks Jpre Jpost Mb pout hD => ?_⟩
  choose Qf hQf using fun σ : List Bool × List Bool => hS1 D H Kmax pout (seamOrderK D Kmax σ.1)
    hD σ.1.length σ.2.length (wordOrders D σ.1) (wordSlow Ks σ.1) (wordPositive σ.1)
    (wordOrders D σ.2) (wordSlow Ks σ.2) (wordPositive σ.2) le_rfl
  obtain ⟨Rf, hRf⟩ : ∃ Rf : List Bool × List Bool → ℕ,
      Rf = fun σ => seamReserve D Kmax pout Ks σ.1 σ.2 := ⟨_, rfl⟩
  refine ⟨(blockWords Jpre H ×ˢ blockWords Jpost H).sup Qf,
    (blockWords Jpre H ×ˢ blockWords Jpost H).sup Rf, fun Ns hNs => ?_⟩
  choose qf hqf using fun σ => hQf σ Mb Ns
  refine ⟨(blockWords Jpre H ×ˢ blockWords Jpost H).sup qf,
    fun Ls Jm qJ Jchart hchart hJs hqJ hJc hqΥ Ca Cs Cpad Cage Cm CG Cchart => ?_⟩
  have hL5 := blockLetters_body blockLetters.{u, v, w, x} D Kmax Ks Ls Jm Jchart qJ _ hJs hqJ hJc
    Ca Cm Cchart CG
  obtain ⟨CL, hCL, hLb⟩ := hL5
  have hT5 := blockTransition_body blockTransition.{u, v, w, x, v} Kmax Jchart Cchart CG
    Cpad Cage
  obtain ⟨CU, _hCU, hTb⟩ := hT5
  choose cf CMf CNf hcf using fun σ => hqf σ 1 1 Cs CU 1 one_pos one_pos χm hχs hχe hχsupp hχone
  refine ⟨CL, hCL, fun Cth => ?_⟩
  have hC : 0 ≤ CL * max 1 (max Cth 0) := mul_nonneg hCL (zero_le_one.trans (le_max_left _ _))
  refine ⟨∑ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      ∑ M ∈ Finset.range (Mb + 1), CMf σ M * (CL * max 1 (max Cth 0)) ^ (σ.1.length + σ.2.length),
    ∑ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H,
      CNf σ Ns * (CL * max 1 (max Cth 0)) ^ (σ.1.length + σ.2.length),
    1 / (1 + ∑ σ ∈ blockWords Jpre H ×ˢ blockWords Jpost H, 1 / cf σ),
    Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun M _ =>
      mul_nonneg ((hcf σ).2.1 M).le (pow_nonneg hC _),
    Finset.sum_nonneg fun σ _ => mul_nonneg ((hcf σ).2.2.1 Ns).le (pow_nonneg hC _),
    one_div_one_add_sum_pos fun σ _ => (hcf σ).1, ?_⟩
  exact seamAllocationBody_of hcongr hclamp hshrink hU hζ heE hcl hΘ₀ hchart hD hLb hCL hTb hχs
    hχsupp Qf qf cf CMf CNf (fun σ _ => (hcf σ).2.2.2) (fun σ => (hcf σ).2.1)
    (fun σ => (hcf σ).2.2.1) (fun σ hσ => Finset.le_sup hσ)
    (fun σ hσ => (Finset.le_sup (f := qf) hσ).trans hqΥ)
    (fun σ hσ => one_div_one_add_sum_le (fun σ' _ => (hcf σ').1) hσ)
    (fun σ hσ => le_of_eq_of_le (congrFun hRf σ).symm (Finset.le_sup hσ)) Cth
    (fun M hM => Finset.sum_le_sum fun σ _ =>
      Finset.single_le_sum (f := fun M' => CMf σ M' * (CL * max 1 (max Cth 0)) ^
        (σ.1.length + σ.2.length))
        (fun M' _ => mul_nonneg ((hcf σ).2.1 M').le (pow_nonneg hC _))
        (Finset.mem_range.2 (Nat.lt_succ_of_le hM)))
    le_rfl hNs

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The one-patch statement with smooth models**.

`PatchJointGenSmoothStatement`: the one-patch statement (`PatchJointGenStatement`) with the smooth models
of the patches (`PatchSmoothModel`: slot `K`, and for a family without edges the agreeing slot-`0`
model of the edge-free clause) as conclusion; the extension to `L²` data (`PlaneModelExtensionStatement`) is added
separately. The orders are chosen from the accuracy: the slow order `Ks` (also the word lengths)
makes the retained endpoints of the two-block theorem and the seam price beat `E^{2 Pacc}` after the interpolation
`θ = 1/2` (moment orders `4 ≤ 8`) and the radius conversion `E^{-2qδ Kmax}`; the constants come
next, and the starting level makes `E` small enough for the gains, the strain, the pulse length and
the seam budget.

`patchJointGenSmooth`: proved from the moment-weighted pullback, `cycle_seam` and the
word-chain uniqueness, with the two-block theorem, the moments, the mass interpolation and seam allocation, and the price ledger.

For an empty family there are no models and the statement is trivial; when `Pacc` is small, `Ks`
comes from the radius conversion alone. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev Set
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
  AVRegularity.CycleReference
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- A threshold for a positive power. -/
theorem small_rpow_threshold {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ E : ℝ, 0 ≤ E → E ≤ E₀ → E ^ p ≤ t :=
  ⟨t ^ (1 / p), Real.rpow_pos_of_pos ht _, fun _ hE h => rpow_le_of_le_root hE hp ht h⟩

/-- A smooth patch model (with the edge-free clause) for an empty family. -/
theorem patchSmoothModel_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Mout Mb D : ℕ) (C c ε : ℝ)
    (n : ℕ) (π : ι → ℝ) (K : ι → ℕ) (ν tS tp ρs ρold R : ℝ) (N : ℕ) (hN : 0 < N)
    (j : Fin 2 → Fin N) (y : Vec 2) (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (A0 : ∀ (i i' : ι) (d : admissibleOrders (fun _ => 0) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))) (edgeFree : Prop) :
    PatchSmoothModel hζ Mout Mb D C c ε n π K ν tS tp ρs ρold R N hN j y b A A0 edgeFree :=
  ⟨0, fun _ => by simp only [Finset.univ_eq_empty, LinearMap.zero_apply, Pi.zero_apply, Finset.sum_empty,
      ← ClosedSubmodule.norm_coe, mul_zero, ENNReal.ofReal_zero, Std.le_refl],
    fun _ _ _ _ => by simp only [Finset.univ_eq_empty, LinearMap.zero_apply, Pi.zero_apply, ContinuousLinearMap.map_zero, sub_zero,
      Finset.sum_empty, mul_zero, ENNReal.ofReal_zero, Std.le_refl],
    fun _ => ⟨0, fun _ => funext fun i => isEmptyElim i,
    fun _ => by simp only [Finset.univ_eq_empty, LinearMap.zero_apply, Pi.zero_apply, Finset.sum_empty,
      ← ClosedSubmodule.norm_coe, mul_zero, ENNReal.ofReal_zero, Std.le_refl],
    fun _ _ _ _ => by simp only [Finset.univ_eq_empty, LinearMap.zero_apply, Pi.zero_apply, ContinuousLinearMap.map_zero, sub_zero,
      Finset.sum_empty, mul_zero, ENNReal.ofReal_zero, Std.le_refl]⟩⟩

/-- **The one-patch statement with smooth models**:`PatchJointGenStatement` with the smooth models of the patches
(slot `K`, and the slot-`0` model of the edge-free clause) as conclusion (model order
`Mb ≥ max Mout Kmax`, model radius `c R`). -/
def PatchJointGenSmoothStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧ g₀ ≤ 1 / 8 ∧
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (Mout H D Kmax : ℕ), 2 ≤ D →
      ∃ (Ks Ls Jm qJ Jchart : ℕ), Kmax + D + 2 ≤ Jchart ∧ Kmax + D + 2 ≤ Jm ∧
      ∀ (Ca Cth Cb COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad : ℕ),
      ∃ (C CP c : ℝ) (mStar n Mb : ℕ), 0 < c ∧ 0 ≤ C ∧ 0 ≤ CP ∧ 4 ≤ n ∧ Mout ≤ Mb ∧
        Kmax ≤ Mb ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (r ρold : ℝ),
        JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
          Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
          A Θ T r ρold →
        ∀ (N : ℕ) (hN : 0 < N), 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m) →
          ∀ j : Fin 2 → Fin N,
          PatchSmoothModel hζ Mout Mb D C c (CP * ocEpsilon q Λ (m - 1) ^ Pacc) n π K ν tS
            (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) r ρold (Real.sqrt (B * ocTauPP α q Λ m)) N hN j
            (patchOutputCentre (Φ (m - 1)) hφ tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) N j)
            (streamVel (Φ m)) (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
            (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (fun _ => 0))
            (∀ v u, IsEmpty (F.Γ v u))

/-- The squared accuracy constant of the one-patch statement (level-independent form, chart jets at `E = 1`). -/
def b1AccuracySq (Cchart : ℕ → ℝ) (Jchart Kmax Mb Npre : ℕ) (Crat CN Cs CM : ℝ)
    (K2 qm : ℝ) : ℝ :=
  (2 * (compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) ^ 2 * K2 *
      datumEnergyPrice Cchart 1 Jchart Npre + returnConstant Cchart 1 Kmax 0 * (CN * Cs) ^ 2) *
      max 1 Crat ^ (2 * Kmax)) ^ (1 - (4 : ℝ) / 8) *
    (2 * (returnConstant Cchart 1 Kmax 8 * (qm * datumEnergyPrice Cchart 1 Jchart Npre) +
      patchModelConstant Cchart 1 8 Mb CM) * max 1 Crat ^ (2 * Kmax)) ^ ((4 : ℝ) / 8)

theorem le_sqrt_sq_self (y : ℝ) : y ≤ Real.sqrt y ^ 2 := by
  rcases le_or_gt 0 y with hy | hy
  · rw [Real.sq_sqrt hy]
  · rw [Real.sqrt_eq_zero'.2 hy.le]
    nlinarith

/-- **The slot-`K` part of the one-patch statement, for the families at one `Λ`.** -/
theorem b1k_family (hW : WeightedPullbackStatement.{v}) {α s q : ℝ} (hq : IsAdmissibleQ α s q)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) {Λ Λ₀ Λ₀' : ℕ} (hΛ₀ : Λ₀ ≤ Λ) (hΛ₀' : Λ₀' ≤ Λ)
    (hΛ128 : 128 ≤ Λ) {g₀ : ℝ} (hg₀ : g₀ ≤ 1 / 32) {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm) (hD : 2 ≤ D)
    (hKs : Ks + 1 ≤ Jm) (hqJ : Ks + 1 + Kmax ≤ qJ)
    {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
    {Cw : ℕ → ℝ} {Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem : ℝ} {Npre Npost Lpre Lpost : ℕ}
    (hC2 : TwoBlockJointBody.{u, v, w, x} α q hζ Cw Λ₀ D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem Npre Npost Lpre Lpost)
    {g₁ Θlong : ℝ} {Mb Q Ns : ℕ} {CL CM CN c : ℝ}
    (hG2 : SeamAllocationBody.{u, v, w, x} α q Λ hζ g₁ Θlong D H Kmax Ks Ks Ks Mb 8 Q Ns Ls
      Jm qJ Jchart hchart Ca ((1 + max (Cchart 0) 0 / 2) / 8) Cpad Cage Cm CG Cchart CL Cth CM CN
      c)
    {Cw' : ℕ → ℝ} {Cenergy1' Cprep' CTm : ℝ}
    (hG4 : TwoBlockMomentBody.{u, v, w, x} α q hζ Cw' Λ₀' D Ks Kmax Jchart Jm hchart Cm Cchart CG
      Cenergy1' Cprep' CTm 8 Npre)
    (hCe1 : 0 ≤ Cenergy1) (hCe2 : 0 ≤ Cenergy2) (hCprep : 0 ≤ Cprep) (hCT : 0 ≤ CT)
    (hCR : 0 ≤ CR) (hCterm : 0 ≤ Cterminal) (hCrem : 0 ≤ Crem) (hCN : 0 ≤ CN) (hCM : 0 ≤ CM)
    (hCTm : 0 ≤ CTm) (hCprep' : 0 ≤ Cprep') (hCe1' : 0 ≤ Cenergy1')
    (hNpre : Npost + (Ks + 1) + (Ks + H) * (Ks + 1) ≤ Npre)
    (hNpost : (Ks + 1) + (Ks + H) * (Ks + 1) ≤ Npost)
    (hNpre' : (Ks + 1) + H * (Ks + 1) ≤ Npre)
    (hg₀₁ : g₀ ≤ g₁ / 2) (hg₁0 : 0 < g₁)
    (Cl Cs as E₀ : ℝ)
    (hLed : ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ → ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
        Real.sqrt (B * ocTauPP α q Λ m) ≤ Cl * ocEpsilon q Λ (m - 1) ^ (1 + ocC α q) ∧
        Cl⁻¹ * ocEpsilon q Λ (m - 1) ^ (-(6 * ocDelta α q)) ≤
          ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 ∧
        Real.sqrt (B / ν) ≤ Cl * ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)) ∧
        ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ Cl * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) ∧
        ocEll q Λ m ν ^ 2 / ocTau α q Λ m ≤ Cl * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) ∧
        ocTauPP α q Λ m / ocTau α q Λ m ≤ Cl * ocEpsilon q Λ (m - 1) ^ (-(2 * ocDelta α q)))
    (hSL : ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B → 0 < ν →
        ocEll q Λ m ν ^ 2 ≤ ocTauPP α q Λ m →
        seamWindowPrice α q Λ m ν B Q Ns c ≤ Cs * ocEpsilon q Λ (m - 1) ^ as)
    (hm₀ : ∀ m : ℕ, mStar ≤ m → ocEpsilon q Λ (m - 1) ≤ E₀)
    (hT1 : ∀ E : ℝ, 0 ≤ E → E ≤ E₀ → CT * Cl * E ^ ocC α q ≤ 1)
    (hT1' : ∀ E : ℝ, 0 ≤ E → E ≤ E₀ → CTm * Cl * E ^ ocC α q ≤ 1)
    (hT2 : ∀ E : ℝ, 0 ≤ E → E ≤ E₀ → Cl * E ^ (2 * ocDelta α q) ≤ g₁ / 2)
    (hT3 : ∀ E : ℝ, 0 ≤ E → E ≤ E₀ → Θlong * (Cl * E ^ (4 * ocDelta α q)) ≤ 1)
    (hT4 : ∀ E : ℝ, 0 ≤ E → E ≤ E₀ → Cs * E ^ as ≤ 1)
    (hk : ocC α q * ((2 * (Ks + 1) : ℕ) : ℝ) ≤ 2 * as) (hcC : 0 ≤ ocC α q)
    (hqδ : 0 ≤ q * ocDelta α q)
    (Pacc : ℝ) (hP : 2 * Pacc ≤ (1 - (4 : ℝ) / 8) *
      (ocC α q * ((2 * (Ks + 1) : ℕ) : ℝ) - 2 * (q * ocDelta α q) * Kmax) -
        (4 : ℝ) / 8 * (2 * (q * ocDelta α q) * Kmax))
    (Mout : ℕ) (hMb : Mb ≤ Jchart + 1) (hMoutb : Mout ≤ Mb) (hKb : Kmax ≤ Mb)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (r ρold : ℝ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (N : ℕ) (hN : 0 < N) (hNR : 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m))
    (j : Fin 2 → Fin N) :
    PatchSmoothModel hζ Mout Mb D (Real.sqrt (patchModelConstant Cchart 1 8 Mb CM)) 1
      (Real.sqrt (b1AccuracySq Cchart Jchart Kmax Mb Npre Crat CN Cs CM
        (c2RemainingConstant.{u, v} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR Cterminal Crem
          (max Cth 0) Cl Npre Npost Lpre Lpost Ks Ks).toReal
        (twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0) 8 *
          energyConstant.{u, v} Cw' Kmax D H CG Cenergy1' (max Cth 0) Npre).toReal) *
        ocEpsilon q Λ (m - 1) ^ Pacc) 4 π K ν tS
      (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) r ρold (Real.sqrt (B * ocTauPP α q Λ m)) N hN j
      (patchOutputCentre (Φ (m - 1)) hφ tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) N j)
      (streamVel (Φ m)) (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (fun _ => 0))
      (∀ v u, IsEmpty (F.Γ v u)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact patchSmoothModel_of_isEmpty hζ _ _ _ _ _ _ _ π K _ _ _ _ _ _ N hN j _ _ _ _ _
  have hΛ : 1 ≤ Λ := le_trans (by norm_num) hΛ128
  have hCth : 0 ≤ Cth * Θ := by
    obtain ⟨v⟩ := hι
    exact (Finset.sum_nonneg fun u _ => hp.henv.nonneg v u).trans (hp.henv.row_sum v)
  have hM1 : 1 ≤ M' := le_trans (by omega) (hp.hm2.trans hp.hmM)
  obtain ⟨hR, -, -, hAt, hell, -⟩ := hLed M' hM1 κ hp.hband m hp.hm2 hp.hmM ν B hp.hν hp.hB
  have hsp := hSL M' hM1 κ hp.hband m hp.hm2 hp.hmM ν B hp.hν hp.hB hp.cov.pos.1 hp.cov.ellT
  have hE0 := (Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ).le
  have hEs := hm₀ m hp.hmStar
  obtain ⟨-, hE1, -⟩ := Scales.epsilon_basic (q := q) (m := m - 1) hq.1 hΛ128
  have hmax : ∀ i, max Mout (K i) ≤ Mb := fun i => max_le hMoutb ((hp.hK i).trans hKb)
  have hCP : b1AccuracySq Cchart Jchart Kmax Mb Npre Crat CN Cs CM
      (c2RemainingConstant.{u, v} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR Cterminal Crem
        (max Cth 0) Cl Npre Npost Lpre Lpost Ks Ks).toReal
      (twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0) 8 *
        energyConstant.{u, v} Cw' Kmax D H CG Cenergy1' (max Cth 0) Npre).toReal ≤
      Real.sqrt (b1AccuracySq Cchart Jchart Kmax Mb Npre Crat CN Cs CM
        (c2RemainingConstant.{u, v} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR Cterminal Crem
          (max Cth 0) Cl Npre Npost Lpre Lpost Ks Ks).toReal
        (twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0) 8 *
          energyConstant.{u, v} Cw' Kmax D H CG Cenergy1' (max Cth 0) Npre).toReal) ^ 2 :=
    le_sqrt_sq_self _
  unfold b1AccuracySq at hCP
  rw [← returnConstant_level Cchart (ocEpsilon q Λ (m - 1)) 1,
    ← returnConstant_level Cchart (ocEpsilon q Λ (m - 1)) 1,
    ← datumEnergyPrice_level Cchart (ocEpsilon q Λ (m - 1)) 1,
    ← patchModelConstant_level Cchart (ocEpsilon q Λ (m - 1)) 1] at hCP
  rw [patchModelConstant_level Cchart 1 (ocEpsilon q Λ (m - 1))]
  exact family_of_parts massInterpolation hW hq hΛ₀ hΛ₀' hΛ128 hΛ hg₀ hchart hmol hD hKs hqJ hζ
    hC2 hG2 hG4 hCe1 hCe2 hCprep hCT hCR hCterm hCrem hCN hCM hCTm hCprep' hCe1' hp hNpre hNpost
    hNpre' hg₀₁ hg₁0 hCth Cl Cs as hE1 hR hAt hell hsp hk (hT1 _ hE0 hEs) (hT1' _ hE0 hEs)
    (hT2 _ hE0 hEs) (hT3 _ hE0 hEs) (hT4 _ hE0 hEs) hcC hqδ Pacc hP _ hCP Mout hMb hmax hMoutb N hN
    hNR j

/-- A threshold for `a E^p ≤ b`. -/
theorem threshold_mul_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hp : 0 < p) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ E : ℝ, 0 ≤ E → E ≤ E₀ → a * E ^ p ≤ b := by
  obtain ⟨E₀, hE₀, h⟩ := small_rpow_threshold hp (div_pos hb (by linarith : (0 : ℝ) < a + 1))
  refine ⟨E₀, hE₀, fun E hE hEE => ?_⟩
  have h1 := mul_le_mul_of_nonneg_left (h E hE hEE) ha
  have h2 : a * (b / (a + 1)) ≤ b := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- **The slot-`K` part of the one-patch statement.** -/
theorem patchJointGenSmooth (hW : WeightedPullbackStatement.{v})
    (hseam : CycleSeamStatement.{u, v}) (hU : WordChainUniqueStatement.{u, v}) :
    PatchJointGenSmoothStatement.{u, v, w, x} := by
  intro α s hα0 hα1 hs0 hs1 q hq ζ hζ
  obtain ⟨Cw, Λ₀C, h128C, hC2⟩ := twoBlockJoint.{u, v, w, x} hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Λ₀S, h128S, hG2⟩ := seamAllocation_of_ingredients.{u, v, w, x} hseam packageBufferShrink
    planeChainMetricCongr clampedMetric hU hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cw', Λ₀M, h128M, hG4⟩ := twoBlockMoment.{u, v, w, x} hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cl, hCl1, Λ₀L, h128L, hLed⟩ := b1_scale_ledger hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Λ₀P, h128P, hSL⟩ := seamWindowPrice_ledger hα0 hα1 hs0 hs1 hq hζ
  have hex := Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have hcC : 0 < ocC α q := hex.2.2.2.2.2
  have hδ : 0 < ocDelta α q := hex.2.1
  have hqδ : 0 ≤ q * ocDelta α q := mul_nonneg (lt_trans zero_lt_one hq.1).le hδ.le
  refine ⟨max (max (max Λ₀C Λ₀S) (max Λ₀M Λ₀L)) Λ₀P, le_max_of_le_right h128P,
    fun Λ hΛ => ?_⟩
  have hΛC : Λ₀C ≤ Λ := le_trans (by omega) hΛ
  have hΛS : Λ₀S ≤ Λ := le_trans (by omega) hΛ
  have hΛM : Λ₀M ≤ Λ := le_trans (by omega) hΛ
  have hΛL : Λ₀L ≤ Λ := le_trans (by omega) hΛ
  have hΛP : Λ₀P ≤ Λ := le_trans (le_max_right _ _) hΛ
  have hΛ128 : 128 ≤ Λ := h128P.trans hΛP
  obtain ⟨g₁, Θlong, hg₁0, hG2Λ⟩ := hG2 Λ hΛS
  refine ⟨min (g₁ / 2) (1 / 32), lt_min (by linarith) (by norm_num),
    (min_le_right _ _).trans (by norm_num), fun Pacc hPacc Mout H D Kmax hD => ?_⟩
  -- the orders
  obtain ⟨Ks, hKs⟩ : ∃ Ks : ℕ,
      Ks = ⌈(2 * Pacc + 2 * (q * ocDelta α q) * Kmax) / ocC α q⌉₊ := ⟨_, rfl⟩
  have hKsP : 2 * Pacc + 2 * (q * ocDelta α q) * Kmax ≤ ocC α q * Ks := by
    have h := Nat.le_ceil ((2 * Pacc + 2 * (q * ocDelta α q) * Kmax) / ocC α q)
    rw [div_le_iff₀ hcC, ← hKs] at h
    linarith
  obtain ⟨Q, Jstar, hG2Q⟩ := hG2Λ D H Kmax Ks Ks Ks (max Mout Kmax) 8 hD
  obtain ⟨Ns, hNs, hSLQ⟩ := hSL Q (ocC α q * (Ks + 1))
  obtain ⟨qΥ, hG2N⟩ := hG2Q Ns hNs
  refine ⟨Ks, Jstar, Kmax + D + 2 + Ks + 1, Ks + Jstar + Kmax + 1,
    Kmax + D + 2 + Ks + Jstar + qΥ + max Mout Kmax, by omega, by omega,
    fun Ca Cth Cb COld Crat Cm CG Cchart Cpad Cage Npad => ?_⟩
  have hchart : Kmax + D + 2 ≤ Kmax + D + 2 + Ks + Jstar + qΥ + max Mout Kmax := by omega
  have hmol : Kmax + D + 2 ≤ Kmax + D + 2 + Ks + 1 := by omega
  have hKsJ : Ks + D + 2 ≤ Kmax + D + 2 + Ks + Jstar + qΥ + max Mout Kmax := by omega
  -- the constants
  obtain ⟨Cenergy1, Cenergy2, Cprep, CT, CR, Cterminal, Crem, he1, he2, hCprep, hCT, hCR,
    hCterm, hCrem, hC2N⟩ := hC2 D Ks Kmax _ _ hchart hmol hKsJ Cm Cchart CG
  obtain ⟨Lpre, Lpost, -, -, hC2body⟩ := hC2N
    ((Ks + 1) + (Ks + H) * (Ks + 1) + (Ks + 1) + (Ks + H) * (Ks + 1) + 8)
    ((Ks + 1) + (Ks + H) * (Ks + 1))
  obtain ⟨CL, -, hG2Cth⟩ := hG2N Jstar (Kmax + D + 2 + Ks + 1) (Ks + Jstar + Kmax + 1)
    (Kmax + D + 2 + Ks + Jstar + qΥ + max Mout Kmax) hchart le_rfl (by omega) (by omega)
    (by omega) Ca ((1 + max (Cchart 0) 0 / 2) / 8) Cpad Cage Cm CG Cchart
  obtain ⟨CM, CN, c, hCM, hCN, hc, hG2body⟩ := hG2Cth Cth
  obtain ⟨Cenergy1', Cprep', CTm, he1', hCprep', hCTm, hG4n⟩ :=
    hG4 D Ks Kmax _ _ hchart hmol hKsJ Cm Cchart CG
  have hG4body := hG4n 8 ((Ks + 1) + (Ks + H) * (Ks + 1) + (Ks + 1) + (Ks + H) * (Ks + 1) + 8)
    (by omega)
  obtain ⟨Cs, hCs, hSLc⟩ := hSLQ c hc
  -- the thresholds
  have has : 0 < ocC α q * (Ks + 1) := mul_pos hcC (by positivity)
  have hCl0 : 0 < Cl := zero_lt_one.trans_le hCl1
  obtain ⟨E1, hE1, hT1⟩ := threshold_mul_le (mul_nonneg hCT hCl0.le) one_pos hcC
  obtain ⟨E2, hE2, hT1'⟩ := threshold_mul_le (mul_nonneg hCTm hCl0.le) one_pos hcC
  obtain ⟨E3, hE3, hT2⟩ := threshold_mul_le hCl0.le (by linarith : 0 < g₁ / 2)
    (by linarith : 0 < 2 * ocDelta α q)
  obtain ⟨E4, hE4, hT3⟩ := threshold_mul_le (mul_nonneg (le_max_right Θlong 0) hCl0.le) one_pos
    (by linarith : 0 < 4 * ocDelta α q)
  obtain ⟨E5, hE5, hT4⟩ := threshold_mul_le hCs one_pos has
  obtain ⟨m₀, hm₀⟩ := exists_level_small hq.1
    (lt_min (lt_min (lt_min hE1 hE2) (lt_min hE3 hE4)) hE5)
  refine ⟨Real.sqrt (patchModelConstant Cchart 1 8 (max Mout Kmax) CM),
    Real.sqrt (b1AccuracySq Cchart (Kmax + D + 2 + Ks + Jstar + qΥ + max Mout Kmax) Kmax
      (max Mout Kmax) ((Ks + 1) + (Ks + H) * (Ks + 1) + (Ks + 1) + (Ks + H) * (Ks + 1) + 8) Crat CN
      Cs CM
      (c2RemainingConstant.{u, v} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR Cterminal Crem
        (max Cth 0) Cl ((Ks + 1) + (Ks + H) * (Ks + 1) + (Ks + 1) + (Ks + H) * (Ks + 1) + 8)
        ((Ks + 1) + (Ks + H) * (Ks + 1)) Lpre Lpost Ks Ks).toReal
      (twoMomentPrice.{u, v} Cw' Kmax D H CG Cprep' (max Cth 0) 8 *
        energyConstant.{u, v} Cw' Kmax D H CG Cenergy1' (max Cth 0)
          ((Ks + 1) + (Ks + H) * (Ks + 1) + (Ks + 1) + (Ks + H) * (Ks + 1) + 8)).toReal),
    1, m₀, 4, max Mout Kmax, one_pos, Real.sqrt_nonneg _, Real.sqrt_nonneg _, le_rfl,
    le_max_left _ _, le_max_right _ _, ?_⟩
  intro ι _ _ h _ _ _ _ _ _ π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ P' Ctx F actual A Θ T r ρold
    hp N hN hNR j
  have hEmin : min (min (min E1 E2) (min E3 E4)) E5 ≤ E1 ∧ min (min (min E1 E2) (min E3 E4)) E5 ≤ E2 ∧
      min (min (min E1 E2) (min E3 E4)) E5 ≤ E3 ∧ min (min (min E1 E2) (min E3 E4)) E5 ≤ E4 ∧
      min (min (min E1 E2) (min E3 E4)) E5 ≤ E5 := by
    refine ⟨?_, ?_, ?_, ?_, min_le_right _ _⟩ <;>
    · simp only [min_le_iff, le_refl, true_or, or_true]
  have hH : H * (Ks + 1) ≤ (Ks + H) * (Ks + 1) := Nat.mul_le_mul_right _ (by omega)
  exact b1k_family hW hq hζ hΛC hΛM hΛ128 (min_le_right _ _) hchart hmol hD (by omega) (by omega)
    hC2body hG2body hG4body (by linarith) (by linarith) (by linarith) hCT hCR hCterm hCrem hCN hCM
    hCTm (by linarith) (by linarith) (by omega) (by omega) (by omega) (min_le_left _ _) hg₁0 Cl Cs
    (ocC α q * (Ks + 1)) (min (min (min E1 E2) (min E3 E4)) E5) (hLed Λ hΛL) (hSLc Λ hΛP)
    (fun m hm => hm₀ Λ hΛ128 m hm)
    (fun E hE hEE => hT1 E hE (hEE.trans hEmin.1))
    (fun E hE hEE => hT1' E hE (hEE.trans hEmin.2.1))
    (fun E hE hEE => hT2 E hE (hEE.trans hEmin.2.2.1))
    (fun E hE hEE => by
      have h := hT3 E hE (hEE.trans hEmin.2.2.2.1)
      have hEp : 0 ≤ Cl * E ^ (4 * ocDelta α q) :=
        mul_nonneg hCl0.le (Real.rpow_nonneg hE _)
      have := mul_le_mul_of_nonneg_right (le_max_left Θlong 0) hEp
      nlinarith only [h, hEp, this])
    (fun E hE hEE => hT4 E hE (hEE.trans hEmin.2.2.2.2))
    (by push_cast; linarith) hcC.le hqδ Pacc (by push_cast; linarith only [hKsP, hcC, hqδ]) Mout (by omega)
    (le_max_left _ _) (le_max_right _ _) π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T
    r ρold hp N hN hNR j

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The one-patch statement**.

`patchJointGen`: `PatchJointGenStatement` (the one-patch statement at an abstract radius) from the smooth models of the
patches (`patchJointGenSmooth`), extended to `L²` data by the plane-model extension
(`patchModelsGen_of_smooth`; the edge-free clause by the uniqueness of the extension). Hypotheses: the moment-weighted pullback,
`cycle_seam` and the word-chain uniqueness.

For an empty family there are no models and the statement is trivial. Patches with `N R` above `9`
are not asked for by the one-patch statement. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- **The one-patch statement** at an abstract radius. -/
theorem patchJointGen (hW : WeightedPullbackStatement.{v}) (hseam : CycleSeamStatement.{u, v})
    (hU : WordChainUniqueStatement.{u, v}) : PatchJointGenStatement.{u, v, w, x} := by
  intro α s hα0 hα1 hs0 hs1 q hq ζ hζ
  obtain ⟨Λ₀, h128, hΛ⟩ := patchJointGenSmooth.{u, v, w, x} hW hseam hU α s hα0 hα1 hs0 hs1 q hq
    ζ hζ
  refine ⟨Λ₀, h128, fun Λ hΛ₀ => ?_⟩
  obtain ⟨g₀, hg₀, hg₀8, hP⟩ := hΛ Λ hΛ₀
  refine ⟨g₀, hg₀, hg₀8, fun Pacc hPacc Mout H D Kmax hD => ?_⟩
  obtain ⟨Ks, Ls, Jm, qJ, Jchart, hchart, hmol, hC⟩ := hP Pacc hPacc Mout H D Kmax hD
  refine ⟨Ks, Ls, Jm, qJ, Jchart, hchart, hmol,
    fun Ca Cth Cb COld Crat Cm CG Cchart Cpad Cage Npad => ?_⟩
  obtain ⟨C, CP, c, mStar, n, Mb, hc, hC0, hCP, hn, hMo, hKb, hfam⟩ :=
    hC Ca Cth Cb COld Crat Cm CG Cchart Cpad Cage Npad
  refine ⟨C, CP, c, mStar, n, hc, hC0, hCP, hn, ?_⟩
  intro ι _ _ h _ _ _ _ _ _ π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ P' Ctx F actual A Θ T r
    ρold hp
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) (h128.trans hΛ₀)
  have hR : 0 < Real.sqrt (B * ocTauPP α q Λ m) :=
    Real.sqrt_pos.2 (mul_pos hp.cov.pos.2.1 (Construction.Stream.ocTauPP_pos hΛ1))
  exact patchModelsGen_of_smooth hζ hn π hp.hπ K
    (fun i => max_le hMo ((hp.hK i).trans hKb)) hMo ν tS _ r ρold _ hR hc _ _ _ _ _
    fun N hN h8 _ j => hfam π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T r ρold hp N
      hN h8 j

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **`cycle_joint` from `cycle_seam` and the word-chain uniqueness**.

the one-patch statement (`patchJointGen`, at the cascade radius by `patchJoint_of_gen`) with the moment-weighted
pullback (`weightedPullback`), the plane-solution statement (`planeTorus`) and the path reduction
(`pathReduction`) give `cycle_joint` through `cycle_joint_of_remaining`. The two hypotheses are
the statement of `cycle_seam` (restated as `CycleSeamStatement`) and the uniqueness of word chains
(`WordChainUniqueStatement`). The second hypothesis is proved (`wordChainUnique`), and
`cycle_joint_of_cycleSeam` discharges it. -/

@[expose] public section

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- **`cycle_joint` from `cycle_seam` and uniqueness of word chains.** -/
theorem cycle_joint_of_seam (hseam : CycleSeamStatement.{0, v})
    (hU : WordChainUniqueStatement.{0, v}) : CycleJointStatement.{u, v, w, x} :=
  cycle_joint_of_remaining (patchJoint_of_gen (patchJointGen weightedPullback hseam hU))
    planeTorus pathReduction

/-- **`cycle_joint` from `cycle_seam` alone** (uniqueness of word chains is `wordChainUnique`). -/
theorem cycle_joint_of_cycleSeam (hseam : CycleSeamStatement.{0, v}) :
    CycleJointStatement.{u, v, w, x} :=
  cycle_joint_of_seam hseam wordChainUnique

end AVRegularity.CycleJointProofs.Assembly
end
end
