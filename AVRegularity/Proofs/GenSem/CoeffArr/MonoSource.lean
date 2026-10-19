-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.CoeffArr.FluxX
public import AVRegularity.Proofs.GenSem.ChainMetric

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Providers.GenSem

/-! **The coefficient array of `liftCellSource`.** For scalar fibres and the test field
`fun _ Y => Pi.single w (a Y)`, `liftCellSource Q Cc · hh n t X z v` is the applied array
`applyArr (n+1) (srcArr Q Cc w hh n t v) a X z`. -/

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

/-- **`A_n^{(hh)}` of the test field is an applied array.** -/
theorem liftA_apply (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} {t : ℝ} {a : Vec 2 → ℝ}
    (hreg : LiftRegular Q Cc w t hh n (n + Dm + 2))
    (ha : ContDiff ℝ ((n + Dm + 1 : ℕ) : WithTop ℕ∞) a) (X z : Vec 2) (v : ι) :
    liftA Q Cc (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) hh n t X z v =
      applyArr (n + 1) (liftAArr Q Cc w hh n t v) a X z := by
  have hent : ∀ hh' k, hh' ≤ hh → k ≤ n → ∀ u,
      ArrSmooth (n + Dm + 2) (entryArr (Cc hh' k) k w t u) := fun hh' k h1 h2 u =>
    arrSmooth_entryArr _ _ _ _ _ (hreg.coeff hh' h1 k h2 · · u)
  have hΦ : ∀ hh' k, k ≤ n → liftApply k (Cc hh' k) (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) t =
      fun X z v => applyArr k (entryArr (Cc hh' k) k w t v) a X z := by
    intro hh' k hk
    funext X z v
    exact liftApply_single k _ w (ha.of_le (by exact_mod_cast (by omega : k ≤ n + Dm + 1))) t X z v
  have hG : ∀ i j, ContDiff ℝ (1 : ℕ) (fun p : Vec 2 × Vec 2 => Q.G t p.1 i j) := fun i j =>
    (hreg.metric i j).of_le (by exact_mod_cast (by omega : 1 ≤ n + Dm + 2))
  have e1 : cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1))
        (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) t) X z v =
      applyArr (n + 1) (cellB1Arr Q.η Q.G Q.v t (entryArr (Cc hh (n - 1)) (n - 1) w t v)) a X z := by
    rw [hΦ hh (n - 1) (by omega), cellB1_apply Q.η Q.G Q.v t (K := n - 1)
      (ha.of_le (by exact_mod_cast (by omega : n - 1 + 1 ≤ n + Dm + 1)))
      (fun u => (hent hh (n - 1) le_rfl (by omega) u).mono (by omega))
      (fun u => arrSupp_entryArr _ _ _ _ _) hG X z v]
    exact (congrFun (congrFun (applyArr_eq_of_supp (K := n - 1 + 1) (K' := n + 1) (by omega)
      (arrSupp_cellB1Arr Q.η Q.G Q.v t (arrSupp_entryArr _ _ _ _ _)) a) X) z).symm
  have e2 : (if 2 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2))
        (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) t) X z else 0) v =
      applyArr (n + 1) (if 2 ≤ n then cellB2Arr Q.η Q.G t
        (entryArr (Cc hh (n - 2)) (n - 2) w t v) else 0) a X z := by
    by_cases h2 : 2 ≤ n
    · simp only [h2, ite_true]
      rw [hΦ hh (n - 2) (by omega), cellB2_apply Q.η Q.G t (K := n - 2)
        (ha.of_le (by exact_mod_cast (by omega : n - 2 + 2 ≤ n + Dm + 1)))
        (fun u => (hent hh (n - 2) le_rfl (by omega) u).mono (by omega))
        (fun u => arrSupp_entryArr _ _ _ _ _) hG X z v]
      exact (congrFun (congrFun (applyArr_eq_of_supp (K := n - 2 + 2) (K' := n + 1) (by omega)
        (arrSupp_cellB2Arr Q.η Q.G t (arrSupp_entryArr _ _ _ _ _)) a) X) z).symm
    · simp [h2, applyArr_zero]
  have e3 : (if hh = 0 then (0 : ι → ℝ) else ∑ j ∈ Finset.range (min Dm n + 1),
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j))
          (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) t) X z) v = 
      applyArr (n + 1) (if hh = 0 then 0 else ∑ j ∈ Finset.range (min Dm n + 1),
        sourceG Q.edge (Real.sqrt Q.η) t (fun u => entryArr (Cc (hh - 1) (n - j)) (n - j) w t u) v j)
        a X z := by
    by_cases h0 : hh = 0
    · simp [h0, applyArr_zero]
    · simp only [h0, ite_false]
      rw [applyArr_sum]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      have hjD : j ≤ Dm := by omega
      have hjn : j ≤ n := by omega
      rw [hΦ (hh - 1) (n - j) (by omega), sourceCoeff_apply Q.edge Q.η hjD t (K := n - j)
        (A := fun u => entryArr (Cc (hh - 1) (n - j)) (n - j) w t u)
        (ha.of_le (by exact_mod_cast (by omega : n - j + Dm + 1 ≤ n + Dm + 1)))
        (fun u => (hent (hh - 1) (n - j) (by omega) (by omega) u).mono (by omega))
        (fun u => arrSupp_entryArr _ _ _ _ _)
        (fun v u d γ hγ α k => (hreg.edge v u d γ hγ α k).of_le
          (by exact_mod_cast (by omega : 1 ≤ n + Dm + 2))) X z v]
      have hsupp := (sourceG_gSupp Q.edge (Real.sqrt Q.η) t
        (A := fun u => entryArr (Cc (hh - 1) (n - j)) (n - j) w t u)
        (fun u => arrSupp_entryArr _ _ _ _ _) v).1 j
      rw [show n - j + j = n by omega] at hsupp
      have h1 := congrFun (congrFun (applyArr_eq_of_supp (K := n) (K' := n - j + (Dm + 1))
        (by omega) hsupp a) X) z
      have h2 := congrFun (congrFun (applyArr_eq_of_supp (K := n) (K' := n + 1)
        (by omega) hsupp a) X) z
      rw [h1, h2]
  unfold liftA liftAArr
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [e1, e2, e3, applyArr_sub, applyArr_add]
  rfl

/-- **`L_n^{(hh)} = P_0 A_n^{(hh)}` of the test field**, component `u`, at any `z₀`. -/
theorem liftMean_apply (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} {t : ℝ} {a : Vec 2 → ℝ}
    (hreg : LiftRegular Q Cc w t hh n (n + Dm + 2))
    (ha : ContDiff ℝ ((n + Dm + 1 : ℕ) : WithTop ℕ∞) a) (X z0 : Vec 2) (u : ι) :
    liftMean Q Cc (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) hh n t X u =
      applyArr (n + 1) (meanArr (liftAArr Q Cc w hh n t u)) a X z0 := by
  have hA0 : ∀ u, ArrSmooth 0 (liftAArr Q Cc w hh n t u) := fun u =>
    arrSmooth_liftAArr Q Cc w (r := 0) (hreg.mono le_rfl le_rfl (by omega)) u
  have hfun : (fun z => liftA Q Cc (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) hh n t X z) =
      fun z u => applyArr (n + 1) (liftAArr Q Cc w hh n t u) a X z := by
    funext z u
    exact liftA_apply Q Cc w hreg ha X z u
  have hcont : Continuous
      (fun z => liftA Q Cc (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) hh n t X z) := by
    rw [hfun]
    exact continuous_pi fun u => continuous_applyArr_z (hA0 u) a X
  have hint := integrableOn_unitCube_of_continuous hcont
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) u).integral_comp_comm hint
  simp only [ContinuousLinearMap.proj_apply] at h
  unfold liftMean fieldCellMean
  rw [← h]
  have h2 := fieldCellMean_applyArr (n + 1) (liftAArr Q Cc w hh n t u) a X z0
    (fun m α => arrSmooth_integrableOn (hA0 u) m α X)
  rw [← h2]
  unfold fieldCellMean
  congr 1
  funext z
  exact congrFun (congrFun hfun z) u

/-! ### The coefficient array of the cell source -/

/-- **The coefficient array of `liftCellSource` for the test field `single w a`**, component `v`:
`-(A - P_0 A) + ∑_{j=1}^{n-2} ∑_{hh'+hh''=hh} ∑_u C_j^{(hh')}[v,u] ∘ P_0 A_{n-j}^{(hh'')}[u]`. -/
def srcArr (Q : LiftOperatorData ι (fun _ => ℝ) Dm) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) : CArr :=
  -(liftAArr Q Cc w hh n t v - meanArr (liftAArr Q Cc w hh n t v))
    + ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∑ u : ι,
        compArr j (cArr (Cc p.1 j) t v u) (meanArr (liftAArr Q Cc w p.2 (n - j) t u)) 0

/-- The cell source of the lift recursion for the test field `single w a`, scalar
fibres, is the applied array `srcArr`. -/
theorem liftCellSource_applyArr (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} {t : ℝ} {a : Vec 2 → ℝ}
    (hreg : LiftRegular Q Cc w t hh n (n + Dm + 2))
    (ha : ContDiff ℝ ((n + Dm + 1 : ℕ) : WithTop ℕ∞) a) (X z : Vec 2) (v : ι) :
    liftCellSource Q Cc (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) hh n t X z v =
      applyArr (n + 1) (srcArr Q Cc w hh n t v) a X z := by
  have hcomp : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q Cc (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) p.2 (n - j))
        t X z v =
      applyArr (n + 1) (∑ u : ι, compArr j (cArr (Cc p.1 j) t v u)
        (meanArr (liftAArr Q Cc w p.2 (n - j) t u)) 0) a X z := by
    intro j hj p hp
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hreg' : LiftRegular Q Cc w t p.2 (n - j) (n - j + Dm + 2) :=
      hreg.mono (by omega) (by omega) (by omega)
    have hreg'' : LiftRegular Q Cc w t p.2 (n - j) (j + Dm + 2) :=
      hreg.mono (by omega) (by omega) (by omega)
    have hL : liftMean Q Cc (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) p.2 (n - j) t =
        fun X u => applyArr (n - j + 1) (meanArr (liftAArr Q Cc w p.2 (n - j) t u)) a X 0 := by
      funext Y u
      exact liftMean_apply Q Cc w hreg'
        (ha.of_le (by exact_mod_cast (by omega : n - j + Dm + 1 ≤ n + Dm + 1))) Y 0 u
    rw [liftApply_arrField j (n - j + 1) (Cc p.1 j) t
      (fun u => meanArr (liftAArr Q Cc w p.2 (n - j) t u)) 0
      (liftMean Q Cc (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) p.2 (n - j)) hL
      (ha.of_le (by exact_mod_cast (by omega : n - j + 1 + j ≤ n + Dm + 1)))
      (fun u => arrSlowSmooth_meanArr (arrSmooth_liftAArr Q Cc w hreg'' u))
      (fun u => arrSupp_meanArr (arrSupp_liftAArr Q Cc w p.2 (n - j) t u)) X z v,
      applyArr_sum]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [show j + (n - j + 1) = n + 1 by omega]
  unfold liftCellSource srcArr
  simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Finset.sum_apply]
  rw [liftA_apply Q Cc w hreg ha X z v, liftMean_apply Q Cc w hreg ha X z v,
    applyArr_add, applyArr_neg, applyArr_sub]
  simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, applyArr_sum, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun p hp => ?_
  rw [hcomp j hj p hp, applyArr_sum]
  simp only [Finset.sum_apply]
end

/-! **`liftFluxX` of the test field `single w a` is an applied array.** -/

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

/-- `liftApply` of the test field is the vector field of applied entry arrays. -/
theorem liftApply_single_fun (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {a : Vec 2 → ℝ} (hh k : ℕ) (t : ℝ)
    (ha : ContDiff ℝ (k : WithTop ℕ∞) a) :
    liftApply k (Cc hh k) (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) t =
      fun X z v => applyArr k (entryArr (Cc hh k) k w t v) a X z := by
  funext X z v
  exact liftApply_single k _ w ha t X z v

/-- **The slow flux of the test field is the applied array `fluxXArr`.** Hypotheses: the lift
data are `C^{Dm+2}` at time `t` (grades `≤ hh`, orders `≤ n`), and `a` is `C^{n+Dm}`. -/
theorem liftFluxX_applyArr (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} {t : ℝ} {a : Vec 2 → ℝ}
    (hreg : LiftRegular Q Cc w t hh n (Dm + 2))
    (ha : ContDiff ℝ ((n + Dm : ℕ) : WithTop ℕ∞) a) (X z : Vec 2) (κ : Fin 2) (v : ι) :
    liftFluxX Q Cc (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) hh n t X z κ v =
      applyArr n (fluxXArr Q Cc w hh n t v κ) a X z := by
  have hent : ∀ hh' k, hh' ≤ hh → k ≤ n → ∀ u,
      ArrSmooth (Dm + 2) (entryArr (Cc hh' k) k w t u) := fun hh' k h1 h2 u =>
    arrSmooth_entryArr _ _ _ _ _ (hreg.coeff hh' h1 k h2 · · u)
  have hΦ : ∀ hh' k, k ≤ n →
      liftApply k (Cc hh' k) (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) t =
      fun X z v => applyArr k (entryArr (Cc hh' k) k w t v) a X z := fun hh' k hk =>
    liftApply_single_fun Cc w hh' k t (ha.of_le (by exact_mod_cast (by omega : k ≤ n + Dm)))
  have hB1 : ∀ u, ArrSmooth 1 (entryArr (Cc hh (n - 1)) (n - 1) w t u) := fun u =>
    ((hent hh (n - 1) le_rfl (by omega) u).mono (by omega))
  -- the four terms
  have eA : (Real.sqrt Q.η * Q.v t z κ) * liftApply (n - 1) (Cc hh (n - 1))
      (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) t X z v =
      applyArr n (fluxXA Q Cc w hh n t v κ) a X z := by
    rw [hΦ hh (n - 1) (by omega)]
    rw [applyArr_eq_of_supp (K := n - 1) (K' := n) (by omega) (arrSupp_fluxXA Q Cc w hh n t v κ) a]
    rw [fluxXA, applyArr_mulArr]
  have eB : (Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X κ j • fastPartial j
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) t) X z) v =
      applyArr n (fluxXB Q Cc w hh n t v κ) a X z := by
    rw [hΦ hh (n - 1) (by omega)]
    simp only [fastPartial_vec _ (n - 1) hB1, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [applyArr_eq_of_supp (K := n - 1) (K' := n) (by omega) (arrSupp_fluxXB Q Cc w hh n t v κ) a]
    simp only [fluxXB, applyArr_smul, applyArr_sum, applyArr_mulArr, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  have eC : (if 2 ≤ n then -(Q.η • ∑ j : Fin 2, Q.G t X κ j • slowPartial j
      (liftApply (n - 2) (Cc hh (n - 2)) (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) t) X z)
      else (0 : ι → ℝ)) v = applyArr n (fluxXC Q Cc w hh n t v κ) a X z := by
    by_cases h2 : 2 ≤ n
    · simp only [h2, ite_true, fluxXC]
      rw [hΦ hh (n - 2) (by omega)]
      have hsl := fun j => slowPartial_vec j (n - 2)
        (ha.of_le (by exact_mod_cast (by omega : n - 2 + 1 ≤ n + Dm)))
        (B := fun u => entryArr (Cc hh (n - 2)) (n - 2) w t u)
        (fun u => ((hent hh (n - 2) le_rfl (by omega) u).mono (by omega)).slow)
        (fun u => arrSupp_entryArr _ _ _ _ _)
      simp only [hsl, Pi.neg_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      have hs : ArrSupp (n - 1) (-(Q.η • ∑ j : Fin 2, mulArr (fun X _ => Q.G t X κ j)
          (slowArr j (entryArr (Cc hh (n - 2)) (n - 2) w t v)))) := by
        have := arrSupp_fluxXC Q Cc w hh n t v κ
        simpa [fluxXC, h2] using this
      rw [applyArr_eq_of_supp (K := n - 1) (K' := n) (by omega) hs a]
      simp only [applyArr_neg, applyArr_smul, applyArr_sum, applyArr_mulArr, Pi.neg_apply,
        Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
      rw [show n - 2 + 1 = n - 1 by omega]
    · simp [h2, fluxXC, applyArr_zero]
  have eD : (if hh = 0 then (0 : ι → ℝ) else ∑ j ∈ Finset.Icc 1 (min Dm n),
      (Real.sqrt Q.η * ((j - 1).factorial : ℝ)⁻¹) •
        iteratedDeriv (j - 1) (fun ε : ℝ => sourceFlux Q.edge Q.η ε t
          (liftApply (n - j) (Cc (hh - 1) (n - j))
            (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) t) κ X z) 0) v =
      applyArr n (fluxXD Q Cc w hh n t v κ) a X z := by
    by_cases h0 : hh = 0
    · simp [h0, fluxXD, applyArr_zero]
    · simp only [h0, ite_false, fluxXD]
      rw [applyArr_sum]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_Icc.mp hj
      have hjD : j ≤ Dm := by omega
      have hjn : j ≤ n := by omega
      have hfun : (fun ε : ℝ => sourceFlux Q.edge Q.η ε t
          (liftApply (n - j) (Cc (hh - 1) (n - j))
            (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) t) κ X z) =
          fun ε => ∑ p ∈ Finset.range Dm, ε ^ p • (fun u => applyArr (n - j + Dm)
            (fluxG Q.edge (Real.sqrt Q.η) t κ
              (fun u => entryArr (Cc (hh - 1) (n - j)) (n - j) w t u) u p) a X z) := by
        funext ε u
        rw [hΦ (hh - 1) (n - j) (by omega),
          sourceFlux_apply Q.edge Q.η ε t κ (K := n - j)
            (A := fun u => entryArr (Cc (hh - 1) (n - j)) (n - j) w t u)
            (ha.of_le (by exact_mod_cast (by omega : n - j + Dm ≤ n + Dm)))
            (fun u => (hent (hh - 1) (n - j) (by omega) (by omega) u).mono (by omega))
            (fun u => arrSupp_entryArr _ _ _ _ _) X z u, evalApplyHom_apply, applyArr_evalG]
        simp
      rw [hfun, iteratedDeriv_poly _ _ (by omega : j - 1 < Dm)]
      have hsupp := (fluxG_gSupp Q.edge (Real.sqrt Q.η) t κ
        (A := fun u => entryArr (Cc (hh - 1) (n - j)) (n - j) w t u)
        (fun u => arrSupp_entryArr _ _ _ _ _) v).1 (j - 1)
      rw [show n - j + (j - 1) = n - 1 by omega] at hsupp
      rw [applyArr_smul]
      have h1 := congrFun (congrFun (applyArr_eq_of_supp (K := n - 1) (K' := n - j + Dm)
        (by omega) hsupp a) X) z
      have h2 := congrFun (congrFun (applyArr_eq_of_supp (K := n - 1) (K' := n)
        (by omega) hsupp a) X) z
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [h1, h2]
      have hf : ((j - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
  unfold liftFluxX fluxXArr
  simp only [applyArr_sub, applyArr_add, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← eA, ← eC, ← eD]
  rw [← eB]
  simp only [Pi.smul_apply, smul_eq_mul]
end

/-! **`fluxCoeff` of the path mean flux and of the direct flux.**

* `liftFluxX_monoScaled`: `liftFluxX` of the scaled monomial test field at its centre.
* `fluxCoeff_pathMeanFlux`: the coefficient array of `pathMeanFlux`.
* `fluxCoeff_directFlux`: the coefficient array of `directFlux`. -/

section
/-! ### Scaled monomials -/

theorem orderedDerivative_const_mul (c : ℝ) : ∀ {m : ℕ} (α : DerivativeWord2 m) {g : Vec 2 → ℝ},
    ContDiff ℝ ⊤ g →
      orderedDerivative α (fun x => c * g x) = fun x => c * orderedDerivative α g x := by
  intro m
  induction m with
  | zero =>
    intro α g _
    have : α = Fin.elim0 := Subsingleton.elim _ _
    subst this
    simp [orderedDerivative_zero_word]
  | succ m ih =>
    intro α g hg
    have h1 : (fun x => fderiv ℝ (fun x => c * g x) x (basisVec (α 0))) =
        fun x => c * fderiv ℝ g x (basisVec (α 0)) := by
      funext x
      rw [fderiv_const_mul (hg.differentiable (by simp) x)]
      simp
    rw [orderedDerivative_succ, h1, ih (fun i => α i.succ) (contDiff_dirDeriv hg _)]
    funext x
    rw [orderedDerivative_succ]

/-- At the centre, an applied array on a scaled monomial is the scaled sum over permutations,
for an array supported in orders `≤ K` (every word length `m`). -/
theorem applyArr_mono_scaled (K : ℕ) {A : CArr} (hA : ArrSupp K A) (c : ℝ) (y z : Vec 2) {m : ℕ}
    (I : DerivativeWord2 m) :
    applyArr K A (fun Y => c * mono y I Y) y z = c * ∑ σ : Equiv.Perm (Fin m), A m (I ∘ σ) y z := by
  by_cases hm : m ≤ K
  · have hd : ∀ {r} (α : DerivativeWord2 r),
        orderedDerivative α (fun Y => c * mono y I Y) y = c * orderedDerivative α (mono y I) y :=
      fun α => congrFun (orderedDerivative_const_mul c α (contDiff_mono y I)) y
    unfold applyArr
    simp only [hd]
    have h := applyArr_mono K A y z I hm
    unfold applyArr at h
    simp only [fun r (α : DerivativeWord2 r) (x : ℝ) => show A r α y z * (c * x) = c * (A r α y z * x)
      from by ring, ← Finset.mul_sum]
    rw [h]
  · have hz : ∀ σ : Equiv.Perm (Fin m), A m (I ∘ σ) = 0 := fun σ => hA m (by omega) _
    simp only [hz, Pi.zero_apply, Finset.sum_const_zero, mul_zero]
    unfold applyArr
    refine Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun α _ => ?_
    have hrK : r ≠ m := by
      have := Finset.mem_range.mp hr
      omega
    have hd := congrFun (orderedDerivative_const_mul c α (contDiff_mono y I)) y
    rw [hd, orderedDerivative_mono_of_ne y I α hrK, mul_zero, mul_zero]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

/-- **`liftFluxX` of the scaled monomial test field at its centre.** -/
theorem liftFluxX_monoScaled (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} {t : ℝ}
    (hreg : LiftRegular Q Cc w t hh n (Dm + 2)) (c : ℝ) (y z : Vec 2) (κ : Fin 2) (v : ι)
    {m : ℕ} (I : DerivativeWord2 m) :
    liftFluxX Q Cc (fun _ Y => (Pi.single w (c * mono y I Y) : ι → ℝ)) hh n t y z κ v =
      c * ∑ σ : Equiv.Perm (Fin m), fluxXArr Q Cc w hh n t v κ m (I ∘ σ) y z := by
  rw [liftFluxX_applyArr Q Cc w hreg
    (((contDiff_const.mul (contDiff_mono y I))).of_le (by exact_mod_cast le_top)) y z κ v]
  exact applyArr_mono_scaled n ((arrSupp_fluxXArr Q Cc w hh n t v κ).mono (by omega)) c y z I
end

/-! **`fluxCoeff` of `pathMeanFlux` and of `directFlux`.** -/

theorem mono_zero_smul (ρ : ℝ) {r : ℕ} (I : DerivativeWord2 r) (X : Vec 2) :
    mono 0 I (ρ • X) = ρ ^ r * mono 0 I X := by
  unfold mono
  simp only [sub_zero, Pi.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  simp

/-- **`fluxCoeff` of the path mean flux.** `Q` is the lift data of the scalar path family
(components `Fin (h+1)`), `s = (ℓ²)⁻¹ t`. Hypothesis: the lift data are `C^{Dm+2}` at time `s`
(grades `≤ h`, orders `≤ n`). The identity holds for every `d` (for `n < d - 1` both sides
vanish). -/
theorem fluxCoeff_pathMeanFlux (D : OCData) (m : ℕ) {ρ : ℝ} {h Dm : ℕ}
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ)
    (hreg : LiftRegular Q Cc (0 : Fin (h + 1)) ((D.cellScaleSq m)⁻¹ * t) h n (Dm + 2))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (κ : Fin 2) :
    fluxCoeff (pathMeanFlux D m ρ Q Cc n t) d I 0 κ =
      -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) *
        ρ ^ (d - 1) * ((d - 1).factorial : ℝ)⁻¹ *
        fieldCellMean (fun z => ∑ σ : Equiv.Perm (Fin (d - 1)),
          fluxXArr Q Cc 0 h n ((D.cellScaleSq m)⁻¹ * t) (Fin.last h) κ (d - 1) (I ∘ σ) 0 z) := by
  set s := (D.cellScaleSq m)⁻¹ * t with hs
  set c₀ := -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ)
    with hc₀
  have hfield : (fun (_ : ℝ) (X : Vec 2) =>
      (Pi.single (0 : Fin (h + 1)) (mono 0 I (ρ • X)) : Fin (h + 1) → ℝ)) =
      fun _ Y => (Pi.single (0 : Fin (h + 1)) (ρ ^ (d - 1) * mono 0 I Y) : Fin (h + 1) → ℝ) := by
    funext _ Y
    rw [mono_zero_smul]
  have hψ : ∀ z u, liftFluxX Q Cc
      (fun _ (X : Vec 2) => (Pi.single (0 : Fin (h + 1)) (mono 0 I (ρ • X)) : Fin (h + 1) → ℝ))
      h n s (ρ⁻¹ • (0 : Vec 2)) z κ u =
      ρ ^ (d - 1) * ∑ σ : Equiv.Perm (Fin (d - 1)),
        fluxXArr Q Cc 0 h n s u κ (d - 1) (I ∘ σ) 0 z := by
    intro z u
    rw [hfield, smul_zero]
    exact liftFluxX_monoScaled Q Cc 0 hreg _ 0 z κ u I
  have hcont : Continuous (fun z => liftFluxX Q Cc
      (fun _ (X : Vec 2) => (Pi.single (0 : Fin (h + 1)) (mono 0 I (ρ • X)) : Fin (h + 1) → ℝ))
      h n s (ρ⁻¹ • (0 : Vec 2)) z κ) := by
    refine continuous_pi fun u => ?_
    have hA0 : ArrSmooth 0 (fluxXArr Q Cc 0 h n s u κ) :=
      arrSmooth_fluxXArr Q Cc 0 (r := 0) (hreg.mono le_rfl le_rfl (by omega)) u κ
    have : (fun z => liftFluxX Q Cc
        (fun _ (X : Vec 2) => (Pi.single (0 : Fin (h + 1)) (mono 0 I (ρ • X)) : Fin (h + 1) → ℝ))
        h n s (ρ⁻¹ • (0 : Vec 2)) z κ u) =
        fun z => applyArr n (fluxXArr Q Cc 0 h n s u κ) (fun Y => ρ ^ (d - 1) * mono 0 I Y) 0 z := by
      funext z
      rw [hfield, smul_zero]
      exact liftFluxX_applyArr Q Cc 0 hreg
        (((contDiff_const.mul (contDiff_mono 0 I))).of_le (by exact_mod_cast le_top)) 0 z κ u
    rw [this]
    exact continuous_applyArr_z hA0 _ 0
  have hint := integrableOn_unitCube_of_continuous hcont
  have hcomm := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (h + 1) => ℝ)
    (Fin.last h)).integral_comp_comm hint
  simp only [ContinuousLinearMap.proj_apply] at hcomm
  have hmean : fieldCellMean (fun z => liftFluxX Q Cc
      (fun _ (X : Vec 2) => (Pi.single (0 : Fin (h + 1)) (mono 0 I (ρ • X)) : Fin (h + 1) → ℝ))
      h n s (ρ⁻¹ • (0 : Vec 2)) z κ) (Fin.last h) =
      ρ ^ (d - 1) * fieldCellMean (fun z => ∑ σ : Equiv.Perm (Fin (d - 1)),
        fluxXArr Q Cc 0 h n s (Fin.last h) κ (d - 1) (I ∘ σ) 0 z) := by
    unfold fieldCellMean
    rw [← hcomm]
    simp only [hψ]
    rw [integral_const_mul]
  unfold fluxCoeff pathMeanFlux
  simp only [Pi.smul_apply, smul_eq_mul]
  change ((d - 1).factorial : ℝ)⁻¹ * (c₀ * fieldCellMean (fun z => liftFluxX Q Cc
      (fun _ (X : Vec 2) => (Pi.single (0 : Fin (h + 1)) (mono 0 I (ρ • X)) : Fin (h + 1) → ℝ))
      h n s (ρ⁻¹ • (0 : Vec 2)) z κ) (Fin.last h)) = _
  rw [hmean]
  ring

/-- **`fluxCoeff` of the direct flux.** Hypotheses: `1 ≤ d` and all stage orders are `≥ 1`
(otherwise the order `0` and the order `1` have the same word length). -/
theorem fluxCoeff_directFlux {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, NormedSpace ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (G : GenStage D hr Dm b j₀) (p : OddSlot) (c : StageCtx D b j₀ G.level p)
    {v u : CompIn G.comps} (γ : G.fam.Γ v u) (ords : Finset ℕ) (hords : ∀ d' ∈ ords, 1 ≤ d')
    (t : ℝ) {d : ℕ} (hd : 1 ≤ d) (I : DerivativeWord2 (d - 1)) :
    fluxCoeff (directFlux G p c γ ords t) d I 0 =
      if d ∈ ords then
        (D.kap G.level * D.eps G.level ^ (d - 2) * ((d - 1).factorial : ℝ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin (d - 1)),
            fieldCellMean (fun z => G.fam.flux p c v u γ d (I ∘ σ) t 0 z)
      else 0 := by
  unfold fluxCoeff directFlux
  have hmono : (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) = mono 0 I := rfl
  rw [hmono]
  have hF : ∀ d' (α : DerivativeWord2 (d' - 1)),
      fieldCellMean (fun z => G.fam.flux p c v u γ d' α t ((D.eps (G.level - 1))⁻¹ • (0 : Vec 2)) z)
      = fieldCellMean (fun z => G.fam.flux p c v u γ d' α t 0 z) := fun d' α => by
    rw [smul_zero]
  simp only [hF]
  by_cases hdo : d ∈ ords
  · rw [Finset.sum_eq_single d]
    simp only [hdo, ↓reduceIte]
    · have key := smul_sum_orderedDerivative_mono 0 I
        (fun α => fieldCellMean (fun z => G.fam.flux p c v u γ d α t 0 z))
      simp only [mul_smul, ← Finset.smul_sum]
      rw [smul_comm (((d - 1).factorial : ℝ)⁻¹) (D.kap G.level),
        smul_comm (((d - 1).factorial : ℝ)⁻¹) (D.eps G.level ^ (d - 2)), key]
    · intro d' hd' hne
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [orderedDerivative_mono_of_ne 0 I α (by have := hords d' hd'; omega), mul_zero, zero_smul]
    · intro h; exact absurd hdo h
  · simp only [hdo, ↓reduceIte]
    rw [Finset.sum_eq_zero, smul_zero]
    intro d' hd'
    refine Finset.sum_eq_zero fun α _ => ?_
    have hne : d' ≠ d := fun h => hdo (h ▸ hd')
    rw [orderedDerivative_mono_of_ne 0 I α (by have := hords d' hd'; omega), mul_zero, zero_smul]

/-! The cell source of the monomial test field at its centre: the form consumed by the cell
problem of the lift coefficients. -/

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

/-- At its centre `y`, the cell source of the monomial field `mono y I` (in the component `u`) is
the sum over the permutations of the array `srcArr` at the permuted words. -/
theorem liftCellSource_monoField (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (u : ι) {hh n : ℕ} {t : ℝ}
    (hreg : LiftRegular Q Cc u t hh n (n + Dm + 2)) (y z : Vec 2) (v : ι) {m : ℕ}
    (I : DerivativeWord2 m) (hm : m ≤ n + 1) :
    liftCellSource Q Cc (fun _ => monoField u y I) hh n t y z v =
      ∑ σ : Equiv.Perm (Fin m), srcArr Q Cc u hh n t v m (I ∘ σ) y z := by
  have h := liftCellSource_applyArr Q Cc u hreg
    ((contDiff_mono y I).of_le (by exact_mod_cast le_top)) y z v
  rw [show (fun _ : ℝ => monoField u y I) = fun _ Y => (Pi.single u (mono y I Y) : ι → ℝ) from rfl,
    h]
  exact applyArr_mono (n + 1) _ y z I hm
end

end AVRegularity.Providers.GenSem
end
