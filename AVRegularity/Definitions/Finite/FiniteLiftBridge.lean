-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.IsAdmissibleQ
import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.Definitions.Iteration.CascadeStatement
import AVRegularity.Statements.Intermediate.Readout.ReadoutLemma
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public section
open MeasureTheory Homogenization
namespace AVRegularity

/-! Plumbing: the elementary choices of the proof of the finite-level statement
`OcFiniteStatement` that need no estimate.

* The construction exponents are positive: `δ, γ, c, μ_s, η₀ = min{δ/8, μ_s/4}`, and `ε_m ≤ 1`.
* `exists_ocBandChain`, `exists_ocData`: every `κ ∈ 𝒦_M` is the terminal diffusivity of a band
  chain, and a stream sequence with such a chain and terminal level `M` is an `OCData`.
* `exists_mollifier`: an admissible kernel template `φ₀` exists.
* `exists_invariantAdmissible`, `exists_ledgerAdmissible`, `exists_freshKernelOrder`: the cascade
  invariant constants, the ledger constants and the fresh terminal kernel order can be chosen.
* `exists_ocTauPP_le`, `exists_entry_wait`: `τ''_m → 0`, hence the entry wait: for every constant
  `C` the terminal preparation `t_p + h_M ≤ a_M + (C+1)h_M ≤ a + 6J_wτ''_{M+1} + (C+1)τ''_M` is
  below any `t₀ > 0` for large `M` (`IsWeakStage`, `IsTerminalPrepMap`). -/

theorem ocDelta_pos_of_admissible {α s q : ℝ} (hα₀ : 0 < α) (hq : IsAdmissibleQ α s q) :
    0 < ocDelta α q := by
  obtain ⟨hq1, -, hq3, -⟩ := hq
  unfold ocDelta
  have h1 : (2 - (1 + α)) / (2 * ((1 + α) - 1)) = (1 - α) / (2 * α) := by ring_nf
  rw [h1, lt_div_iff₀ (by positivity)] at hq3
  have h2 : (2 * q + 1) * (1 + α) / (2 * q + 2) < 1 := by
    rw [div_lt_one (by linarith)]; nlinarith
  have h3 : 0 < (q - 1) / 4 := by linarith
  exact mul_pos h3 (by linarith)

theorem ocGamma_pos_of_admissible {α s q : ℝ} (hα₀ : 0 < α) (hq : IsAdmissibleQ α s q) :
    0 < ocGamma α q := by
  unfold ocGamma
  have := hq.1
  apply div_pos (mul_pos (by linarith) (by linarith)) (by linarith)

theorem ocC_pos_of_admissible {α s q : ℝ} (hα₀ : 0 < α) (hq : IsAdmissibleQ α s q) :
    0 < ocC α q := by
  unfold ocC
  have := ocGamma_pos_of_admissible hα₀ hq
  have := ocDelta_pos_of_admissible hα₀ hq
  positivity

theorem ocMuS_pos_of_admissible {α s q : ℝ} (hα₀ : 0 < α) (hs₀ : 0 < s)
    (hq : IsAdmissibleQ α s q) : 0 < ocMuS α q s := by
  obtain ⟨hq1, -, -, hq4⟩ := hq
  have h4 : (1 + α) - 1 + s = α + s := by ring
  rw [h4, lt_div_iff₀ (by linarith)] at hq4
  unfold ocMuS ocGamma
  have hq0 : 0 < q + 1 := by linarith
  have key : q * ((q - 1) * (1 + α) / (q + 1)) = (q - 1) * (q * (1 + α) / (q + 1)) := by ring
  rw [key, ← mul_sub]
  refine mul_pos (by linarith) ?_
  rw [sub_pos, div_lt_iff₀ hq0]
  nlinarith

theorem succEta0_pos_of_admissible {α s q : ℝ} (hα₀ : 0 < α) (hs₀ : 0 < s)
    (hq : IsAdmissibleQ α s q) : 0 < succEta0 α q s := by
  unfold succEta0
  have := ocDelta_pos_of_admissible hα₀ hq
  have := ocMuS_pos_of_admissible hα₀ hs₀ hq
  exact lt_min (by positivity) (by positivity)

theorem ocEpsilon_le_one {q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) : ocEpsilon q Λ m ≤ 1 := by
  unfold ocEpsilon
  split_ifs
  · exact le_rfl
  · have hp : 0 < (Λ : ℝ) ^ (q ^ m / (q - 1)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < Λ by omega)) _
    have hc : (1 : ℝ) ≤ (⌈(Λ : ℝ) ^ (q ^ m / (q - 1))⌉₊ : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hp).ne'
    exact inv_le_one_of_one_le₀ hc

theorem ocEpsilon_nonneg {q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) : 0 ≤ ocEpsilon q Λ m :=
  (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ).le

/-- Every `κ ∈ 𝒦_M` is the terminal diffusivity of a band chain. -/
theorem exists_ocBandChain (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (M : ℕ) (κM : ℝ)
    (hκ : κM ∈ ocBand α q Λ M) :
    ∃ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ ∧ κ M = κM := by
  let g : ℕ → ℝ := fun j => Nat.rec κM (fun i x => ocMeanFlux α q Λ ζ (M - i) x) j
  refine ⟨fun k => g (M - k), ⟨?_, fun m hm1 hmM => ?_⟩, ?_⟩
  · simpa [g] using hκ
  · have h1 : M - (m - 1) = (M - m) + 1 := by omega
    have h2 : M - (M - m) = m := by omega
    show g (M - (m - 1)) = ocMeanFlux α q Λ ζ m (g (M - m))
    rw [h1]
    show ocMeanFlux α q Λ ζ (M - (M - m)) (g (M - m)) = _
    rw [h2]
  · simp [g]

/-- A stream sequence with a band chain through `κ ∈ 𝒦_M` and terminal level `M` is an `OCData`. -/
theorem exists_ocData (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (M : ℕ) (κ : ℝ) (hκ : κ ∈ ocBand α q Λ M) :
    ∃ D : OCData, D.α = α ∧ D.q = q ∧ D.Λ = Λ ∧ D.ζ = ζ ∧ D.Φ = Φ ∧
      IsOCBandChain α q Λ ζ M D.κ ∧ D.κ M = κ ∧ D.term = M := by
  obtain ⟨κc, hc, hcM⟩ := exists_ocBandChain α q Λ ζ M κ hκ
  have hadm : ∀ m, AVenhance.IsAdmissibleStream (Φ m) := by
    intro m
    obtain ⟨h, -⟩ := hΦ.2 (m + 1) (by omega)
    simpa using h
  exact ⟨⟨α, q, Λ, ζ, Φ, hadm, κc, M⟩, rfl, rfl, rfl, rfl, rfl, hc, hcM, rfl⟩

/-- An admissible kernel template exists (a normalized bump of radius `1/2`). -/
theorem exists_mollifier :
    ∃ (φ₀ : Vec 2 → ℝ) (_ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ ∧ (∀ z, 0 ≤ φ₀ z) ∧
      ∫ z, φ₀ z = 1 ∧ Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall := by
  let b : ContDiffBump (0 : Vec 2) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, b.integrable_normed, b.contDiff_normed, fun z => b.nonneg_normed z,
    b.integral_normed, ?_⟩
  intro z hz
  rw [b.support_normed_eq] at hz
  have hz' : ‖z‖ < 1 / 2 := by simpa [b] using hz
  have h := HilbertVec.norm_ofVec_le_mul_norm z
  show Analysis.Convolution.euclideanNorm z ≤ 1
  unfold Analysis.Convolution.euclideanNorm
  simp only [Nat.cast_ofNat] at h
  linarith

/-- The cascade invariant constants can be chosen (`IsInvariantAdmissible`). -/
theorem exists_invariantAdmissible (kS thr : InvConsts) (r₀ D₀ H J N p nk Kres Lpr Lc Lf : ℕ)
    (σ₀ δ q c : ℝ) (hσ₀ : 0 < σ₀) (hσl : σ₀ < kS.lamC) (hq : 1 < q) (hc : 0 < c)
    (halloc : IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf)
    (hnk : max Lpr (max Lc Lf) + 1 ≤ 2 * nk) :
    ∃ kI : InvConsts, IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ δ q c := by
  obtain ⟨hL, hKs, hKan, hLan, hJm, hLs, -, -, hHp, hm0, hm1⟩ := halloc
  have hlam : σ₀ < (q - 1) * (1 + c) + q * σ₀ := by nlinarith
  refine ⟨InvConsts.mk kS.c₀ kS.cr (max kS.Γk thr.Γk) (max kS.Cwid thr.Cwid)
    (min kS.σf (δ + σ₀)) (min kS.lamC ((q - 1) * (1 + c) + q * σ₀)) (max kS.Ca thr.Ca) kS.mEnv
    (fun j => max (kS.Cm j) (thr.Cm j)) (fun j => max (kS.cker j) (thr.cker j)) Kres Kres Kres
    Kres (max Lpr (max Lc Lf)) (succLstar Kres kS.G0 H J N p) kS.G0 kS.Hprod, ?_⟩
  refine ⟨rfl, rfl, le_max_left _ _, le_max_right _ _, le_max_left _ _, le_max_right _ _, rfl,
    lt_min hσl hlam, min_le_left _ _, min_le_right _ _, le_max_left _ _, le_max_right _ _,
    fun j => ⟨le_max_left _ _, le_max_right _ _⟩, fun j => ⟨le_max_left _ _, le_max_right _ _⟩,
    le_rfl, hL, hnk, le_rfl, hKs, le_rfl, hKan, le_rfl, hLan, le_rfl, hJm, le_rfl, hLs, rfl, rfl,
    hHp, hm0, le_rfl, hm1⟩

theorem exists_ledgerAdmissible (Ce CIthr Cwthr : ℝ) :
    ∃ CI Cw : ℝ, IsLedgerAdmissible Ce CI Cw CIthr Cwthr :=
  ⟨max Ce CIthr, max Cwthr 1, le_max_left _ _, le_max_right _ _, le_max_left _ _,
    lt_of_lt_of_le one_pos (le_max_right _ _)⟩

theorem exists_freshKernelOrder (LcT Lpr Lc Lf : ℕ) :
    ∃ nT : ℕ+, IsFreshKernelOrder nT LcT Lpr Lc Lf :=
  ⟨⟨max LcT (max Lpr (max Lc Lf)) + 1, by omega⟩, by
    refine ⟨?_, ?_⟩ <;> simp only [PNat.mk_coe] <;> omega⟩

/-- `ε_k⁻¹ ≥ k` for `k ≥ 1` (`Λ ≥ 2`, `q > 1`). -/
theorem le_ocEpsilon_inv {q : ℝ} {Λ k : ℕ} (hΛ : 2 ≤ Λ) (hq : 1 < q) (hk : 1 ≤ k) :
    (k : ℝ) ≤ (ocEpsilon q Λ k)⁻¹ := by
  rw [AVRegularity.Construction.Stream.ocEpsilon_inv_eq_nat hk]
  have hΛ1 : (1 : ℝ) ≤ Λ := by exact_mod_cast (show 1 ≤ Λ by omega)
  have hpow : (1 : ℝ) + k * (q - 1) ≤ q ^ k := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ q - 1 by linarith) k
    rwa [add_sub_cancel] at h
  have hexp : (k : ℝ) ≤ q ^ k / (q - 1) := by
    rw [le_div_iff₀ (sub_pos.mpr hq)]; nlinarith
  calc (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self).le
    _ ≤ (Λ : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hΛ) k
    _ = (Λ : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ k).symm
    _ ≤ (Λ : ℝ) ^ (q ^ k / (q - 1)) := Real.rpow_le_rpow_of_exponent_le hΛ1 hexp
    _ ≤ _ := Nat.le_ceil _

/-- `τ''_m ≤ (m-1)^{-e}`, `e = 2 - β + 2δ` (`m ≥ 2`). -/
theorem ocTauPP_le_rpow {α q : ℝ} {Λ m : ℕ} (hΛ : 2 ≤ Λ) (hq : 1 < q)
    (he : 0 < 2 - (1 + α) + 2 * ocDelta α q) (hm : 2 ≤ m) :
    ocTauPP α q Λ m ≤ ((m - 1 : ℕ) : ℝ) ^ (-(2 - (1 + α) + 2 * ocDelta α q)) := by
  set e := 2 - (1 + α) + 2 * ocDelta α q
  have hΛ1 : 1 ≤ Λ := by omega
  have hk : 1 ≤ m - 1 := by omega
  have hεpos : 0 < ocEpsilon q Λ (m - 1) := AVRegularity.Construction.Stream.ocEpsilon_pos hΛ1
  have hkpos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have hX : ((m - 1 : ℕ) : ℝ) ^ e ≤ ocEpsilon q Λ (m - 1) ^ (-e) := by
    rw [Real.rpow_neg hεpos.le, ← Real.inv_rpow hεpos.le]
    exact Real.rpow_le_rpow hkpos.le (le_ocEpsilon_inv hΛ hq hk) he.le
  have hXpos : 0 < ((m - 1 : ℕ) : ℝ) ^ e := Real.rpow_pos_of_pos hkpos e
  have hceil : ocEpsilon q Λ (m - 1) ^ (-e) ≤ (⌈ocEpsilon q Λ (m - 1) ^ (-e)⌉₊ : ℝ) :=
    Nat.le_ceil _
  unfold ocTauPP
  rw [Real.rpow_neg hkpos.le]
  have h25 : (2 : ℝ) ^ (-25 : ℤ) ≤ 1 := by norm_num
  calc (2 : ℝ) ^ (-25 : ℤ) / (⌈ocEpsilon q Λ (m - 1) ^ (-e)⌉₊ : ℝ)
      ≤ 1 / ((m - 1 : ℕ) : ℝ) ^ e :=
        div_le_div₀ zero_le_one h25 hXpos (le_trans hX hceil)
    _ = (((m - 1 : ℕ) : ℝ) ^ e)⁻¹ := one_div _

/-- `τ''_m → 0`. -/
theorem exists_ocTauPP_le {α s q : ℝ} {Λ : ℕ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hq : IsAdmissibleQ α s q) (hΛ : 2 ≤ Λ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → ocTauPP α q Λ m ≤ ε := by
  have hδ := ocDelta_pos_of_admissible hα₀ hq
  set e := 2 - (1 + α) + 2 * ocDelta α q with he_def
  have he : 0 < e := by rw [he_def]; linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (ε ^ (-e⁻¹))
  refine ⟨N + 2, fun m hm => le_trans (ocTauPP_le_rpow hΛ hq.1 he (by omega)) ?_⟩
  have hb : 0 < ε ^ (-e⁻¹) := Real.rpow_pos_of_pos hε _
  have hkN : ε ^ (-e⁻¹) ≤ ((m - 1 : ℕ) : ℝ) := by
    refine le_trans hN ?_
    exact_mod_cast (show N ≤ m - 1 by omega)
  calc ((m - 1 : ℕ) : ℝ) ^ (-e) ≤ (ε ^ (-e⁻¹)) ^ (-e) :=
        Real.rpow_le_rpow_of_nonpos hb hkN (by linarith)
    _ = ε := by
        rw [← Real.rpow_mul hε.le]
        have : -e⁻¹ * -e = 1 := by field_simp
        rw [this, Real.rpow_one]

/-- **The entry wait**: for every constant `C` and `t₀ > 0`,
`(C + 1)τ''_M + 6J_wτ''_{M+1} ≤ t₀` for every large `M`. -/
theorem exists_entry_wait {α s q : ℝ} {Λ : ℕ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hq : IsAdmissibleQ α s q) (hΛ : 2 ≤ Λ) (C : ℝ) (Jw : ℕ) (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      (|C| + 1) * ocTauPP α q Λ M + 6 * Jw * ocTauPP α q Λ (M + 1) ≤ t₀ := by
  have hd : 0 < (|C| + 1) + 6 * Jw := by positivity
  obtain ⟨M₀, hM₀⟩ := exists_ocTauPP_le hα₀ hα₁ hq hΛ (t₀ / ((|C| + 1) + 6 * Jw))
    (div_pos ht₀ hd)
  refine ⟨M₀, fun M hM => ?_⟩
  have h1 := hM₀ M hM
  have h2 := hM₀ (M + 1) (by omega)
  have hC : 0 ≤ |C| + 1 := by positivity
  have hJ : (0 : ℝ) ≤ 6 * Jw := by positivity
  calc (|C| + 1) * ocTauPP α q Λ M + 6 * Jw * ocTauPP α q Λ (M + 1)
      ≤ (|C| + 1) * (t₀ / ((|C| + 1) + 6 * Jw)) + 6 * Jw * (t₀ / ((|C| + 1) + 6 * Jw)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hC) (mul_le_mul_of_nonneg_left h2 hJ)
    _ = t₀ := by field_simp

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! Definition: the two constant component maps used by the finite
assembly.

* `compReindex e`: the **mass-preserving reindexing** of normalized component vectors along a
  component equivalence `e : CompIn S ≃ CompIn S'`, `(compReindex e z)_{v'} = z_{e⁻¹v'}`. It is a
  linear isometry of the Euclidean spaces `CompSpace`; when the masses correspond
  (`π'(e v) = π v`) it carries `compField π a` to `compField π' (a ∘ e⁻¹)` ("the
  mass-preserving reindexing is an isometry on `CompSpace` and preserves the represented size").
* `compReadoutCLM π ω`: the **physical scalar readout** `𝓡_phys Z = ∑_v ω_v Z_v`, written
  in normalized coordinates `z_v = π_v^{-1/2} Z_v`, i.e. `z ↦ ∑_v ω_v π_v^{1/2} z_v`. At the root
  of the weak construction (one component `(0, ∅)`, mass `1/2`, readout `1`) it is the evaluation
  of the finest scalar field, `𝓡_root z = 2^{-1/2}z_{(0,∅)}` with `‖𝓡_root‖ = 2^{-1/2} ≤ 1` and
  `𝓡_root(compField π a) = a_{(0,∅)}`; it is applied once, after all vector lifts, and the
  constant maps `𝖱_T, 𝖱_i` act inside the lifts. -/

/-- The reindexing `z ↦ z ∘ e⁻¹` of normalized component vectors, a linear isometry. -/
def compReindex {S S' : Finset Comp} (e : CompIn S ≃ CompIn S') : CompSpace S →L[ℝ] CompSpace S' :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).toContinuousLinearEquiv.toContinuousLinearMap

/-- The physical scalar readout `z ↦ ∑_v ω_v π_v^{1/2} z_v` (normalized coordinates). -/
def compReadoutCLM {S : Finset Comp} (π ω : CompIn S → ℝ) : CompSpace S →L[ℝ] ℝ :=
  ∑ v : CompIn S, (ω v * Real.sqrt (π v)) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : CompIn S => ℝ) v

end AVRegularity
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVenhance
open scoped ENNReal Topology
namespace AVRegularity

/-! Plumbing: the adapters of the finite assembly.


* `compReindex`: an isometry (`compReindex_norm_le`) which carries `compField π a` to
  `compField π' (a ∘ e⁻¹)` when the masses correspond (`compReindex_compField`); with the
  readout lemma `iteration_readout` it preserves representations and does not increase the
  represented size (`compReindex_rep`), the typed adapter.
* `compReadoutCLM`: its norm is at most `∑_v |ω_v| π_v^{1/2}` (`compReadoutCLM_norm_le`; at the
  weak root `(1/2)^{1/2} ≤ 1`, uniform in the terminal level) and it reads `compField π a` as
  `∑_v ω_v a_v` (`compReadoutCLM_compField`). -/

theorem compReindex_apply {S S' : Finset Comp} (e : CompIn S ≃ CompIn S') (z : CompSpace S)
    (v' : CompIn S') : WithLp.ofLp (compReindex e z) v' = WithLp.ofLp z (e.symm v') := rfl

theorem compReindex_norm_le {S S' : Finset Comp} (e : CompIn S ≃ CompIn S') :
    ‖compReindex e‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [one_mul]
  exact le_of_eq ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).norm_map z)

theorem compReindex_compField {S S' : Finset Comp} (e : CompIn S ≃ CompIn S')
    (π : CompIn S → ℝ) (π' : CompIn S' → ℝ) (hπ : ∀ v, π' (e v) = π v)
    (a : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) (x : Vec 2) :
    compReindex e (compField π a x) = compField π' (fun y v' => a y (e.symm v')) x := by
  refine (WithLp.ofLp_injective 2).eq_iff.mp ?_
  funext v'
  rw [compReindex_apply]
  simp only [compField, toCompSpace]
  rw [← hπ (e.symm v'), e.apply_symm_apply]

/-- The typed adapter: a mass-preserving reindexing keeps a representation and does not
increase its represented size (readout lemma `iteration_readout`, `‖compReindex e‖ ≤ 1`). -/
theorem compReindex_rep (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) (K : ℕ) (hK : 1 ≤ K) (lam : ℝ)
    {S S' : Finset Comp} (e : CompIn S ≃ CompIn S') (r : Representation (CompSpace S))
    (hr : IsRepresentationAt lam K r) :
    IsRepresentationAt lam K (r.map (compReindex e)) ∧
      (r.map (compReindex e)).value = (fun x => compReindex e (r.value x)) ∧
      representedSize s K lam (r.map (compReindex e)) ≤ representedSize s K lam r := by
  obtain ⟨h1, h2, h3⟩ := (iteration_readout s hs₀ hs₁ K hK (H := CompSpace S)
    (H' := CompSpace S')).2.2 lam r (compReindex e) hr
  refine ⟨h1, h2, le_trans h3 ?_⟩
  calc ENNReal.ofReal ‖compReindex e‖ * representedSize s K lam r
      ≤ ENNReal.ofReal 1 * representedSize s K lam r :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (compReindex_norm_le e)) le_rfl
    _ = representedSize s K lam r := by rw [ENNReal.ofReal_one, one_mul]

theorem compReadoutCLM_apply {S : Finset Comp} (π ω : CompIn S → ℝ) (z : CompSpace S) :
    compReadoutCLM π ω z = ∑ v, ω v * Real.sqrt (π v) * WithLp.ofLp z v := by
  simp [compReadoutCLM]

theorem compReadoutCLM_norm_le {S : Finset Comp} (π ω : CompIn S → ℝ) :
    ‖compReadoutCLM π ω‖ ≤ ∑ v, |ω v| * Real.sqrt (π v) := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun v _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) fun z => ?_
  rw [compReadoutCLM_apply, Real.norm_eq_abs, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun v _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
  have := PiLp.norm_apply_le z v
  rwa [Real.norm_eq_abs] at this

theorem compReadoutCLM_compField {S : Finset Comp} (π ω : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (a : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) (x : Vec 2) :
    compReadoutCLM π ω (compField π a x) = ∑ v, ω v * a x v := by
  rw [compReadoutCLM_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [compField, toCompSpace]
  have h := (Real.sqrt_pos.mpr (hπ v)).ne'
  field_simp

theorem latticeShift_add (n m : Fin 2 → ℤ) :
    latticeShift (n + m) = latticeShift n + latticeShift m := by
  funext i
  simp [latticeShift]

end AVRegularity
end
end
