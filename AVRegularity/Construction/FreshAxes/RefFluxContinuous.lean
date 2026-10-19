-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.ChartDerivativeBounded
import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleReference.OcRefFlux

/-! Continuity of the reference flux in time: the odd pulses have disjoint short supports, so the
pulse sum is locally finite. -/

@[expose] public noncomputable section

open Homogenization Filter Topology

namespace AVRegularity

namespace FreshAxes

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}

theorem ocPulse_ne_zero_near (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k : ℤ} {t : ℝ}
    (h : ocPulse α q Λ ζ m k t ≠ 0) :
    |t - k * ocTau α q Λ m| < 2 / 3 * ocTau α q Λ m := by
  have hτ : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ
  unfold ocPulse at h
  have hz : ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) ≠ 0 := right_ne_zero_of_mul h
  have hmem := hζ.2.2.1 (subset_tsupport _ hz)
  rw [Set.mem_Ioo, lt_div_iff₀ hτ, div_lt_iff₀ hτ] at hmem
  rw [abs_lt]
  constructor <;> linarith [hmem.1, hmem.2]

theorem continuous_pulseSum (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) :
    Continuous (fun t => ∑' k : {k : ℤ // Odd k},
      (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) • ocPi k) := by
  have hτ : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ
  set f : {k : ℤ // Odd k} → ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun k t =>
    (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) • ocPi k
  have hcont : ∀ k, Continuous (f k) := fun k =>
    ((CycleReference.ocPulse_continuous hζ k.1).mul
      (CycleReference.ocPulseMemory_continuous hΛ hζ hν k.1)).smul continuous_const
  have hsupp : ∀ k t, f k t ≠ 0 → |t - k.1 * ocTau α q Λ m| < 2 / 3 * ocTau α q Λ m := by
    intro k t hne
    apply ocPulse_ne_zero_near hΛ hζ
    intro h0
    apply hne
    simp [f, h0]
  -- the indices whose support meets a window of half-width `τ` around `t₀` form a finite set
  have hfin : ∀ t₀ : ℝ, {k : {k : ℤ // Odd k} |
      (Function.support (f k) ∩ Set.Ioo (t₀ - ocTau α q Λ m) (t₀ + ocTau α q Λ m)).Nonempty}.Finite := by
    intro t₀
    refine (Set.Finite.preimage (Subtype.val_injective.injOn)
      (Set.finite_Icc (⌊t₀ / ocTau α q Λ m⌋ - 2) (⌈t₀ / ocTau α q Λ m⌉ + 2))).subset ?_
    rintro k ⟨t, htk, ht⟩
    have h1 := hsupp k t htk
    rw [abs_lt] at h1
    have hk1 : (k.1 : ℝ) * ocTau α q Λ m < t₀ + 5 / 3 * ocTau α q Λ m := by linarith [ht.2]
    have hk2 : t₀ - 5 / 3 * ocTau α q Λ m < (k.1 : ℝ) * ocTau α q Λ m := by linarith [ht.1]
    have hk1' : (k.1 : ℝ) < t₀ / ocTau α q Λ m + 5 / 3 := by
      have := (lt_div_iff₀ hτ).2 hk1
      rwa [add_div, mul_div_assoc, div_self hτ.ne', mul_one] at this
    have hk2' : t₀ / ocTau α q Λ m - 5 / 3 < (k.1 : ℝ) := by
      have := (div_lt_iff₀ hτ).2 hk2
      rwa [sub_div, mul_div_assoc, div_self hτ.ne', mul_one] at this
    have hc := Int.le_ceil (t₀ / ocTau α q Λ m)
    have hf := Int.floor_le (t₀ / ocTau α q Λ m)
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · have : ((⌊t₀ / ocTau α q Λ m⌋ - 2 : ℤ) : ℝ) < k.1 := by push_cast; linarith
      exact_mod_cast this.le
    · have : (k.1 : ℝ) < ((⌈t₀ / ocTau α q Λ m⌉ + 2 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this.le
  have hlf : LocallyFinite fun k => Function.support (f k) := by
    intro t₀
    refine ⟨Set.Ioo (t₀ - ocTau α q Λ m) (t₀ + ocTau α q Λ m), Ioo_mem_nhds (by linarith)
      (by linarith), ?_⟩
    simpa [Set.inter_comm] using hfin t₀
  have heq : (fun t => ∑' k, f k t) = fun t => ∑ᶠ k, f k t := by
    funext t
    exact tsum_eq_finsum (hlf.point_finite t)
  change Continuous (fun t => ∑' k, f k t)
  rw [heq]
  exact continuous_finsum hcont hlf

/-- Each entry of the reference flux is continuous in time. -/
theorem refFlux_entry_continuous (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (i j : Fin 2) : Continuous (fun t => ocRefFlux α q Λ ζ m ν t i j) := by
  have h := ((continuous_const (y := ν • (1 : Matrix (Fin 2) (Fin 2) ℝ))).add
    ((continuous_pulseSum (α := α) (q := q) (Λ := Λ) (m := m) hΛ hζ hν).const_smul
      (ocMu q Λ m ν * ocHStar α q Λ m ν)))
  exact (continuous_apply j).comp ((continuous_apply i).comp h)

end FreshAxes

end AVRegularity
