-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq

/-! Existence of the oc stream sequence.

This module imports only the definitions
and the predecessor hypotheses required to construct the recursive sequence. -/

@[expose] public section

open Homogenization AVenhance
open scoped ContDiff

namespace AVRegularity.Providers

theorem exists_isOCStreamSeq (α _s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < _s) (_hs₁ : _s < (1 - α) / 2) (q : ℝ)
    (_hq : AVRegularity.IsAdmissibleQ α _s q) (ζ : ℝ → ℝ)
    (hζ : AVRegularity.IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ Φ : ℕ → ℝ → Vec 2 → ℝ, AVRegularity.IsOCStreamSeq α q Λ ζ Φ := by
  have hΛ₁ : 1 ≤ Λ := by omega
  let P : ℕ → {φ : ℝ → Vec 2 → ℝ // AVenhance.IsAdmissibleStream φ} :=
    Nat.rec
      ⟨(fun _ _ => 0), by
        constructor
        · change ContDiff ℝ ∞ (fun _ : ℝ × Vec 2 => (0 : ℝ))
          exact contDiff_const
        · intro N j t x
          simp⟩
      (fun n prev =>
        ⟨AVRegularity.ocNextStream α q Λ ζ (n + 1) prev.1 prev.2,
          AVRegularity.Construction.Stream.ocNextStream_isAdmissible α q Λ ζ hζ hΛ₁
            (n + 1) (by omega) prev.1 prev.2⟩)
  let Φ : ℕ → ℝ → Vec 2 → ℝ := fun n => (P n).1
  refine ⟨Φ, ?_⟩
  constructor
  · rfl
  · intro m hm
    cases m with
    | zero => omega
    | succ n =>
      refine ⟨(P n).2, ?_⟩
      rfl

end AVRegularity.Providers
