/-
The Lean side of the egg example. Checked with Lean 4 and Mathlib (standard axioms only); the example ships a
hand-made Dump.lean output (ledger/lean-dump.json) with these statements, so running it needs no Lean.
-/
import Mathlib

namespace Egg
open Real

/-- First-order cooking time (Buay et al. 2006, eq. (11)): a sphere of radius `R` and thermal diffusivity `α`,
at temperature `T0`, is put into a bath at `Tb`; the time until its centre reaches `Tc`. -/
noncomputable def time (R α Tb T0 Tc : ℝ) : ℝ :=
  R ^ 2 / (π ^ 2 * α) * log (2 * (Tb - T0) / (Tb - Tc))

/-- The cited result, as a hypothesis on the true cooking time `cook`: it is given by the first-order formula. -/
def FirstOrder (cook : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ R α Tb T0 Tc : ℝ, 0 < R → 0 < α → T0 < Tc → Tc < Tb → cook R α Tb T0 Tc = time R α Tb T0 Tc

/-- Bigger eggs: the time scales with the square of the radius. -/
theorem scaling (k R α Tb T0 Tc : ℝ) : time (k * R) α Tb T0 Tc = k ^ 2 * time R α Tb T0 Tc := by
  unfold time; ring

/-- Colder eggs take strictly longer. -/
theorem colder (R α Tb T0 T0' Tc : ℝ) (hR : 0 < R) (hα : 0 < α) (h0 : T0' < T0) (h1 : T0 < Tc)
    (h2 : Tc < Tb) : time R α Tb T0 Tc < time R α Tb T0' Tc := by
  unfold time
  have hc : 0 < R ^ 2 / (π ^ 2 * α) := by positivity
  apply mul_lt_mul_of_pos_left _ hc
  apply Real.log_lt_log
  · apply div_pos <;> linarith
  · apply div_lt_div_of_pos_right _ (by linarith); linarith

/-- The fridge penalty: the extra time for a colder egg does not depend on how hard it should be (`Tc`). -/
theorem fridge (cook : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (h : FirstOrder cook) (R α Tb T0 T0' Tc : ℝ)
    (hR : 0 < R) (hα : 0 < α) (h0 : T0' < T0) (h1 : T0 < Tc) (h2 : Tc < Tb) :
    cook R α Tb T0' Tc - cook R α Tb T0 Tc = R ^ 2 / (π ^ 2 * α) * log ((Tb - T0') / (Tb - T0)) := by
  rw [h _ _ _ _ _ hR hα (by linarith) h2, h _ _ _ _ _ hR hα h1 h2]
  unfold time
  rw [← mul_sub, ← Real.log_div]
  · congr 2
    have a : Tb - T0 ≠ 0 := by linarith
    have b : Tb - Tc ≠ 0 := by linarith
    field_simp
  · apply ne_of_gt; apply div_pos <;> linarith
  · apply ne_of_gt; apply div_pos <;> linarith

end Egg
