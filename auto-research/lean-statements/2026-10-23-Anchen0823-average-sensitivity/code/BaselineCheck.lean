import Submission
import Mathlib.Tactic

/- Statement-review checks, Apache-2.0; Anchen0823 with OpenAI Codex assistance.
The full proof is public and pinned separately; no proof is assumed as an axiom. -/
namespace StatementResearch

open OAI.LeanBlast.GotsmanLinial

theorem baseline_eight : BigOSpeedrun.AverageSensitivity.Bound (8 : ℚ) := by
  intro n d hn hd hdn p hp
  have h := Race.bound n d hn hd hdn p hp
  have hc : ((1881 / 500 : ℚ) : ℝ) ≤ ((8 : ℚ) : ℝ) := by norm_num
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg d)) (Real.sqrt_nonneg _))

/-- info: 'StatementResearch.baseline_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms baseline_eight

end StatementResearch
