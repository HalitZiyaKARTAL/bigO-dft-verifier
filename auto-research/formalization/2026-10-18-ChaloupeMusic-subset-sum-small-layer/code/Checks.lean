import SmallLayer

/-!
Checks read by `verify.py`: the definitions on small instances, the hypotheses of Corollary D at
the sizes of the note, and the axioms of every stated result.
-/

open Finset SmallLayer

/-! The definitions on three indices. -/

-- Weights 1, 2, 4: the 8 subset sums are distinct, so `|Σ(V)| = 8` and `d(V) = 0`.
#eval (sums (fun i : Fin 3 => (2 : ℤ) ^ (i : ℕ)) univ).card
-- Equal weights 1, 1, 1: `Σ(V) = {0, 1, 2, 3}`, so `d(V) = 3 - log₂ 4 = 1`.
#eval (sums (fun _ : Fin 3 => (1 : ℤ)) univ).card
-- `Σ_2(V)` is `{3, 5, 6}` for weights 1, 2, 4 and `{2}` for equal weights.
#eval (layer (fun i : Fin 3 => (2 : ℤ) ^ (i : ℕ)) univ 2).card
#eval (layer (fun _ : Fin 3 => (1 : ℤ)) univ 2).card

example : deficiency (fun _ : Fin 3 => (1 : ℤ)) univ = 1 := by
  have h : (sums (fun _ : Fin 3 => (1 : ℤ)) univ).card = 4 := by decide
  rw [deficiency, h, card_univ, Fintype.card_fin]
  rw [show ((4 : ℕ) : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one]
  · norm_num
  · norm_num

/-! The hypotheses of Corollary D hold together, so the corollary is not vacuous. The note
takes `m = 2⌊μn/2⌋`, `σ = m/2`, `k = ⌊am⌋`, `v = m - 2k` with `μ = 0.473`, `a = 0.0082`; at
`m = 1000` this gives `k = 8`, `σ = 500`, `v = 984`. -/

-- Lean's elaborator declines to unfold a power above `2 ^ 256` by default; the kernel checks the
-- arithmetic either way.
set_option exponentiation.threshold 1024 in
example : 2 * 8 ≤ 500 ∧ 2 * 500 ≤ 984 + 2 * 8 ∧ Nat.choose 500 8 * Nat.choose 984 8 ≤ 2 ^ 984 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  calc Nat.choose 500 8 * Nat.choose 984 8
      ≤ 500 ^ 8 * 984 ^ 8 := Nat.mul_le_mul (Nat.choose_le_pow _ _) (Nat.choose_le_pow _ _)
    _ ≤ 2 ^ 984 := by norm_num

/-! Axioms. -/

#print axioms SmallLayer.covering
#print axioms SmallLayer.sampling
#print axioms SmallLayer.good_layer
#print axioms SmallLayer.good_layer_density
#print axioms SmallLayer.fixed_set
#print axioms SmallLayer.corollaryD
